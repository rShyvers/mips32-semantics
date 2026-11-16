import Std.Data.HashMap.Basic
import Semantics.Asm.Table
import Semantics.Asm.Float

/-!
# Asm.Layout — segments, data directives, the two passes

Pass 1 (`layoutLine`) assigns every statement its address and binds labels; pass 2 (`applyItem`)
encodes instructions (`encode` of the table's `Instruction`) and lays out data bytes.

**Byte order.** A `Program` maps a word-aligned address to the word value the processor's
`readMemWord` reads there, which depends on the byte order of `profile` (`Types.lean`). Data
directives therefore lay out *bytes* (byte `k` of an `n`-byte datum at address `a + k` is
`byteShift profile.bigEndianMem n k`, the same helper the memory accesses use) and `putByte` packs
each byte into its word with `byteInValue`: little-endian for the Release 6 profile (`.word
0x01020304` stores byte `04` first; a `.double` stores its least-significant byte first), and a
big-endian profile would flip every datum automatically.
-/

namespace Asm

-- ====================================================================
-- Program-building helpers (byte order of `profile`)
-- ====================================================================

/-- Round `a` up to the next multiple of `n` (`n > 0`). -/
def alignUpNat (a n : Nat) : Nat := ((a + n - 1) / n) * n

/-- Write a single byte into `prog` at `addr`, merging it into the word that contains it (other
bytes of that word are left untouched, defaulting to 0), at the byte position `profile`'s byte
order gives address `addr` inside that word. -/
def putByte (prog : Program) (addr : W32) (b : Nat) : Program :=
  let wordAddr := natToW32 ((addr.toNat / 4) * 4)
  let k := addr.toNat % 4
  let be := profile.bigEndianMem
  let existing := prog.getD wordAddr 0
  let cleared := existing &&& ~~~(byteInValue be 4 0xff k)
  prog.insert wordAddr (cleared ||| byteInValue be 4 (b % 256).toUInt8 k)

/-- Write `bytes` at consecutive addresses starting at `addr`. -/
def putBytes (prog : Program) (addr : W32) (bytes : List Nat) : Program :=
  (bytes.foldl (fun (p, a) b => (putByte p a b, a + 1#32)) (prog, addr)).1

/-- The `n` bytes of the `n`-byte datum `v` in memory order (byte `k` goes to address `a + k`),
in the byte order of `profile`; `v` taken modulo `256^n`. -/
def datumBytes (n : Nat) (v : Nat) : List Nat :=
  (List.range n).map fun k => (v >>> byteShift profile.bigEndianMem n k) % 256

-- ====================================================================
-- Data directives (a table: width, alignment and operand value)
-- ====================================================================

/-- A fixed-width data directive: each operand is one `width`-byte datum, aligned to `width`. -/
structure DataDir where
  width : Nat
  value : Std.HashMap String W32 → String → Nat → Except AsmError Nat

/-- A signed-or-unsigned integer datum in `lo..hi`, as its `width`-byte pattern. -/
def intDatum (what : String) (lo hi : Int) (labelsOk : Bool) :
    Std.HashMap String W32 → String → Nat → Except AsmError Nat := fun labels tok line => do
  let v ← if labelsOk then evalExpr labels tok line else parseImmediate tok line
  checkRange what lo hi v line
  pure (ofInt32 v).toNat

/-- The fixed-width data directives. -/
def dataTable : List (String × DataDir) :=
  [ (".word", ⟨4, intDatum ".word value" (-2147483648) 4294967295 true⟩),
    (".half", ⟨2, intDatum ".half value" (-32768) 65535 false⟩),
    (".byte", ⟨1, intDatum ".byte value" (-128) 255 false⟩),
    (".float", ⟨4, fun _ tok line => parseFloatLit 24 8 tok line⟩),
    (".double", ⟨8, fun _ tok line => parseFloatLit 53 11 tok line⟩) ]

/-- The string directives (`.asciiz`, `.asciz`, `.string` append a NUL; `.ascii` does not). -/
def stringDirectives : List String := [".ascii", ".asciiz", ".asciz", ".string"]

/-- A data-emitting directive (laid out by `directiveLayout`). Segment directives, `.align`,
`.set` and the no-op `.globl`/`.global`/`.extern` are handled directly in `layoutLine`. -/
def isDataDirective (m : String) : Bool :=
  dataTable.any (·.1 == m) || stringDirectives.contains m || m == ".space"

/-- Alignment and byte count of a data directive (the alignment is applied to the location
counter before the item -- and before binding its labels -- unless `.align 0` switched automatic
alignment off). -/
def directiveLayout (mnemonic : String) (operands : List String) (lineNo : Nat) :
    Except AsmError (Nat × Nat) := do
  if operands.isEmpty then
    throw (.badOperand s!"{mnemonic} needs at least one operand" lineNo)
  match dataTable.find? (·.1 == mnemonic) with
  | some (_, d) => pure (d.width, d.width * operands.length)
  | none =>
  if mnemonic == ".space" then
    match operands with
    | [tok] => do
        let n ← parseImmediate tok lineNo
        if n < 0 then throw (.badImmediate s!".space requires a non-negative count" lineNo)
        pure (1, n.toNat)
    | _ => throw (.badOperand s!".space expects exactly one operand" lineNo)
  else if stringDirectives.contains mnemonic then do
    let nul := if mnemonic == ".ascii" then 0 else 1
    let mut total := 0
    for tok in operands do
      let bytes ← parseStringTok tok lineNo
      total := total + bytes.length + nul
    pure (1, total)
  else throw (.badDirective s!"unknown directive '{mnemonic}'" lineNo)

-- ====================================================================
-- Pass 1: layout (addresses + labels)
-- ====================================================================

/-- The four assembly segments. Each has its own location counter; a
segment directive without an operand resumes where that segment left off. -/
inductive Seg
  | text | data | ktext | kdata

def Seg.isText : Seg → Bool
  | .text => true
  | .ktext => true
  | _ => false

/-- A line with real content (label-only lines are folded into the label
table and otherwise dropped). `size` is the number of bytes the item
occupies (used for overlap detection). -/
structure RawItem where
  lineNo : Nat
  addr : W32
  size : Nat
  mnemonic : String
  operands : List String

/-- Layout state. Location counters are `Nat`s so that running past
`2^32` is detected instead of wrapping. `pending` holds labels seen but
not yet bound: a label binds to the address of the *next item after
alignment* (B2), not to the raw location counter at the label. -/
structure LState where
  seg : Seg
  textAddr : Nat
  dataAddr : Nat
  ktextAddr : Nat
  kdataAddr : Nat
  autoAlign : Bool
  /-- `.set noat` is in effect: idioms that need `$at` are rejected. -/
  noat : Bool := false
  pending : List String
  labels : Std.HashMap String W32
  items : Array RawItem

def LState.curAddr (s : LState) : Nat :=
  match s.seg with
  | .text => s.textAddr
  | .data => s.dataAddr
  | .ktext => s.ktextAddr
  | .kdata => s.kdataAddr

def LState.setAddr (s : LState) (a : Nat) : LState :=
  match s.seg with
  | .text => { s with textAddr := a }
  | .data => { s with dataAddr := a }
  | .ktext => { s with ktextAddr := a }
  | .kdata => { s with kdataAddr := a }

/-- Bind every pending label to `addr`. -/
def LState.bindPending (s : LState) (addr : Nat) (line : Nat) : Except AsmError LState :=
  if s.pending.isEmpty then pure s
  else if addr ≥ 4294967296 then
    throw (.badDirective "label address is beyond the 32-bit address space" line)
  else
    pure { s with
      labels := s.pending.foldl (fun m l => m.insert l (natToW32 addr)) s.labels
      pending := [] }


/-- Place an item of `bytes` bytes at the current location rounded up to
`align`, binding the pending labels to that aligned address. -/
def LState.place (s : LState) (pl : ParsedLine) (m : String) (align bytes : Nat) :
    Except AsmError LState := do
  let aligned := alignUpNat s.curAddr align
  if aligned + bytes > 4294967296 then
    throw (.badDirective s!"'{m}' runs past the end of the 32-bit address space" pl.lineNo)
  let s ← s.bindPending aligned pl.lineNo
  let item : RawItem :=
    { lineNo := pl.lineNo, addr := natToW32 aligned, size := bytes, mnemonic := m, operands := pl.operands }
  pure { (s.setAddr (aligned + bytes)) with items := s.items.push item }

def layoutLine (s : LState) (pl : ParsedLine) : Except AsmError LState := do
  let mut st := s
  for lbl in pl.labels do
    if st.labels.contains lbl || st.pending.contains lbl then
      throw (.duplicateLabel s!"label '{lbl}' already defined" pl.lineNo)
    st := { st with pending := lbl :: st.pending }
  let s := st
  match pl.mnemonic with
  | none => pure s
  | some m =>
    let segOf : Option Seg :=
      match m with
      | ".text" => some .text
      | ".data" => some .data
      | ".ktext" => some .ktext
      | ".kdata" => some .kdata
      | _ => none
    match segOf with
    | some seg =>
      -- A label still pending at a segment switch names the end of the
      -- segment being left.
      let s ← s.bindPending s.curAddr pl.lineNo
      let s := { s with seg := seg, autoAlign := true }
      match pl.operands with
      | [] => pure s
      | [tok] => do
          let a ← parseImmediate tok pl.lineNo
          checkRange s!"{m} address" 0 4294967295 a pl.lineNo
          pure (s.setAddr a.toNat)
      | _ => throw (.badOperand s!"{m} takes at most one address operand" pl.lineNo)
    | none =>
    if m == ".set" then
      -- `.set noreorder` is what this assembler always does; `.set noat` /
      -- `.set at` only switch the `$at` idioms off / on. `.set reorder` would
      -- change the meaning of the program (the assembler would have to fill
      -- delay slots) and is rejected, as is any other option.
      match pl.operands with
      | ["noreorder"] => pure s
      | ["noat"] => pure { s with noat := true }
      | ["at"] => pure { s with noat := false }
      | ["reorder"] =>
        throw (.badDirective
          ".set reorder is not supported: this assembler never fills delay slots (it always behaves as .set noreorder)"
          pl.lineNo)
      | _ => throw (.badDirective s!".set: unsupported option(s) {pl.operands}" pl.lineNo)
    else if m == ".globl" || m == ".global" || m == ".extern" then
      -- Accepted for source compatibility; this single-file assembler has
      -- no symbol visibility, so they are no-ops (labels stay pending).
      if pl.operands.isEmpty then throw (.badOperand s!"{m} expects a symbol name" pl.lineNo)
      else pure s
    else if m == ".align" then
      match pl.operands with
      | [tok] => do
          let n ← parseImmediate tok pl.lineNo
          checkRange ".align exponent" 0 16 n pl.lineNo
          if n == 0 then
            -- MARS/GNU as: `.align 0` turns off the automatic alignment of
            -- `.half`/`.word`/`.float`/`.double` until the next segment
            -- directive. Instructions are always word-aligned regardless.
            pure { s with autoAlign := false }
          else
            let aligned := alignUpNat s.curAddr (2 ^ n.toNat)
            if aligned > 4294967296 then
              throw (.badDirective ".align runs past the end of the 32-bit address space" pl.lineNo)
            let s ← s.bindPending aligned pl.lineNo
            pure (s.setAddr aligned)
      | _ => throw (.badOperand ".align expects exactly one operand" pl.lineNo)
    else if isDataDirective m then do
      let (align, bytes) ← directiveLayout m pl.operands pl.lineNo
      s.place pl m (if s.autoAlign then align else 1) bytes
    else if isKnownMnemonic m then do
      if !s.seg.isText then
        throw (.badDirective s!"instruction '{m}' in a data segment (.data/.kdata)" pl.lineNo)
      if s.noat && atIdioms.contains m then
        throw (.badOperand s!"'{m}' expands through $at, which .set noat forbids" pl.lineNo)
      let simple ← expandIdiom m pl.operands pl.lineNo
      let mut n := 0
      for (sm, sops) in simple do
        n := n + (← stmtWords sm sops pl.lineNo)
      -- Instructions are always word-aligned (data directives are allowed
      -- in `.text`, so the location counter may be unaligned here).
      s.place pl m 4 (4 * n)
    else if m.startsWith "." then
      throw (.badDirective s!"unknown directive '{m}'" pl.lineNo)
    else
      throw (unknownMnemonicError m pl.lineNo)


-- ====================================================================
-- Pass 2: encode (labels now fully resolved)
-- ====================================================================

/-- The bytes of a data directive's operands. -/
def dataItemBytes (labels : Std.HashMap String W32) (item : RawItem) :
    Except AsmError (Option (List Nat)) := do
  match dataTable.find? (·.1 == item.mnemonic) with
  | some (_, d) => do
      let mut bytes : List Nat := []
      for tok in item.operands do
        bytes := bytes ++ datumBytes d.width (← d.value labels tok item.lineNo)
      pure (some bytes)
  | none =>
  if stringDirectives.contains item.mnemonic then do
    let mut bytes : List Nat := []
    for tok in item.operands do
      let b ← parseStringTok tok item.lineNo
      bytes := bytes ++ b ++ (if item.mnemonic == ".ascii" then [] else [0])
    pure (some bytes)
  else if item.mnemonic == ".space" then
    pure (some [])   -- reserved bytes default to 0 (sparse map, unread = 0)
  else pure none

/-- Emit one laid-out item into the program. -/
def applyItem (labels : Std.HashMap String W32) (prog : Program) (item : RawItem) :
    Except AsmError Program := do
  match ← dataItemBytes labels item with
  | some bytes => pure (putBytes prog item.addr bytes)
  | none =>
    let simple ← expandIdiom item.mnemonic item.operands item.lineNo
    let mut p := prog
    let mut a := item.addr
    for (sm, sops) in simple do
      let instrs ← encodeStmt { labels, addr := a, name := sm, line := item.lineNo } sops
      for i in instrs do
        p := p.insert a (encode i)
        a := a + 4#32
    if a.toNat ≠ (item.addr.toNat + item.size) % 4294967296 then
      throw (.badOperand s!"internal error: '{item.mnemonic}' emitted a different size in pass 2 than pass 1 reserved" item.lineNo)
    pure p

/-- Reject two items occupying the same bytes (possible once segment
directives take explicit addresses) -- the later one would otherwise
silently overwrite the earlier. -/
def checkOverlap (items : Array RawItem) : Except AsmError Unit := do
  let spans := (items.filter (fun it => it.size > 0)).qsort (fun a b => a.addr.toNat < b.addr.toNat)
  let mut prev : Option RawItem := none
  for it in spans do
    match prev with
    | some p =>
      if p.addr.toNat + p.size > it.addr.toNat then
        let (first, second) := if p.lineNo ≤ it.lineNo then (p, it) else (it, p)
        throw (.badDirective
          s!"'{second.mnemonic}' overlaps the bytes emitted by '{first.mnemonic}' on line {first.lineNo}" second.lineNo)
    | none => pure ()
    prev := some it
  pure ()


end Asm
