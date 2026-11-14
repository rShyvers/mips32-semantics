import Std.Data.HashMap.Basic
import Semantics.Word
import Semantics.Types
import Semantics.State
import Semantics.Instruction
import Semantics.Asm
import Semantics.Step
import Semantics.Env
import Semantics.Refine.Abs

/-!
# EquivHarness — arithmetic equivalence corpus (thin interpreter, no MARS)

This replaces the originally-planned "unseal a real MIPS program (CS47) and
find its bug" step: that program needs assembler macros, which
`docs/spec/SPEC-NOTES.md` §9 puts explicitly out of scope, so it can't be
assembled by `Asm.lean` at all. Instead, this harness validates the
semantics against a small corpus we wrote ourselves: for several arithmetic
operations, a "base" program using the direct instruction (`mult`, `div`,
`sub`, …) and a "variant" program computing the same function with
bit-shifting/bitwise instructions instead — the kind of strength-reduction a
compiler or a hand-optimizing assembly programmer would do. Two of the
pairs are *deliberately wrong* (the classic "replace division/mod by a
power of two with a raw shift/mask" bug, which breaks on negative
dividends), so this harness actually has to detect a real divergence, not
just confirm agreement everywhere — the same spirit as the sealed-program
bug hunt, on a corpus we control end to end.

**Why no MARS here, unlike `DiffHarness`:** `DiffHarness` differentially
validates the whole semantics against real MARS 4.5 by spawning a `java`
process per program — the right tool for "is this semantics the same
language as the real simulator?". That's unnecessary (and, per program,
hundreds of times slower) for "do these two *already-validated* programs
compute the same function?": the question is internal to the semantics,
so running both programs directly through our own `step`/`run` — a "thin
interpreter", pure Lean, no subprocess, no JVM, no per-case compilation —
is both sufficient and far faster. `assemble` + `run` IS the full execution
pipeline this project cares about; MARS is only needed as an external
oracle, and there is no external oracle question being asked here.

## Corpus layout (`tests/equiv/`)

Every program takes its input(s) in `$a0` (register 4) and, for the one
two-input pair, also `$a1` (register 5); every program leaves its result in
`$t9` (register 25) and halts cleanly via `syscall 10`.
-/

/-- One equivalence claim: run `basePath` and `variantPath` on the same
inputs and compare `$t9`. `expectEquivalent := true` means every tested
input must agree (a real, provable equivalence); `false` means at least one
input is expected to disagree (a deliberately-wrong variant, kept in the
corpus specifically to prove this harness isn't vacuously green). -/
structure EquivCase where
  name : String
  basePath : String
  variantPath : String
  expectEquivalent : Bool
  note : String

def corpus : List EquivCase :=
  [ { name := "mul_pow2"
    , basePath := "tests/equiv/mul_pow2_base.asm"
    , variantPath := "tests/equiv/mul_pow2_shift.asm"
    , expectEquivalent := true
    , note := "x*8 via mult/mflo vs sll by 3" }
  , { name := "mul_const5"
    , basePath := "tests/equiv/mul_const5_base.asm"
    , variantPath := "tests/equiv/mul_const5_shiftadd.asm"
    , expectEquivalent := true
    , note := "x*5 via mult/mflo vs (x<<2)+x (addu, non-trapping)" }
  , { name := "div_pow2_buggy"
    , basePath := "tests/equiv/div_pow2_base.asm"
    , variantPath := "tests/equiv/div_pow2_shift_buggy.asm"
    , expectEquivalent := false
    , note := "x/4 via div/mflo vs plain sra (WRONG: rounds toward -inf, not zero)" }
  , { name := "div_pow2_correct"
    , basePath := "tests/equiv/div_pow2_base.asm"
    , variantPath := "tests/equiv/div_pow2_shift_correct.asm"
    , expectEquivalent := true
    , note := "x/4 via div/mflo vs bias-corrected sra" }
  , { name := "mod_pow2_buggy"
    , basePath := "tests/equiv/mod_pow2_base.asm"
    , variantPath := "tests/equiv/mod_pow2_mask_buggy.asm"
    , expectEquivalent := false
    , note := "x%4 via div/mfhi vs plain andi mask (WRONG: always non-negative)" }
  , { name := "mod_pow2_correct"
    , basePath := "tests/equiv/mod_pow2_base.asm"
    , variantPath := "tests/equiv/mod_pow2_mask_correct.asm"
    , expectEquivalent := true
    , note := "x%4 via div/mfhi vs a0 - (bias-corrected quotient)*4" }
  , { name := "sub_twos_complement"
    , basePath := "tests/equiv/sub_base.asm"
    , variantPath := "tests/equiv/sub_twos_complement.asm"
    , expectEquivalent := true
    , note := "a0-a1 via subu vs nor+addiu+addu (two's-complement negate-and-add)" }
  ]

/-- Signed 32-bit test vectors: zero, unit steps around every pair's
divisor/shift-amount (both exact multiples and non-multiples, both signs),
the INT_MIN/INT_MAX boundary (and INT_MIN+3, the div/mod bias-add's own
edge case), and a handful of larger ordinary and overflow-triggering
values. The second component is only exercised by `sub_twos_complement`
(every other program ignores `$a1`); for everything else it's filler. -/
def testVectors : List (Int × Int) :=
  [ (0,0), (1,0), (-1,0), (2,0), (-2,0), (3,0), (-3,0), (4,0), (-4,0), (5,0), (-5,0)
  , (7,0), (-7,0), (8,0), (-8,0)
  , (2147483647,0), (-2147483648,0), (-2147483645,0)
  , (100,0), (-100,0), (101,0), (-101,0)
  , (123456789,0), (-123456789,0)
  , (429496729,0), (858993459,0), (-858993459,0), (-429496730,0)
  , (268435456,0), (-268435456,0), (536870912,0)
  -- sub-specific pairs (meaningful two-input cases; harmless as single-input
  -- filler elsewhere, since single-input programs never read $a1)
  , (5,3), (3,5), (-5,3), (5,-3), (-5,-3), (0,1), (1,0)
  , (2147483647,-1), (-2147483648,1), (-2147483648,-1)
  , (-2147483648,-2147483648), (2147483647,2147483647)
  , (100,37), (-100,-37), (37,-100)
  ]

/-- Outcome of running one assembled program on one input. -/
inductive RunOutcome where
  | result (v : Int)                 -- clean exit; `$t9`'s signed value
  | otherHalt (reason : String)      -- halted some other way (not `.exit`)
  | limitReached

/-- Load `prog` (`Env.load`), set `$a0`/`$a1`, and run it hosted. -/
def runOne (prog : Program) (a0 a1 : Int) (fuel : Nat) : RunOutcome :=
  let s0 := load prog
  let s0 := writeReg s0 4 (ofInt32 a0)
  let s0 := writeReg s0 5 (ofInt32 a1)
  match runHosted { image := prog } fuel { machine := s0 } with
  | .halted .exit h _ => .result (asSigned (readReg h.machine 25))
  | .halted (.unhandledException code epc bad) _ _ =>
    .otherHalt s!"unhandledException code={code.toNat} epc={epc} badVAddr={bad}"
  | .halted (.noInstruction pc) _ _ => .otherHalt s!"noInstruction {pc}"
  | .limitReached _ _ => .limitReached

instance : ToString RunOutcome where
  toString
    | .result v => toString v
    | .otherHalt r => s!"<halt: {r}>"
    | .limitReached => "<limitReached>"

def outcomesMatch : RunOutcome → RunOutcome → Bool
  | .result a, .result b => a == b
  | _, _ => false

/-- Load and assemble one `.asm` file, failing loudly (this harness's whole
corpus is meant to always assemble; an `AsmError` here is itself a bug in
the corpus, not a possible verdict). -/
def loadProgram (path : String) : IO Program := do
  let src ← IO.FS.readFile path
  match assemble src with
  | .ok prog => pure prog
  | .error e => throw (IO.userError s!"{path}: assemble failed: {repr e}")

structure CaseResult where
  name : String
  mismatches : List (Int × Int × RunOutcome × RunOutcome)
  actuallyEquivalent : Bool   -- true iff zero mismatches across all test vectors

def runCase (c : EquivCase) (fuel : Nat) : IO CaseResult := do
  let base ← loadProgram c.basePath
  let variant ← loadProgram c.variantPath
  let mismatches := testVectors.filterMap fun (a0, a1) =>
    let rb := runOne base a0 a1 fuel
    let rv := runOne variant a0 a1 fuel
    if outcomesMatch rb rv then none else some (a0, a1, rb, rv)
  pure { name := c.name, mismatches := mismatches, actuallyEquivalent := mismatches.isEmpty }

/-! ## Expected-output programs (`tests/asm/*.asm`)

Programs that MARS cannot run (FCSR, exceptions with a `.ktext` handler,
Release 2 instructions, …) carry their expectation in a comment:

```
# Expected output: "<exact text the program prints>"
# Expected halt: exit | unhandledException <ExcCode> | noInstruction      (optional; default exit)
```

Everything between the first and the last `"` on the `Expected output` line
is the expected text. Each such program is assembled, loaded (`Env.load`) and run hosted
(`Env.runProgram`); the accumulated output and the stop reason must match. A program without an `Expected output` line is not
checked (and is reported as such). -/

/-- The text after `prefix` on the first source line that starts with it. -/
def expectationLine (src pfx : String) : Option String :=
  (src.splitOn "\n").findSome? fun l =>
    if l.startsWith pfx then some ((l.drop pfx.length).toString) else none

/-- The text between the first and the last double quote of `s`. -/
def quoted (s : String) : Option String :=
  match s.splitOn "\"" with
  | _ :: rest@(_ :: _) => some (String.intercalate "\"" rest.dropLast)
  | _ => none

/-- Run one expected-output program; `none` if it has no expectation,
otherwise `some (ok, description)`. -/
def checkAsmProgram (path : String) : IO (Option (Bool × String)) := do
  let src ← IO.FS.readFile path
  match (expectationLine src "# Expected output:").bind quoted with
  | none => pure none
  | some expected =>
    let expectedHalt :=
      ((expectationLine src "# Expected halt:").map (·.trimAscii.toString)).getD "exit"
    match assemble src with
    | .error e => pure (some (false, s!"assemble failed: {repr e}"))
    | .ok prog =>
      let (halt, out) :=
        match runProgram prog 1000000 with
        | .halted .exit h _ => ("exit", h.out)
        | .halted (.unhandledException code _ _) h _ => (s!"unhandledException {code.toNat}", h.out)
        | .halted (.noInstruction _) h _ => ("noInstruction", h.out)
        | .limitReached h _ => ("limitReached", h.out)
      if out == expected && halt == expectedHalt then pure (some (true, s!"output {repr out}, halt {halt}"))
      else pure (some (false,
        s!"expected output {repr expected} halt {expectedHalt}; got output {repr out} halt {halt}"))

/-! ## The manual spec against `step` (`docs/MANUAL-SPEC.md`, "Validate before proving")

On every state of the hosted run of every program in `tests/corpus` and `tests/oracle`, the
independent spec's instruction time `Manual.InstructionTime modelImpl modelOracle decode (abs s)` is
compared with `abs (step s)`, field by field (memory: the bytes the model wrote in this step and the
aligned word around the effective address of a load or store). A state whose instruction's page is
not transcribed yet (`Manual.Operation` is `none`) is skipped and counted. Every mismatch is a FAIL. -/

open Manual Refine in
/-- The fields where two architectural states differ, on the given physical addresses. -/
def archDiff (x y : Arch) (addrs : List PAddr) : List String := Id.run do
  let mut d : List String := []
  if x.PC != y.PC then d := d ++ [s!"PC {x.PC} vs {y.PC}"]
  for k in List.finRange 32 do
    if x.GPR k != y.GPR k then d := d ++ [s!"GPR[{k}] {x.GPR k} vs {y.GPR k}"]
    if x.FPR k != y.FPR k then d := d ++ [s!"FPR[{k}] {x.FPR k} vs {y.FPR k}"]
  if x.HI != y.HI then d := d ++ ["HI"]
  if x.LO != y.LO then d := d ++ ["LO"]
  if x.FCSR != y.FCSR then d := d ++ [s!"FCSR {x.FCSR} vs {y.FCSR}"]
  for p in addrs do
    if x.Mem p != y.Mem p then d := d ++ [s!"Mem[{p}] {x.Mem p} vs {y.Mem p}"]
  if x.LLbit != y.LLbit then d := d ++ ["LLbit"]
  if x.LLAddr != y.LLAddr then d := d ++ ["LLAddr"]
  if x.Status != y.Status then d := d ++ [s!"Status {x.Status} vs {y.Status}"]
  if x.Cause != y.Cause then d := d ++ [s!"Cause {x.Cause} vs {y.Cause}"]
  if x.EPC != y.EPC then d := d ++ [s!"EPC {x.EPC} vs {y.EPC}"]
  if x.BadVAddr != y.BadVAddr then d := d ++ ["BadVAddr"]
  if x.ErrorEPC != y.ErrorEPC then d := d ++ ["ErrorEPC"]
  if x.EBase != y.EBase then d := d ++ ["EBase"]
  if x.ConfigK0 != y.ConfigK0 || x.ConfigK23 != y.ConfigK23 || x.ConfigKU != y.ConfigKU then
    d := d ++ ["Config"]
  if x.Count != y.Count then d := d ++ [s!"Count {x.Count} vs {y.Count}"]
  if x.Compare != y.Compare then d := d ++ ["Compare"]
  if x.CauseTI != y.CauseTI then d := d ++ ["CauseTI"]
  if x.HWREna != y.HWREna then d := d ++ ["HWREna"]
  if x.HW != y.HW then d := d ++ ["HW"]
  if x.LowPower != y.LowPower then d := d ++ ["LowPower"]
  if x.BranchDelay != y.BranchDelay then d := d ++ [s!"BranchDelay {x.BranchDelay} vs {y.BranchDelay}"]
  if x.Nullify != y.Nullify then d := d ++ ["Nullify"]
  return d

/-- The physical bytes to compare after the step from `s` to `s'`: the keys the model added, and the
aligned word around the effective address of a pilot load or store at `pc`. -/
def memCheckAddrs (s s' : State) : List PAddr :=
  let added := s'.physMem.keys.filter (fun k => !s.physMem.contains k)
  let ea : List PAddr :=
    match readMemWord s s.pc |>.bind decode with
    | some (.lw b _ o) | some (.sw b _ o) | some (.lwl b _ o) =>
      let va := readReg s (regIdx b) + signExt16 o
      let pa := fixedMappingPA (erlSet s) va &&& ~~~3#32
      [pa, pa + 1#32, pa + 2#32, pa + 3#32]
    -- 7B S4 FPU: the bytes an FP store may write (aligned word, or the doubleword)
    | some (.swc1 b _ o) | some (.sdc1 b _ o) =>
      let va := readReg s (regIdx b) + signExt16 o
      let pa := fixedMappingPA (erlSet s) va &&& ~~~7#32
      (List.range 8).map fun k => pa + BitVec.ofNat 32 k
    | some (.swxc1 _ i b) | some (.sdxc1 _ i b) =>
      let va := readReg s (regIdx b) + readReg s (regIdx i)
      let pa := fixedMappingPA (erlSet s) va &&& ~~~7#32
      (List.range 8).map fun k => pa + BitVec.ofNat 32 k
    | _ => []
  added ++ ea

/-- The mnemonic (constructor name) of the instruction at `pc`, for the skip counts. -/
def ctorAt (s : State) : String :=
  match readMemWord s s.pc |>.bind decode with
  | some i => ((toString (repr i)).splitOn " ").head!.replace "Instruction." ""
  | none => "<undecodable>"

structure ManualStats where
  compared : Nat := 0
  skipped : Nat := 0
  mismatches : Nat := 0
  skippedBy : Std.HashMap String Nat := {}

/-- Run one program hosted and compare the spec with `step` on every state. -/
def manualCheckProgram (path : String) (stats : ManualStats) (fuel : Nat) :
    IO (ManualStats × List String) := do
  let src ← IO.FS.readFile path
  match assemble src with
  | .error _ => pure (stats, [])   -- not assemblable (the other harnesses report that)
  | .ok prog =>
    let services := !(src.splitOn "# oracle: bare").length > 1
    let env : HostEnv := { image := prog, services := services }
    let mut h : Hosted := { machine := load prog }
    let mut st := stats
    let mut msgs : List String := []
    for _ in [0:fuel] do
      let s := h.machine
      match Manual.InstructionTime Manual.modelImpl Manual.modelOracle decode (Refine.abs s) with
      | none =>
        let c := ctorAt s
        st := { st with skipped := st.skipped + 1,
                        skippedBy := st.skippedBy.insert c ((st.skippedBy.getD c 0) + 1) }
      | some a' =>
        let s' := step s
        let d := archDiff a' (Refine.abs s') (memCheckAddrs s s')
        st := { st with compared := st.compared + 1 }
        if !d.isEmpty then
          st := { st with mismatches := st.mismatches + 1 }
          if msgs.length < 5 then
            msgs := msgs ++ [s!"{path}: pc={s.pc} {ctorAt s}: {String.intercalate "; " (d.take 6)}"]
      match hostStep env h with
      | .next h' => h := h'
      | .halt _ => break
    pure (st, msgs)

/-- The manual-spec check over `tests/corpus` and `tests/oracle`; `true` iff no mismatch. -/
def manualCheck : IO Bool := do
  let mut st : ManualStats := {}
  let mut allMsgs : List String := []
  let mut programs := 0
  for dir in ["tests/corpus", "tests/oracle"] do
    let entries ← System.FilePath.readDir dir
    let paths := (entries.map (·.path.toString)).filter (·.endsWith ".asm") |>.qsort (· < ·)
    for path in paths do
      programs := programs + 1
      let (st', msgs) ← manualCheckProgram path st 20000
      st := st'
      allMsgs := allMsgs ++ msgs
  for m in allMsgs do IO.println s!"FAIL  manual: {m}"
  let skips := st.skippedBy.toList.mergeSort (fun a b => a.2 ≥ b.2)
  IO.println s!"manual spec vs step: {programs} programs, {st.compared} states compared, {st.mismatches} mismatches, {st.skipped} skipped (instruction not transcribed yet)"
  IO.println s!"  skipped by instruction: {String.intercalate ", " (skips.map fun (c, n) => s!"{c} {n}")}"
  pure (st.mismatches == 0)

def main : IO UInt32 := do
  let fuel := 1000
  let mut allOk := true
  for c in corpus do
    let r ← runCase c fuel
    let verdictOk := r.actuallyEquivalent == c.expectEquivalent
    allOk := allOk && verdictOk
    let kind := if c.expectEquivalent then "claimed equivalent" else "claimed DIFFERENT (deliberate bug)"
    IO.println s!"== {c.name} ({kind}) =="
    IO.println s!"   {c.note}"
    IO.println s!"   base={c.basePath}"
    IO.println s!"   variant={c.variantPath}"
    if r.mismatches.isEmpty then
      IO.println s!"   no mismatches across {testVectors.length} inputs"
    else
      IO.println s!"   {r.mismatches.length} mismatch(es) across {testVectors.length} inputs:"
      for (a0, a1, rb, rv) in r.mismatches.take 8 do
        IO.println s!"     a0={a0} a1={a1}: base={rb} variant={rv}"
      if r.mismatches.length > 8 then
        IO.println s!"     ... and {r.mismatches.length - 8} more"
    let status := if verdictOk then "PASS" else "FAIL (unexpected!)"
    IO.println s!"   verdict: {status}"
  IO.println ""
  -- expected-output programs
  let entries ← System.FilePath.readDir "tests/asm"
  let paths := (entries.map (·.path.toString)).filter (·.endsWith ".asm") |>.qsort (· < ·)
  let mut checked := 0
  for path in paths do
    match ← checkAsmProgram path with
    | none => IO.println s!"SKIP  {path} (no '# Expected output:' line)"
    | some (ok, msg) =>
      checked := checked + 1
      allOk := allOk && ok
      IO.println s!"{if ok then "PASS" else "FAIL"}  {path}: {msg}"
  IO.println s!"expected-output programs checked: {checked} of {paths.size}"
  if checked == 0 then
    IO.println "FAIL  no expected-output program found under tests/asm"
    allOk := false
  IO.println ""
  -- the manual spec against `step`
  let manualOk ← manualCheck
  allOk := allOk && manualOk
  IO.println ""
  if allOk then
    IO.println s!"SUMMARY: all {corpus.length} equivalence cases behaved as claimed"
    pure 0
  else
    IO.println "SUMMARY: at least one case did NOT behave as claimed — see FAIL lines above"
    pure 1
