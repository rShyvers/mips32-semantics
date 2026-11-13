/-!
# Word — 32-bit word type and bit-level helpers

Foundation module (DESIGN.md §3). `BitVec 32` is provided by Lean core
(`Init.Data.BitVec`), which is always in scope, so no extra imports are needed.
-/

/-- A 32-bit machine word. -/
abbrev W32 := BitVec 32

/-- Sign-extend the low 16 bits of a word to 32 bits.
Used for I-format immediates (e.g. `addi`, `lw`, `beq` offsets). -/
def signExt16 (w : W32) : W32 :=
  (w.extractLsb 15 0).signExtend 32

/-- Interpret a word as a two's-complement signed integer. -/
def asSigned (w : W32) : Int :=
  w.toInt

/-- Wrap an arbitrary integer into its 32-bit two's-complement representation. -/
def ofInt32 (i : Int) : W32 :=
  BitVec.ofInt 32 i

/-- Zero-extend the low 16 bits of a word to 32 bits.
Used for I-format immediates in logical/unsigned contexts (e.g. `andi`, `ori`, `lui`). -/
def zeroExt16 (w : W32) : W32 :=
  (w.extractLsb 15 0).zeroExtend 32

/-- Take the low `n` bits of a word (as a `W32`), masking off any higher bits.
Used to mask instruction-word fields to their declared widths before shifting. -/
def maskLow (n : Nat) (w : W32) : W32 :=
  w &&& ((1#32 <<< n) - 1#32)
