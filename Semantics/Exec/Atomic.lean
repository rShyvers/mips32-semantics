import Semantics.Exec.Base

/-!
# Exec.Atomic — LL and SC

The execution of LL and SC (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of LL and SC; `none` for every other instruction. -/
def execAtomic (s : State) : Instruction → Option State
  -- `ll`/`sc`: real MIPS32 atomic synchronization primitives (opcodes
  -- 0x30/0x38; MD00086 Rev 2.50 §3.2). `ll` loads like `lw` and additionally
  -- sets `llBit`; `sc` performs its store only if `llBit` is set (checked
  -- *before* clearing it), writing success/failure back to `$rt`, and
  -- always clears `llBit` afterward -- see `Types.lean`'s `llBit` docstring
  -- for this model's single-hart simplification.
  | .ll rs rt imm => some <|
    let addr := readReg s (regIdx rs) + signExt9 imm
    match readMemWord s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some v => mkNext s { (writeReg s (regIdx rt) v) with llBit := true, llAddr := addr }
  | .sc rs rt imm => some <|
    -- The effective-address alignment check happens unconditionally, exactly
    -- as for `sw` (real MIPS32 computes/validates the memory reference
    -- regardless of whether `LLbit` ends up permitting the store); only
    -- *committing* `writeMemWord`'s result is conditional on `s.llBit`,
    -- which is checked before it is cleared below.
    let addr := readReg s (regIdx rs) + signExt9 imm
    match writeMemWord s addr (readReg s (regIdx rt)) with
    | none => takeAddressException s excCodeAdES addr
    | some stored =>
      -- "An SC will fail if the aligned address of the SC does not match
      -- that of the preceding LL" (MD00086 Vol II-A Rev 6.06, SC, p.347):
      -- the addresses are compared in bits 31..2 (the aligned word), bits
      -- 1..0 are ignored.
      if s.llBit && s.llAddr >>> 2 == addr >>> 2 then
        mkNext s { (writeReg stored (regIdx rt) 1#32) with llBit := false }
      else
        mkNext s { (writeReg s (regIdx rt) 0#32) with llBit := false }
  | _ => none
