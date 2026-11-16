import Semantics.Exec.Base

/-!
# Exec.Memory — the integer loads and stores, SYNC, PREF and SYNCI

The execution of the integer loads and stores, SYNC, PREF and SYNCI (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of the integer loads and stores, SYNC, PREF and SYNCI; `none` for every other instruction. -/
def execMemory (s : State) : Instruction → Option State
  -- Memory access: effective address = $rs + sign-extended offset
  -- (SPEC-NOTES §9.3 — we follow the ISA, not MARS's lw/sw zero-extension bug).
  | .lw rs rt imm => some <|
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemWord s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some v => mkNext s (writeReg s (regIdx rt) v)
  | .sw rs rt imm => some <|
    let addr := readReg s (regIdx rs) + signExt16 imm
    match writeMemWord s addr (readReg s (regIdx rt)) with
    | none => takeAddressException s excCodeAdES addr
    | some s' => mkNext s { s' with llBit := false }
  | .lb rs rt imm => some <|
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemByte s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some b => mkNext s (writeReg s (regIdx rt) (signExtByte b))
  | .lbu rs rt imm => some <|
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemByte s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some b => mkNext s (writeReg s (regIdx rt) (zeroExtByte b))
  | .lh rs rt imm => some <|
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemHalf s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some h => mkNext s (writeReg s (regIdx rt) (signExt16 h))
  | .lhu rs rt imm => some <|
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemHalf s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some h => mkNext s (writeReg s (regIdx rt) h)
  | .sh rs rt imm => some <|
    let addr := readReg s (regIdx rs) + signExt16 imm
    match writeMemHalf s addr (readReg s (regIdx rt)) with
    | none => takeAddressException s excCodeAdES addr
    | some s' => mkNext s { s' with llBit := false }
  -- `sb`: `StoreMemory(BYTE, GPR[rt]7..0)` at `base + sext(offset)`; no
  -- alignment requirement, so no Address Error. Clears `llBit` like every
  -- other store (the model's pinned choice; see `State.llBit`).
  | .sb rs rt imm => some <|
    let addr := readReg s (regIdx rs) + signExt16 imm
    match writeMemByte s addr ((readReg s (regIdx rt)) &&& 0xff#32).toNat.toUInt8 with
    | none => takeAddressException s excCodeAdES addr
    | some s' => mkNext s { s' with llBit := false }
  -- `sync`: a no-op for every `stype` (single hart, nothing to order).
  | .sync _ => some <| mkNext s s
  -- `pref`: "Any action, including doing nothing, is permitted … PREF does
  -- not cause addressing-related exceptions" (MD00086 Vol II-A Rev 6.06,
  -- PREF, p.321). A no-op; in particular it does not touch `llBit`. Hints 24..31 "are not
  -- implemented in the Release 6 architecture and generate a Reserved Instruction exception (RI)"
  -- (Table 5.2, p.322-323).
  | .pref _ hint _ => some <|
    if 24 ≤ (hint &&& 31#32).toNat then takeException s excCodeRI else mkNext s s
  -- `synci` (MD00086 Vol II-A Rev 6.06, SYNCI, p.412-413): Operation
  -- `vaddr ← GPR[base] + sign_extend(offset); SynchronizeCacheLines(vaddr)`.
  -- The model has no caches (`Config1.IL = DL = 0`, `config1Value`) and
  -- fetches instructions straight from `physMem`, so every store is already
  -- visible to instruction fetch and there is no cache line to synchronize:
  -- the operation has no effect on architectural state. Its exceptions are
  -- TLB, Cache Error and an implementation-dependent AdEL for kernel
  -- addresses ("It is implementation dependent whether such an exception does
  -- occur", p.412); the model has no TLB or cache and raises none (pin).
  | .synci rs imm => some <|
    let _addr := readReg s (regIdx rs) + signExt16 imm
    mkNext s s
  | _ => none
