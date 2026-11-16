import Semantics.Exec.Base

/-!
# Exec.FpuMemory — the FPU loads and stores

The execution of the FPU loads and stores (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of the FPU loads and stores; `none` for every other instruction. -/
def execFpuMemory (s : State) : Instruction → Option State
  | .lwc1 rs ft imm => some <|
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemWord s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some v => mkNext s (writeFpReg s (regIdx ft) v)
  | .swc1 rs ft imm => some <|
    let addr := readReg s (regIdx rs) + signExt16 imm
    match writeMemWord s addr (readFpReg s (regIdx ft)) with
    | none => takeAddressException s excCodeAdES addr
    | some s' => mkNext s { s' with llBit := false }
  -- `ldc1`/`sdc1`: "An Address Error exception occurs if
  -- EffectiveAddress2..0 ≠ 0 (not doubleword-aligned)" (MD00086 Vol II-A
  -- Rev 6.06, LDC1 p.215, SDC1 p.362). The two words of the doubleword are in the byte order of
  -- `profile` (LDC1 p.215: `paddr xor ((BigEndianCPU xor ReverseEndian) || 0^2)`, `memdoubleword ←
  -- memmsw || memlsw`): little-endian, the word at `addr` is the low half (`FPR[ft]`) and the word
  -- at `addr + 4` the high half (`FPR[ft+1]`); big-endian the other way round.
  -- W5: with `Status.FR = 1` the doubleword is one 64-bit FPR.
  | .ldc1 rs ft imm => some <|
    let addr := readReg s (regIdx rs) + signExt16 imm
    if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdEL addr
    else
    match readMemWord s addr, readMemWord s (addr + 4#32) with
    | some w0, some w1 =>
      let lo := if profile.bigEndianMem then w1 else w0
      let hi := if profile.bigEndianMem then w0 else w1
      mkNext s (writeFpReg (writeFpReg s (regIdx ft) lo) (regIdx (ft + 1#32)) hi)
    | _, _ => takeAddressException s excCodeAdEL addr
  | .sdc1 rs ft imm => some <|
    let addr := readReg s (regIdx rs) + signExt16 imm
    let w0 := if profile.bigEndianMem then readFpReg s (regIdx (ft + 1#32)) else readFpReg s (regIdx ft)
    let w1 := if profile.bigEndianMem then readFpReg s (regIdx ft) else readFpReg s (regIdx (ft + 1#32))
    if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdES addr
    else
    match writeMemWord s addr w0 with
    | none => takeAddressException s excCodeAdES addr
    | some s' =>
      match writeMemWord s' (addr + 4#32) w1 with
      | none => takeAddressException s excCodeAdES addr
      | some s'' => mkNext s { s'' with llBit := false }
  | _ => none
