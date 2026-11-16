import Semantics.Refine.BridgeMem
import Semantics.Refine.Immediate

/-!
# Refine.PcRel — the Release 6 PC-relative instructions against `execInstr` (R6-4)

`ADDIUPC`, `AUIPC`, `ALUIPC`, `LWPC` (MD00086 Vol II-A Rev 6.06, p.37, p.48, p.43, p.246). The
manual's `PC` is the address of the instruction (`abs s` has `PC = s.pc`); the 19-bit immediate of
`ADDIUPC`/`LWPC` is sign-extended as the model's `signExt19`. `LWPC` is `LW` at `PC +
sign_extend(offset) << 2`: the same alignment check, translation and memory read (`lw_refines`).
-/

namespace Refine

open Manual

/-- The opcode of a `pc19Format` word (ADDIUPC, LWPC): PCREL. -/
theorem opcode_pc19Format (rs minor imm : W32) : opcode (pc19Format rs minor imm) = 0x3B#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [opcode, pc19Format, fld, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-- `sign_extend(immediate << 2)` of `ADDIUPC` (p.37) is the model's `signExt19 imm <<< 2`. -/
theorem pc19_offset (imm : W32) : sign_extend (Ops.imm19 imm ++ 0#2) = signExt19 imm <<< 2 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [sign_extend, Ops.imm19, signExt19, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb, BitVec.msb_append]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-- `sign_extend(offset)` of `LWPC` (p.246) is the model's `signExt19`. -/
theorem offset19 (imm : W32) : sign_extend (Ops.imm19 imm) = signExt19 imm := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [sign_extend, Ops.imm19, signExt19, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_extractLsb, BitVec.msb_eq_getLsbD_last]

/-- **ADDIUPC refines.** -/
theorem addiupc_refines (s : State) (hg : Good s) (rs imm w : W32)
    (hw : enc (.addiupc rs imm) = some w) :
    Execute modelCtx w (.addiupc rs imm) (abs s) = some (abs (execInstr s (.addiupc rs imm))) := by
  obtain rfl : pc19Format rs 0#32 imm = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.ADDIUPC rs imm) rs (s.pc + (signExt19 imm <<< 2))
    (fun h => nomatch h) ?_ ?_ rfl ?_ (execInstr_body s _ rfl rfl rfl)
  · rw [InCop1Space, opcode_pc19Format]; rfl
  · rw [InCop0Space, opcode_pc19Format]; rfl
  · alu_run [Ops.ADDIUPC, PC, abs_PC, memory_address, pc19_offset]

/-- **AUIPC refines.** -/
theorem auipc_refines (s : State) (hg : Good s) (rs imm w : W32)
    (hw : enc (.auipc rs imm) = some w) :
    Execute modelCtx w (.auipc rs imm) (abs s) = some (abs (execInstr s (.auipc rs imm))) := by
  obtain rfl : iFormat 0x3B#32 rs 0x1E#32 imm = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.AUIPC rs imm) rs (s.pc + (zeroExt16 imm <<< 16))
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.AUIPC, PC, abs_PC, memory_address, aui_eq]

/-- **ALUIPC refines.** -/
theorem aluipc_refines (s : State) (hg : Good s) (rs imm w : W32)
    (hw : enc (.aluipc rs imm) = some w) :
    Execute modelCtx w (.aluipc rs imm) (abs s) = some (abs (execInstr s (.aluipc rs imm))) := by
  obtain rfl : iFormat 0x3B#32 rs 0x1F#32 imm = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.ALUIPC rs imm) rs ((s.pc + (zeroExt16 imm <<< 16)) &&& ~~~0xFFFF#32)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.ALUIPC, PC, abs_PC, memory_address, aui_eq, BitVec.and_comm (~~~0x0FFFF#32)]

/-- **LWPC refines.** -/
theorem lwpc_refines (s : State) (hg : Good s) (rs off w : W32)
    (hw : enc (.lwpc rs off) = some w) :
    Execute modelCtx w (.lwpc rs off) (abs s) = some (abs (execInstr s (.lwpc rs off))) := by
  obtain ⟨hsz, -, -⟩ := hg
  have hw' : w = pc19Format rs 1#32 off := (Option.some.inj hw).symm
  have hc1 : InCop1Space w = false := by subst hw'; rw [InCop1Space, opcode_pc19Format]; rfl
  have hc0 : InCop0Space w = false := by subst hw'; rw [InCop0Space, opcode_pc19Format]; rfl
  rw [execInstr_body s _ rfl rfl rfl, execute_run modelCtx w _ _ (Ops.LWPC rs off) rfl hc1 hc0 rfl]
  exec_unfold
  simp only [Pseudo.run, Ops.LWPC, bind, PC, abs_PC, offset19]
  generalize s.pc + (signExt19 off <<< 2) = va
  by_cases hal : va.toNat % 4 = 0
  · have hm : (bits va 1 0 != 0#2) = false := by rw [misaligned_eq]; simp [hal]
    simp only [hm, Bool.false_eq_true, ↓reduceIte]
    rw [addrTrans_run s va .DATA .LOAD _ _ rfl, readMemWord_eq s va hal]
    unfold translate
    cases accessAllowed s va
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
      rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_adel]
    · simp only [↓reduceIte, Option.map_some, loadMemory_model, setGPR, abs_Mem]
      rw [complete_writeReg_eq s hsz, regIdx_eq_reg]
  · have hm : (bits va 1 0 != 0#2) = true := by rw [misaligned_eq]; simp [hal]
    have hr : readMemWord s va = none := by unfold readMemWord; simp [hal]
    simp only [hm, ↓reduceIte, SignalException, hr]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_adel]

end Refine
