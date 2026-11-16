import Semantics.Refine.BridgeIntAlu

/-!
# Refine.Immediate — arithmetic and logical with a 16-bit immediate against `execInstr`

`Refine.<ctor>_refines` for `ADDIU`, `SLTI`, `SLTIU`, `ANDI`, `ORI`, `XORI`, `AUI` (Release 6
removed `ADDI`; LUI is AUI with `rs = 0`). `sign_extend(immediate)` is the model's `signExt16`
(`offset16`), `zero_extend(immediate)` its `zeroExt16`.
-/

namespace Refine

open Manual

/-- `sign_extend(immediate << 16)` (the 32-bit `immediate || 0^16`) is the model's
`zeroExt16 imm <<< 16`. -/
theorem aui_eq (imm : W32) : sign_extend (imm16 imm ++ 0#16) = zeroExt16 imm <<< 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [sign_extend, imm16, zeroExt16, BitVec.signExtend_eq, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_extractLsb, BitVec.truncate_eq_setWidth, BitVec.getLsbD_zero]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-- **ADDIU refines.** -/
theorem addiu_refines (s : State) (hg : Good s) (rs rt imm w : W32)
    (hw : enc (.addiu rs rt imm) = some w) :
    Execute modelCtx w (.addiu rs rt imm) (abs s) = some (abs (execInstr s (.addiu rs rt imm))) := by
  obtain rfl : iFormat 0x09#32 rs rt imm = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.ADDIU rs rt imm) rt (readReg s (regIdx rs) + signExt16 imm)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.ADDIU, readGPR_abs s hg.2.2, offset16]

/-- **SLTI refines.** -/
theorem slti_refines (s : State) (hg : Good s) (rs rt imm w : W32)
    (hw : enc (.slti rs rt imm) = some w) :
    Execute modelCtx w (.slti rs rt imm) (abs s) = some (abs (execInstr s (.slti rs rt imm))) := by
  obtain rfl : iFormat 0x0A#32 rs rt imm = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SLTI rs rt imm) rt
    (if asSigned (readReg s (regIdx rs)) < asSigned (signExt16 imm) then 1#32 else 0#32)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  by_cases hc : asSigned (readReg s (regIdx rs)) < asSigned (signExt16 imm) <;>
    alu_run [Ops.SLTI, readGPR_abs s hg.2.2, offset16, slt_w, one_w, hc, decide_true, decide_false] <;>
    rfl

/-- **SLTIU refines.** -/
theorem sltiu_refines (s : State) (hg : Good s) (rs rt imm w : W32)
    (hw : enc (.sltiu rs rt imm) = some w) :
    Execute modelCtx w (.sltiu rs rt imm) (abs s) = some (abs (execInstr s (.sltiu rs rt imm))) := by
  obtain rfl : iFormat 0x0B#32 rs rt imm = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SLTIU rs rt imm) rt
    (if (readReg s (regIdx rs)).toNat < (signExt16 imm).toNat then 1#32 else 0#32)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  by_cases hc : (readReg s (regIdx rs)).toNat < (signExt16 imm).toNat <;>
    alu_run [Ops.SLTIU, readGPR_abs s hg.2.2, offset16, ult_w, one_w, hc, decide_true, decide_false] <;>
    rfl

/-- **ANDI refines.** -/
theorem andi_refines (s : State) (hg : Good s) (rs rt imm w : W32)
    (hw : enc (.andi rs rt imm) = some w) :
    Execute modelCtx w (.andi rs rt imm) (abs s) = some (abs (execInstr s (.andi rs rt imm))) := by
  obtain rfl : iFormat 0x0C#32 rs rt imm = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.ANDI rs rt imm) rt (readReg s (regIdx rs) &&& zeroExt16 imm)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.ANDI, readGPR_abs s hg.2.2]
  rfl

/-- **ORI refines.** -/
theorem ori_refines (s : State) (hg : Good s) (rs rt imm w : W32)
    (hw : enc (.ori rs rt imm) = some w) :
    Execute modelCtx w (.ori rs rt imm) (abs s) = some (abs (execInstr s (.ori rs rt imm))) := by
  obtain rfl : iFormat 0x0D#32 rs rt imm = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.ORI rs rt imm) rt (readReg s (regIdx rs) ||| zeroExt16 imm)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.ORI, readGPR_abs s hg.2.2]
  rfl

/-- **XORI refines.** -/
theorem xori_refines (s : State) (hg : Good s) (rs rt imm w : W32)
    (hw : enc (.xori rs rt imm) = some w) :
    Execute modelCtx w (.xori rs rt imm) (abs s) = some (abs (execInstr s (.xori rs rt imm))) := by
  obtain rfl : iFormat 0x0E#32 rs rt imm = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.XORI rs rt imm) rt (readReg s (regIdx rs) ^^^ zeroExt16 imm)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.XORI, readGPR_abs s hg.2.2]
  rfl

/-- **AUI refines** (Release 6; LUI is AUI with `rs = 0`). -/
theorem aui_refines (s : State) (hg : Good s) (rs rt imm w : W32)
    (hw : enc (.aui rs rt imm) = some w) :
    Execute modelCtx w (.aui rs rt imm) (abs s) = some (abs (execInstr s (.aui rs rt imm))) := by
  obtain rfl : iFormat 0x0F#32 rs rt imm = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.AUI rs rt imm) rt (readReg s (regIdx rs) + (zeroExt16 imm <<< 16))
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.AUI, readGPR_abs s hg.2.2, aui_eq]

end Refine
