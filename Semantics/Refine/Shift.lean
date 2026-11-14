import Semantics.Refine.BridgeIntAlu

/-!
# Refine.Shift — the shifts and rotates against `execInstr` (sub-wave 7C S1)

`Refine.<ctor>_refines` for `SLL`, `SRL`, `SRA`, `SLLV`, `SRLV`, `SRAV`, `ROTR`, `ROTRV`.

No side condition: the manual's `s ← sa` reads the 5-bit `sa` field (MD00086 Vol II-A Rev 6.06,
SLL p.376, SRL p.385, SRA p.383, ROTR p.339), and since Wave 7R the model shifts by `shamt mod 32`
too, so the refinements hold for every constructor value (the 7C S1 branch had `shamt.toNat < 32`).
-/

namespace Refine

open Manual

/-- **SLL refines.** -/
theorem sll_refines (s : State) (hg : Good s) (rd rt shamt w : W32)
    (hw : enc (.sll rd rt shamt) = some w) :
    Execute modelCtx w (.sll rd rt shamt) (abs s) =
      some (abs (execInstr s (.sll rd rt shamt))) := by
  obtain rfl : rFormat 0#32 0#32 rt rd shamt 0x00#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SLL rd rt shamt) rd (readReg s (regIdx rt) <<< (shamt.toNat % 32))
    (fun h => h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.SLL, readGPR_abs s hg.2.2, sll_eq _ _ (low5_lt _), low5]

/-- **SRL refines.** -/
theorem srl_refines (s : State) (hg : Good s) (rd rt shamt w : W32)
    (hw : enc (.srl rd rt shamt) = some w) :
    Execute modelCtx w (.srl rd rt shamt) (abs s) =
      some (abs (execInstr s (.srl rd rt shamt))) := by
  obtain rfl : rFormat 0#32 0#32 rt rd shamt 0x02#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SRL rd rt shamt) rd (readReg s (regIdx rt) >>> (shamt.toNat % 32))
    (fun h => h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.SRL, readGPR_abs s hg.2.2, srl_eq _ _ (low5_lt _), low5]

/-- **SRA refines.** -/
theorem sra_refines (s : State) (hg : Good s) (rd rt shamt w : W32)
    (hw : enc (.sra rd rt shamt) = some w) :
    Execute modelCtx w (.sra rd rt shamt) (abs s) =
      some (abs (execInstr s (.sra rd rt shamt))) := by
  obtain rfl : rFormat 0#32 0#32 rt rd shamt 0x03#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SRA rd rt shamt) rd ((readReg s (regIdx rt)).sshiftRight (shamt.toNat % 32))
    (fun h => h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.SRA, readGPR_abs s hg.2.2, sra_eq _ _ (low5_lt _), low5]

/-- **SLLV refines.** -/
theorem sllv_refines (s : State) (hg : Good s) (rd rt rs w : W32)
    (hw : enc (.sllv rd rt rs) = some w) :
    Execute modelCtx w (.sllv rd rt rs) (abs s) = some (abs (execInstr s (.sllv rd rt rs))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x04#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SLLV rd rt rs) rd
    (readReg s (regIdx rt) <<< ((readReg s (regIdx rs)).extractLsb 4 0).toNat)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.SLLV, readGPR_abs s hg.2.2, sll_eq _ _ (low5_lt _)]
  rfl

/-- **SRLV refines.** -/
theorem srlv_refines (s : State) (hg : Good s) (rd rt rs w : W32)
    (hw : enc (.srlv rd rt rs) = some w) :
    Execute modelCtx w (.srlv rd rt rs) (abs s) = some (abs (execInstr s (.srlv rd rt rs))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x06#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SRLV rd rt rs) rd
    (readReg s (regIdx rt) >>> ((readReg s (regIdx rs)).extractLsb 4 0).toNat)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.SRLV, readGPR_abs s hg.2.2, srl_eq _ _ (low5_lt _)]
  rfl

/-- **SRAV refines.** -/
theorem srav_refines (s : State) (hg : Good s) (rd rt rs w : W32)
    (hw : enc (.srav rd rt rs) = some w) :
    Execute modelCtx w (.srav rd rt rs) (abs s) = some (abs (execInstr s (.srav rd rt rs))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x07#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SRAV rd rt rs) rd
    ((readReg s (regIdx rt)).sshiftRight ((readReg s (regIdx rs)).extractLsb 4 0).toNat)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.SRAV, readGPR_abs s hg.2.2, sra_eq _ _ (low5_lt _)]
  rfl

/-- `ROTR`'s Operation with its first line evaluated: `ArchitectureRevision() = 2`, so the
UNPREDICTABLE branch is not taken. -/
theorem rotr_run (rd rt sa : W32) (c : Ctx) (f : Frame) :
    (Ops.ROTR rd rt sa).run c f =
      (setGPR (reg rd) ((low (readGPR f.arch (reg rt)) (low sa 5).toNat ++
        bits (readGPR f.arch (reg rt)) 31 (low sa 5).toNat).setWidth 32)).run c f := rfl

/-- `ROTRV`'s Operation with its first line evaluated, as for `ROTR`. -/
theorem rotrv_run (rd rt rs : W32) (c : Ctx) (f : Frame) :
    (Ops.ROTRV rd rt rs).run c f =
      (setGPR (reg rd) ((low (readGPR f.arch (reg rt)) (low (readGPR f.arch (reg rs)) 5).toNat ++
        bits (readGPR f.arch (reg rt)) 31 (low (readGPR f.arch (reg rs)) 5).toNat).setWidth 32)).run c f :=
  rfl

/-- **ROTR refines.** -/
theorem rotr_refines (s : State) (hg : Good s) (rd rt sa w : W32)
    (hw : enc (.rotr rd rt sa) = some w) :
    Execute modelCtx w (.rotr rd rt sa) (abs s) = some (abs (execInstr s (.rotr rd rt sa))) := by
  obtain rfl : rFormat 0#32 1#32 rt rd sa 0x02#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.ROTR rd rt sa) rd ((readReg s (regIdx rt)).rotateRight (sa.toNat % 32))
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  rw [rotr_run]
  alu_run [readGPR_abs s hg.2.2, rotr_eq _ _ (low5_lt _), low5]

/-- **ROTRV refines.** -/
theorem rotrv_refines (s : State) (hg : Good s) (rd rt rs w : W32)
    (hw : enc (.rotrv rd rt rs) = some w) :
    Execute modelCtx w (.rotrv rd rt rs) (abs s) = some (abs (execInstr s (.rotrv rd rt rs))) := by
  obtain rfl : rFormat 0#32 rs rt rd 1#32 0x06#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.ROTRV rd rt rs) rd
    ((readReg s (regIdx rt)).rotateRight ((readReg s (regIdx rs)).extractLsb 4 0).toNat)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  rw [rotrv_run]
  alu_run [readGPR_abs s hg.2.2, rotr_eq _ _ (low5_lt _)]
  rfl

end Refine
