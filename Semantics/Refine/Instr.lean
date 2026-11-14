import Semantics.Refine.Cycle
import Semantics.Refine.Invariant
import Semantics.Refine.IntArith
import Semantics.Refine.Memory
import Semantics.Refine.Branch
import Semantics.Refine.BranchLikely
import Semantics.Refine.FpuArith
import Semantics.Refine.Cp0
import Semantics.Refine.Unaligned
import Semantics.Refine.Jump
import Semantics.Refine.System
import Semantics.Refine.Shift
import Semantics.Refine.MulDiv
import Semantics.Refine.BitOps
import Semantics.Refine.Immediate

/-!
# Refine.Instr — the per-instruction refinement, as one hypothesis (7D)

`InstrRefines i` is the shape of the per-instruction theorems `Refine.<ctor>_refines`
(`docs/MANUAL-SPEC.md` I.2 item 9), quantified over the states the cycle executes an instruction
in: the invariant `Inv s`, the instruction is not nullified (`s.nullified = false`, which
`stepCore` guarantees on the execute path), and `w` is a fetched word that `decode`s to `i` (so
`enc i = some w` by `decode_enc`, `Refine/Decode.lean`).

`instrRefines_<ctor>` restates each available `<ctor>_refines` in that shape; `Covered` lists
those constructors and `instrRefines_covered` collects them. The top theorems (`Refine/Step.lean`)
are proved from `PendingRefines`, the same statement for the constructors not yet `Covered`.
-/

namespace Refine

open Manual

/-- **The invariant of the reachable states** (each conjunct is needed by some refinement):
* `Good s`: both register files have 32 entries and `$zero` reads 0 (every per-instruction theorem);
* `FcsrReservedZero s`: FCSR bits 22..18 are 0 (`cfc1_refines`: they "read as zero");
* `StatusImplemented s`: `Status` holds only implemented bits (`resetException_refines_manual`).
`step` preserves it, `resetState`, `hostedStart` and `load p` establish it (`Refine/Step.lean`). -/
def Inv (s : State) : Prop := Good s ∧ FcsrReservedZero s ∧ StatusImplemented s

/-- **The per-instruction refinement of `i`**: from every state the cycle executes `i` in, the
spec's `Execute` of `i` (fetched as `w`) is the model's `execInstr`. -/
def InstrRefines (i : Instruction) : Prop :=
  ∀ (s : State) (w : W32), Inv s → s.nullified = false → decode w = some i → enc i = some w →
    Execute modelCtx w i (abs s) = some (abs (execInstr s i))

/-! ## The available per-instruction theorems in the cycle's shape (generated) -/

theorem instrRefines_clo (rs rd : W32) : InstrRefines (.clo rs rd) :=
  fun s w hg _ _ hw => clo_refines s hg.1 rs rd w hw
theorem instrRefines_clz (rs rd : W32) : InstrRefines (.clz rs rd) :=
  fun s w hg _ _ hw => clz_refines s hg.1 rs rd w hw
theorem instrRefines_seb (rd rt : W32) : InstrRefines (.seb rd rt) :=
  fun s w hg _ _ hw => seb_refines s hg.1 rd rt w hw
theorem instrRefines_seh (rd rt : W32) : InstrRefines (.seh rd rt) :=
  fun s w hg _ _ hw => seh_refines s hg.1 rd rt w hw
theorem instrRefines_wsbh (rd rt : W32) : InstrRefines (.wsbh rd rt) :=
  fun s w hg _ _ hw => wsbh_refines s hg.1 rd rt w hw
theorem instrRefines_ext (rt rs pos size : W32) : InstrRefines (.ext rt rs pos size) :=
  fun s w hg _ _ hw => ext_refines s hg.1 rt rs pos size w hw
theorem instrRefines_ins (rt rs pos size : W32) : InstrRefines (.ins rt rs pos size) :=
  fun s w hg _ _ hw => ins_refines s hg.1 rt rs pos size w hw
theorem instrRefines_beq (rs rt off : W32) : InstrRefines (.beq rs rt off) :=
  fun s w hg hn _ hw => beq_refines s hg.1 hn rs rt off w hw
theorem instrRefines_bne (rs rt off : W32) : InstrRefines (.bne rs rt off) :=
  fun s w hg hn _ hw => bne_refines s hg.1 hn rs rt off w hw
theorem instrRefines_blez (rs off : W32) : InstrRefines (.blez rs off) :=
  fun s w hg hn _ hw => blez_refines s hg.1 hn rs off w hw
theorem instrRefines_bgtz (rs off : W32) : InstrRefines (.bgtz rs off) :=
  fun s w hg hn _ hw => bgtz_refines s hg.1 hn rs off w hw
theorem instrRefines_bltz (rs off : W32) : InstrRefines (.bltz rs off) :=
  fun s w hg hn _ hw => bltz_refines s hg.1 hn rs off w hw
theorem instrRefines_bgez (rs off : W32) : InstrRefines (.bgez rs off) :=
  fun s w hg hn _ hw => bgez_refines s hg.1 hn rs off w hw
theorem instrRefines_bltzal (rs off : W32) : InstrRefines (.bltzal rs off) :=
  fun s w hg hn _ hw => bltzal_refines s hg.1 hn rs off w hw
theorem instrRefines_bgezal (rs off : W32) : InstrRefines (.bgezal rs off) :=
  fun s w hg hn _ hw => bgezal_refines s hg.1 hn rs off w hw
theorem instrRefines_beql (rs rt off : W32) : InstrRefines (.beql rs rt off) :=
  fun s w hg hn _ hw => beql_refines s hg.1 hn rs rt off w hw
theorem instrRefines_bnel (rs rt off : W32) : InstrRefines (.bnel rs rt off) :=
  fun s w hg hn _ hw => bnel_refines s hg.1 hn rs rt off w hw
theorem instrRefines_blezl (rs off : W32) : InstrRefines (.blezl rs off) :=
  fun s w hg hn _ hw => blezl_refines s hg.1 hn rs off w hw
theorem instrRefines_bgtzl (rs off : W32) : InstrRefines (.bgtzl rs off) :=
  fun s w hg hn _ hw => bgtzl_refines s hg.1 hn rs off w hw
theorem instrRefines_bltzl (rs off : W32) : InstrRefines (.bltzl rs off) :=
  fun s w hg hn _ hw => bltzl_refines s hg.1 hn rs off w hw
theorem instrRefines_bgezl (rs off : W32) : InstrRefines (.bgezl rs off) :=
  fun s w hg hn _ hw => bgezl_refines s hg.1 hn rs off w hw
theorem instrRefines_bltzall (rs off : W32) : InstrRefines (.bltzall rs off) :=
  fun s w hg hn _ hw => bltzall_refines s hg.1 hn rs off w hw
theorem instrRefines_bgezall (rs off : W32) : InstrRefines (.bgezall rs off) :=
  fun s w hg hn _ hw => bgezall_refines s hg.1 hn rs off w hw
theorem instrRefines_mtc0 (rt rd sel : W32) : InstrRefines (.mtc0 rt rd sel) :=
  fun s w hg _ _ hw => mtc0_refines s hg.1 rt rd sel w hw
theorem instrRefines_mfc0 (rt rd sel : W32) : InstrRefines (.mfc0 rt rd sel) :=
  fun s w hg _ _ hw => mfc0_refines s hg.1 rt rd sel w hw
theorem instrRefines_di (rt : W32) : InstrRefines (.di rt) :=
  fun s w hg _ _ hw => di_refines s hg.1 rt w hw
theorem instrRefines_ei (rt : W32) : InstrRefines (.ei rt) :=
  fun s w hg _ _ hw => ei_refines s hg.1 rt w hw
theorem instrRefines_rdpgpr (rd rt : W32) : InstrRefines (.rdpgpr rd rt) :=
  fun s w hg _ _ hw => rdpgpr_refines s hg.1 rd rt w hw
theorem instrRefines_wrpgpr (rd rt : W32) : InstrRefines (.wrpgpr rd rt) :=
  fun s w hg _ _ hw => wrpgpr_refines s hg.1 rd rt w hw
theorem instrRefines_addS (fd fs ft : W32) : InstrRefines (.addS fd fs ft) :=
  fun s w hg _ _ hw => addS_refines s hg.1 fd fs ft w hw
theorem instrRefines_addi (rs rt imm : W32) : InstrRefines (.addi rs rt imm) :=
  fun s w hg _ _ hw => addi_refines s hg.1 rs rt imm w hw
theorem instrRefines_addiu (rs rt imm : W32) : InstrRefines (.addiu rs rt imm) :=
  fun s w hg _ _ hw => addiu_refines s hg.1 rs rt imm w hw
theorem instrRefines_slti (rs rt imm : W32) : InstrRefines (.slti rs rt imm) :=
  fun s w hg _ _ hw => slti_refines s hg.1 rs rt imm w hw
theorem instrRefines_sltiu (rs rt imm : W32) : InstrRefines (.sltiu rs rt imm) :=
  fun s w hg _ _ hw => sltiu_refines s hg.1 rs rt imm w hw
theorem instrRefines_andi (rs rt imm : W32) : InstrRefines (.andi rs rt imm) :=
  fun s w hg _ _ hw => andi_refines s hg.1 rs rt imm w hw
theorem instrRefines_ori (rs rt imm : W32) : InstrRefines (.ori rs rt imm) :=
  fun s w hg _ _ hw => ori_refines s hg.1 rs rt imm w hw
theorem instrRefines_xori (rs rt imm : W32) : InstrRefines (.xori rs rt imm) :=
  fun s w hg _ _ hw => xori_refines s hg.1 rs rt imm w hw
theorem instrRefines_lui (rt imm : W32) : InstrRefines (.lui rt imm) :=
  fun s w hg _ _ hw => lui_refines s hg.1 rt imm w hw
theorem instrRefines_add (rs rt rd : W32) : InstrRefines (.add rs rt rd) :=
  fun s w hg _ _ hw => add_refines s hg.1 rs rt rd w hw
theorem instrRefines_addu (rs rt rd : W32) : InstrRefines (.addu rs rt rd) :=
  fun s w hg _ _ hw => addu_refines s hg.1 rs rt rd w hw
theorem instrRefines_sub (rs rt rd : W32) : InstrRefines (.sub rs rt rd) :=
  fun s w hg _ _ hw => sub_refines s hg.1 rs rt rd w hw
theorem instrRefines_subu (rs rt rd : W32) : InstrRefines (.subu rs rt rd) :=
  fun s w hg _ _ hw => subu_refines s hg.1 rs rt rd w hw
theorem instrRefines_and (rs rt rd : W32) : InstrRefines (.and rs rt rd) :=
  fun s w hg _ _ hw => and_refines s hg.1 rs rt rd w hw
theorem instrRefines_or (rs rt rd : W32) : InstrRefines (.or rs rt rd) :=
  fun s w hg _ _ hw => or_refines s hg.1 rs rt rd w hw
theorem instrRefines_xor (rs rt rd : W32) : InstrRefines (.xor rs rt rd) :=
  fun s w hg _ _ hw => xor_refines s hg.1 rs rt rd w hw
theorem instrRefines_nor (rs rt rd : W32) : InstrRefines (.nor rs rt rd) :=
  fun s w hg _ _ hw => nor_refines s hg.1 rs rt rd w hw
theorem instrRefines_slt (rs rt rd : W32) : InstrRefines (.slt rs rt rd) :=
  fun s w hg _ _ hw => slt_refines s hg.1 rs rt rd w hw
theorem instrRefines_sltu (rs rt rd : W32) : InstrRefines (.sltu rs rt rd) :=
  fun s w hg _ _ hw => sltu_refines s hg.1 rs rt rd w hw
theorem instrRefines_movn (rs rt rd : W32) : InstrRefines (.movn rs rt rd) :=
  fun s w hg _ _ hw => movn_refines s hg.1 rs rt rd w hw
theorem instrRefines_movz (rs rt rd : W32) : InstrRefines (.movz rs rt rd) :=
  fun s w hg _ _ hw => movz_refines s hg.1 rs rt rd w hw
theorem instrRefines_j (target : W32) : InstrRefines (.j target) :=
  fun s w hg hn _ hw => j_refines s hg.1 hn target w hw
theorem instrRefines_jal (target : W32) : InstrRefines (.jal target) :=
  fun s w hg hn _ hw => jal_refines s hg.1 hn target w hw
theorem instrRefines_jr (rs : W32) : InstrRefines (.jr rs) :=
  fun s w hg hn _ hw => jr_refines s hg.1 hn rs w hw
theorem instrRefines_jrHb (rs : W32) : InstrRefines (.jrHb rs) :=
  fun s w hg hn _ hw => jrHb_refines s hg.1 hn rs w hw
theorem instrRefines_jalr (rs rd : W32) : InstrRefines (.jalr rs rd) :=
  fun s w hg hn _ hw => jalr_refines s hg.1 hn rs rd w hw
theorem instrRefines_jalrHb (rs rd : W32) : InstrRefines (.jalrHb rs rd) :=
  fun s w hg hn _ hw => jalrHb_refines s hg.1 hn rs rd w hw
theorem instrRefines_lw (base rt off : W32) : InstrRefines (.lw base rt off) :=
  fun s w hg _ _ hw => lw_refines s hg.1 base rt off w hw
theorem instrRefines_sw (base rt off : W32) : InstrRefines (.sw base rt off) :=
  fun s w hg _ _ hw => sw_refines s hg.1 base rt off w hw
theorem instrRefines_mult (rs rt : W32) : InstrRefines (.mult rs rt) :=
  fun s w hg _ _ hw => mult_refines s hg.1 rs rt w hw
theorem instrRefines_multu (rs rt : W32) : InstrRefines (.multu rs rt) :=
  fun s w hg _ _ hw => multu_refines s hg.1 rs rt w hw
theorem instrRefines_div (rs rt : W32) : InstrRefines (.div rs rt) :=
  fun s w hg _ _ hw => div_refines s hg.1 rs rt w hw
theorem instrRefines_divu (rs rt : W32) : InstrRefines (.divu rs rt) :=
  fun s w hg _ _ hw => divu_refines s hg.1 rs rt w hw
theorem instrRefines_mfhi (rd : W32) : InstrRefines (.mfhi rd) :=
  fun s w hg _ _ hw => mfhi_refines s hg.1 rd w hw
theorem instrRefines_mflo (rd : W32) : InstrRefines (.mflo rd) :=
  fun s w hg _ _ hw => mflo_refines s hg.1 rd w hw
theorem instrRefines_mthi (rs : W32) : InstrRefines (.mthi rs) :=
  fun s w hg _ _ hw => mthi_refines s hg.1 rs w hw
theorem instrRefines_mtlo (rs : W32) : InstrRefines (.mtlo rs) :=
  fun s w hg _ _ hw => mtlo_refines s hg.1 rs w hw
theorem instrRefines_mul (rs rt rd : W32) : InstrRefines (.mul rs rt rd) :=
  fun s w hg _ _ hw => mul_refines s hg.1 rs rt rd w hw
theorem instrRefines_madd (rs rt : W32) : InstrRefines (.madd rs rt) :=
  fun s w hg _ _ hw => madd_refines s hg.1 rs rt w hw
theorem instrRefines_maddu (rs rt : W32) : InstrRefines (.maddu rs rt) :=
  fun s w hg _ _ hw => maddu_refines s hg.1 rs rt w hw
theorem instrRefines_msub (rs rt : W32) : InstrRefines (.msub rs rt) :=
  fun s w hg _ _ hw => msub_refines s hg.1 rs rt w hw
theorem instrRefines_msubu (rs rt : W32) : InstrRefines (.msubu rs rt) :=
  fun s w hg _ _ hw => msubu_refines s hg.1 rs rt w hw
theorem instrRefines_sll (rd rt shamt : W32) : InstrRefines (.sll rd rt shamt) :=
  fun s w hg _ _ hw => sll_refines s hg.1 rd rt shamt w hw
theorem instrRefines_srl (rd rt shamt : W32) : InstrRefines (.srl rd rt shamt) :=
  fun s w hg _ _ hw => srl_refines s hg.1 rd rt shamt w hw
theorem instrRefines_sra (rd rt shamt : W32) : InstrRefines (.sra rd rt shamt) :=
  fun s w hg _ _ hw => sra_refines s hg.1 rd rt shamt w hw
theorem instrRefines_sllv (rd rt rs : W32) : InstrRefines (.sllv rd rt rs) :=
  fun s w hg _ _ hw => sllv_refines s hg.1 rd rt rs w hw
theorem instrRefines_srlv (rd rt rs : W32) : InstrRefines (.srlv rd rt rs) :=
  fun s w hg _ _ hw => srlv_refines s hg.1 rd rt rs w hw
theorem instrRefines_srav (rd rt rs : W32) : InstrRefines (.srav rd rt rs) :=
  fun s w hg _ _ hw => srav_refines s hg.1 rd rt rs w hw
theorem instrRefines_rotr (rd rt sa : W32) : InstrRefines (.rotr rd rt sa) :=
  fun s w hg _ _ hw => rotr_refines s hg.1 rd rt sa w hw
theorem instrRefines_rotrv (rd rt rs : W32) : InstrRefines (.rotrv rd rt rs) :=
  fun s w hg _ _ hw => rotrv_refines s hg.1 rd rt rs w hw
theorem instrRefines_wait (code : W32) : InstrRefines (.wait code) :=
  fun s w _ _ _ hw => wait_refines s code w hw
theorem instrRefines_rdhwr (rt rd : W32) : InstrRefines (.rdhwr rt rd) :=
  fun s w hg _ _ hw => rdhwr_refines s hg.1 rt rd w hw
theorem instrRefines_eret : InstrRefines .eret :=
  fun s w _ _ _ hw => eret_refines s w hw
theorem instrRefines_lwl (base rt off : W32) : InstrRefines (.lwl base rt off) :=
  fun s w hg _ _ hw => lwl_refines s hg.1 base rt off w hw


/-- The constructors with an `instrRefines_<ctor>` theorem (83 of 183). -/
def Covered : Instruction → Bool
  | .clo ..
  | .clz ..
  | .seb ..
  | .seh ..
  | .wsbh ..
  | .ext ..
  | .ins ..
  | .beq ..
  | .bne ..
  | .blez ..
  | .bgtz ..
  | .bltz ..
  | .bgez ..
  | .bltzal ..
  | .bgezal ..
  | .beql ..
  | .bnel ..
  | .blezl ..
  | .bgtzl ..
  | .bltzl ..
  | .bgezl ..
  | .bltzall ..
  | .bgezall ..
  | .mtc0 ..
  | .mfc0 ..
  | .di ..
  | .ei ..
  | .rdpgpr ..
  | .wrpgpr ..
  | .addS ..
  | .addi ..
  | .addiu ..
  | .slti ..
  | .sltiu ..
  | .andi ..
  | .ori ..
  | .xori ..
  | .lui ..
  | .add ..
  | .addu ..
  | .sub ..
  | .subu ..
  | .and ..
  | .or ..
  | .xor ..
  | .nor ..
  | .slt ..
  | .sltu ..
  | .movn ..
  | .movz ..
  | .j ..
  | .jal ..
  | .jr ..
  | .jrHb ..
  | .jalr ..
  | .jalrHb ..
  | .lw ..
  | .sw ..
  | .mult ..
  | .multu ..
  | .div ..
  | .divu ..
  | .mfhi ..
  | .mflo ..
  | .mthi ..
  | .mtlo ..
  | .mul ..
  | .madd ..
  | .maddu ..
  | .msub ..
  | .msubu ..
  | .sll ..
  | .srl ..
  | .sra ..
  | .sllv ..
  | .srlv ..
  | .srav ..
  | .rotr ..
  | .rotrv ..
  | .wait ..
  | .rdhwr ..
  | .eret
  | .lwl .. => true
  | _ => false

/-- **The available per-instruction refinements, collected.** -/
theorem instrRefines_covered (i : Instruction) (h : Covered i = true) : InstrRefines i := by
  cases i
  case clo rs rd => exact instrRefines_clo rs rd
  case clz rs rd => exact instrRefines_clz rs rd
  case seb rd rt => exact instrRefines_seb rd rt
  case seh rd rt => exact instrRefines_seh rd rt
  case wsbh rd rt => exact instrRefines_wsbh rd rt
  case ext rt rs pos size => exact instrRefines_ext rt rs pos size
  case ins rt rs pos size => exact instrRefines_ins rt rs pos size
  case beq rs rt off => exact instrRefines_beq rs rt off
  case bne rs rt off => exact instrRefines_bne rs rt off
  case blez rs off => exact instrRefines_blez rs off
  case bgtz rs off => exact instrRefines_bgtz rs off
  case bltz rs off => exact instrRefines_bltz rs off
  case bgez rs off => exact instrRefines_bgez rs off
  case bltzal rs off => exact instrRefines_bltzal rs off
  case bgezal rs off => exact instrRefines_bgezal rs off
  case beql rs rt off => exact instrRefines_beql rs rt off
  case bnel rs rt off => exact instrRefines_bnel rs rt off
  case blezl rs off => exact instrRefines_blezl rs off
  case bgtzl rs off => exact instrRefines_bgtzl rs off
  case bltzl rs off => exact instrRefines_bltzl rs off
  case bgezl rs off => exact instrRefines_bgezl rs off
  case bltzall rs off => exact instrRefines_bltzall rs off
  case bgezall rs off => exact instrRefines_bgezall rs off
  case mtc0 rt rd sel => exact instrRefines_mtc0 rt rd sel
  case mfc0 rt rd sel => exact instrRefines_mfc0 rt rd sel
  case di rt => exact instrRefines_di rt
  case ei rt => exact instrRefines_ei rt
  case rdpgpr rd rt => exact instrRefines_rdpgpr rd rt
  case wrpgpr rd rt => exact instrRefines_wrpgpr rd rt
  case addS fd fs ft => exact instrRefines_addS fd fs ft
  case addi rs rt imm => exact instrRefines_addi rs rt imm
  case addiu rs rt imm => exact instrRefines_addiu rs rt imm
  case slti rs rt imm => exact instrRefines_slti rs rt imm
  case sltiu rs rt imm => exact instrRefines_sltiu rs rt imm
  case andi rs rt imm => exact instrRefines_andi rs rt imm
  case ori rs rt imm => exact instrRefines_ori rs rt imm
  case xori rs rt imm => exact instrRefines_xori rs rt imm
  case lui rt imm => exact instrRefines_lui rt imm
  case add rs rt rd => exact instrRefines_add rs rt rd
  case addu rs rt rd => exact instrRefines_addu rs rt rd
  case sub rs rt rd => exact instrRefines_sub rs rt rd
  case subu rs rt rd => exact instrRefines_subu rs rt rd
  case and rs rt rd => exact instrRefines_and rs rt rd
  case or rs rt rd => exact instrRefines_or rs rt rd
  case xor rs rt rd => exact instrRefines_xor rs rt rd
  case nor rs rt rd => exact instrRefines_nor rs rt rd
  case slt rs rt rd => exact instrRefines_slt rs rt rd
  case sltu rs rt rd => exact instrRefines_sltu rs rt rd
  case movn rs rt rd => exact instrRefines_movn rs rt rd
  case movz rs rt rd => exact instrRefines_movz rs rt rd
  case j target => exact instrRefines_j target
  case jal target => exact instrRefines_jal target
  case jr rs => exact instrRefines_jr rs
  case jrHb rs => exact instrRefines_jrHb rs
  case jalr rs rd => exact instrRefines_jalr rs rd
  case jalrHb rs rd => exact instrRefines_jalrHb rs rd
  case lw base rt off => exact instrRefines_lw base rt off
  case sw base rt off => exact instrRefines_sw base rt off
  case mult rs rt => exact instrRefines_mult rs rt
  case multu rs rt => exact instrRefines_multu rs rt
  case div rs rt => exact instrRefines_div rs rt
  case divu rs rt => exact instrRefines_divu rs rt
  case mfhi rd => exact instrRefines_mfhi rd
  case mflo rd => exact instrRefines_mflo rd
  case mthi rs => exact instrRefines_mthi rs
  case mtlo rs => exact instrRefines_mtlo rs
  case mul rs rt rd => exact instrRefines_mul rs rt rd
  case madd rs rt => exact instrRefines_madd rs rt
  case maddu rs rt => exact instrRefines_maddu rs rt
  case msub rs rt => exact instrRefines_msub rs rt
  case msubu rs rt => exact instrRefines_msubu rs rt
  case sll rd rt shamt => exact instrRefines_sll rd rt shamt
  case srl rd rt shamt => exact instrRefines_srl rd rt shamt
  case sra rd rt shamt => exact instrRefines_sra rd rt shamt
  case sllv rd rt rs => exact instrRefines_sllv rd rt rs
  case srlv rd rt rs => exact instrRefines_srlv rd rt rs
  case srav rd rt rs => exact instrRefines_srav rd rt rs
  case rotr rd rt sa => exact instrRefines_rotr rd rt sa
  case rotrv rd rt rs => exact instrRefines_rotrv rd rt rs
  case wait code => exact instrRefines_wait code
  case rdhwr rt rd => exact instrRefines_rdhwr rt rd
  case eret => exact instrRefines_eret 
  case lwl base rt off => exact instrRefines_lwl base rt off
  all_goals exact absurd h Bool.false_ne_true

/-- **What remains**: the per-instruction refinement of every constructor not yet `Covered` (the
memory/atomic/trap/syscall group and the FPU groups of Wave 7D). -/
def PendingRefines : Prop := ∀ i, Covered i = false → InstrRefines i

theorem allInstrRefines_of (h : PendingRefines) (i : Instruction) : InstrRefines i := by
  cases hc : Covered i
  · exact h i hc
  · exact instrRefines_covered i hc

end Refine
