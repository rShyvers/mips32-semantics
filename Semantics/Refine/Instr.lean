import Semantics.Refine.Cycle
import Semantics.Refine.Invariant
import Semantics.Refine.IntArith
import Semantics.Refine.Shift
import Semantics.Refine.BitOps
import Semantics.Refine.Immediate
import Semantics.Refine.Memory
import Semantics.Refine.Atomic
import Semantics.Refine.Trap
import Semantics.Refine.Syscall
import Semantics.Refine.Branch
import Semantics.Refine.Jump
import Semantics.Refine.Cp0
import Semantics.Refine.System
import Semantics.Refine.FpuArith
import Semantics.Refine.FpuConvert
import Semantics.Refine.FpuMemory
import Semantics.Refine.FpuMove
import Semantics.Refine.FpuControl

/-!
# Refine.Instr — the per-instruction refinement of every constructor (7D)

`InstrRefines i` is the shape of the per-instruction theorems `Refine.<ctor>_refines`
(`docs/MANUAL-SPEC.md` I.2 item 9), quantified over the states the cycle executes an instruction
in: the invariant `Inv s` (`Refine/Defs.lean`), and `w` is a fetched word
that `decode`s to `i` (so `enc i = some w` by `decode_enc`, `Refine/Decode.lean`).

`instrRefines_<ctor>` restates `<ctor>_refines` in that shape, one theorem per constructor of
`Instruction` (119, generated in constructor order), and `allInstrRefines` collects them by
`cases`. `allInstrRefines` is also the completeness check of plan §6.3 for the refinements: a
constructor added to `Instruction` without an `instrRefines_<ctor>` leaves a case of its proof open
and the build fails.
-/

namespace Refine

open Manual

/-- **The per-instruction refinement of `i`**: from every state the cycle executes `i` in, the
spec's `Execute` of `i` (fetched as `w`) is the model's `execInstr`. -/
def InstrRefines (i : Instruction) : Prop :=
  ∀ (s : State) (w : W32), Inv s → decode w = some i → enc i = some w →
    Execute modelCtx w i (abs s) = some (abs (execInstr s i))

/-! ## The per-instruction theorems in the cycle's shape (generated, constructor order) -/

theorem instrRefines_add (rs rt rd : W32) : InstrRefines (.add rs rt rd) :=
  fun s w hg _ hw => add_refines s hg.1 rs rt rd w hw
theorem instrRefines_addu (rs rt rd : W32) : InstrRefines (.addu rs rt rd) :=
  fun s w hg _ hw => addu_refines s hg.1 rs rt rd w hw
theorem instrRefines_sub (rs rt rd : W32) : InstrRefines (.sub rs rt rd) :=
  fun s w hg _ hw => sub_refines s hg.1 rs rt rd w hw
theorem instrRefines_subu (rs rt rd : W32) : InstrRefines (.subu rs rt rd) :=
  fun s w hg _ hw => subu_refines s hg.1 rs rt rd w hw
theorem instrRefines_and (rs rt rd : W32) : InstrRefines (.and rs rt rd) :=
  fun s w hg _ hw => and_refines s hg.1 rs rt rd w hw
theorem instrRefines_or (rs rt rd : W32) : InstrRefines (.or rs rt rd) :=
  fun s w hg _ hw => or_refines s hg.1 rs rt rd w hw
theorem instrRefines_xor (rs rt rd : W32) : InstrRefines (.xor rs rt rd) :=
  fun s w hg _ hw => xor_refines s hg.1 rs rt rd w hw
theorem instrRefines_nor (rs rt rd : W32) : InstrRefines (.nor rs rt rd) :=
  fun s w hg _ hw => nor_refines s hg.1 rs rt rd w hw
theorem instrRefines_slt (rs rt rd : W32) : InstrRefines (.slt rs rt rd) :=
  fun s w hg _ hw => slt_refines s hg.1 rs rt rd w hw
theorem instrRefines_sltu (rs rt rd : W32) : InstrRefines (.sltu rs rt rd) :=
  fun s w hg _ hw => sltu_refines s hg.1 rs rt rd w hw
theorem instrRefines_sll (rd rt shamt : W32) : InstrRefines (.sll rd rt shamt) :=
  fun s w hg _ hw => sll_refines s hg.1 rd rt shamt w hw
theorem instrRefines_pause : InstrRefines .pause :=
  fun s w _ _ hw => pause_refines s w hw
theorem instrRefines_srl (rd rt shamt : W32) : InstrRefines (.srl rd rt shamt) :=
  fun s w hg _ hw => srl_refines s hg.1 rd rt shamt w hw
theorem instrRefines_sra (rd rt shamt : W32) : InstrRefines (.sra rd rt shamt) :=
  fun s w hg _ hw => sra_refines s hg.1 rd rt shamt w hw
theorem instrRefines_sllv (rd rt rs : W32) : InstrRefines (.sllv rd rt rs) :=
  fun s w hg _ hw => sllv_refines s hg.1 rd rt rs w hw
theorem instrRefines_srlv (rd rt rs : W32) : InstrRefines (.srlv rd rt rs) :=
  fun s w hg _ hw => srlv_refines s hg.1 rd rt rs w hw
theorem instrRefines_srav (rd rt rs : W32) : InstrRefines (.srav rd rt rs) :=
  fun s w hg _ hw => srav_refines s hg.1 rd rt rs w hw
theorem instrRefines_rotr (rd rt sa : W32) : InstrRefines (.rotr rd rt sa) :=
  fun s w hg _ hw => rotr_refines s hg.1 rd rt sa w hw
theorem instrRefines_rotrv (rd rt rs : W32) : InstrRefines (.rotrv rd rt rs) :=
  fun s w hg _ hw => rotrv_refines s hg.1 rd rt rs w hw
theorem instrRefines_jalr (rs rd : W32) : InstrRefines (.jalr rs rd) :=
  fun s w hg _ hw => jalr_refines s hg.1 rs rd w hw
theorem instrRefines_jalrHb (rs rd : W32) : InstrRefines (.jalrHb rs rd) :=
  fun s w hg _ hw => jalrHb_refines s hg.1 rs rd w hw
theorem instrRefines_clo (rs rd : W32) : InstrRefines (.clo rs rd) :=
  fun s w hg _ hw => clo_refines s hg.1 rs rd w hw
theorem instrRefines_clz (rs rd : W32) : InstrRefines (.clz rs rd) :=
  fun s w hg _ hw => clz_refines s hg.1 rs rd w hw
theorem instrRefines_seb (rd rt : W32) : InstrRefines (.seb rd rt) :=
  fun s w hg _ hw => seb_refines s hg.1 rd rt w hw
theorem instrRefines_seh (rd rt : W32) : InstrRefines (.seh rd rt) :=
  fun s w hg _ hw => seh_refines s hg.1 rd rt w hw
theorem instrRefines_wsbh (rd rt : W32) : InstrRefines (.wsbh rd rt) :=
  fun s w hg _ hw => wsbh_refines s hg.1 rd rt w hw
theorem instrRefines_ext (rt rs pos size : W32) : InstrRefines (.ext rt rs pos size) :=
  fun s w hg _ hw => ext_refines s hg.1 rt rs pos size w hw
theorem instrRefines_ins (rt rs pos size : W32) : InstrRefines (.ins rt rs pos size) :=
  fun s w hg _ hw => ins_refines s hg.1 rt rs pos size w hw
theorem instrRefines_rdhwr (rt rd sel : W32) : InstrRefines (.rdhwr rt rd sel) :=
  fun s w hg _ hw => rdhwr_refines s hg.1 rt rd sel w hw
theorem instrRefines_addiu (rs rt imm : W32) : InstrRefines (.addiu rs rt imm) :=
  fun s w hg _ hw => addiu_refines s hg.1 rs rt imm w hw
theorem instrRefines_slti (rs rt imm : W32) : InstrRefines (.slti rs rt imm) :=
  fun s w hg _ hw => slti_refines s hg.1 rs rt imm w hw
theorem instrRefines_sltiu (rs rt imm : W32) : InstrRefines (.sltiu rs rt imm) :=
  fun s w hg _ hw => sltiu_refines s hg.1 rs rt imm w hw
theorem instrRefines_andi (rs rt imm : W32) : InstrRefines (.andi rs rt imm) :=
  fun s w hg _ hw => andi_refines s hg.1 rs rt imm w hw
theorem instrRefines_ori (rs rt imm : W32) : InstrRefines (.ori rs rt imm) :=
  fun s w hg _ hw => ori_refines s hg.1 rs rt imm w hw
theorem instrRefines_xori (rs rt imm : W32) : InstrRefines (.xori rs rt imm) :=
  fun s w hg _ hw => xori_refines s hg.1 rs rt imm w hw
theorem instrRefines_aui (rs rt imm : W32) : InstrRefines (.aui rs rt imm) :=
  fun s w hg _ hw => aui_refines s hg.1 rs rt imm w hw
theorem instrRefines_lw (base rt off : W32) : InstrRefines (.lw base rt off) :=
  fun s w hg _ hw => lw_refines s hg.1 base rt off w hw
theorem instrRefines_sw (base rt off : W32) : InstrRefines (.sw base rt off) :=
  fun s w hg _ hw => sw_refines s hg.1 base rt off w hw
theorem instrRefines_lb (base rt off : W32) : InstrRefines (.lb base rt off) :=
  fun s w hg _ hw => lb_refines s hg.1 base rt off w hw
theorem instrRefines_lbu (base rt off : W32) : InstrRefines (.lbu base rt off) :=
  fun s w hg _ hw => lbu_refines s hg.1 base rt off w hw
theorem instrRefines_lh (base rt off : W32) : InstrRefines (.lh base rt off) :=
  fun s w hg _ hw => lh_refines s hg.1 base rt off w hw
theorem instrRefines_lhu (base rt off : W32) : InstrRefines (.lhu base rt off) :=
  fun s w hg _ hw => lhu_refines s hg.1 base rt off w hw
theorem instrRefines_sh (base rt off : W32) : InstrRefines (.sh base rt off) :=
  fun s w hg _ hw => sh_refines s hg.1 base rt off w hw
theorem instrRefines_sb (base rt off : W32) : InstrRefines (.sb base rt off) :=
  fun s w hg _ hw => sb_refines s hg.1 base rt off w hw
theorem instrRefines_ll (base rt off : W32) : InstrRefines (.ll base rt off) :=
  fun s w hg _ hw => ll_refines s hg.1 base rt off w hw
theorem instrRefines_sc (base rt off : W32) : InstrRefines (.sc base rt off) :=
  fun s w hg _ hw => sc_refines s hg.1 base rt off w hw
theorem instrRefines_beq (rs rt off : W32) : InstrRefines (.beq rs rt off) :=
  fun s w hg _ hw => beq_refines s hg.1 rs rt off w hw
theorem instrRefines_bne (rs rt off : W32) : InstrRefines (.bne rs rt off) :=
  fun s w hg _ hw => bne_refines s hg.1 rs rt off w hw
theorem instrRefines_blez (rs off : W32) : InstrRefines (.blez rs off) :=
  fun s w hg _ hw => blez_refines s hg.1 rs off w hw
theorem instrRefines_bgtz (rs off : W32) : InstrRefines (.bgtz rs off) :=
  fun s w hg _ hw => bgtz_refines s hg.1 rs off w hw
theorem instrRefines_bltz (rs off : W32) : InstrRefines (.bltz rs off) :=
  fun s w hg _ hw => bltz_refines s hg.1 rs off w hw
theorem instrRefines_bgez (rs off : W32) : InstrRefines (.bgez rs off) :=
  fun s w hg _ hw => bgez_refines s hg.1 rs off w hw
theorem instrRefines_nal (off : W32) : InstrRefines (.nal off) :=
  fun s w hg _ hw => nal_refines s hg.1 off w hw
theorem instrRefines_bal (off : W32) : InstrRefines (.bal off) :=
  fun s w hg _ hw => bal_refines s hg.1 off w hw
theorem instrRefines_synci (base off : W32) : InstrRefines (.synci base off) :=
  fun s w hg _ hw => synci_refines s hg.1 base off w hw
theorem instrRefines_j (target : W32) : InstrRefines (.j target) :=
  fun s w hg _ hw => j_refines s hg.1 target w hw
theorem instrRefines_jal (target : W32) : InstrRefines (.jal target) :=
  fun s w hg _ hw => jal_refines s hg.1 target w hw
theorem instrRefines_syscall (code : W32) : InstrRefines (.syscall code) :=
  fun s w hg _ hw => syscall_refines s hg.1 code w hw
theorem instrRefines_teq (rs rt code : W32) : InstrRefines (.teq rs rt code) :=
  fun s w hg _ hw => teq_refines s hg.1 rs rt code w hw
theorem instrRefines_tne (rs rt code : W32) : InstrRefines (.tne rs rt code) :=
  fun s w hg _ hw => tne_refines s hg.1 rs rt code w hw
theorem instrRefines_tlt (rs rt code : W32) : InstrRefines (.tlt rs rt code) :=
  fun s w hg _ hw => tlt_refines s hg.1 rs rt code w hw
theorem instrRefines_tge (rs rt code : W32) : InstrRefines (.tge rs rt code) :=
  fun s w hg _ hw => tge_refines s hg.1 rs rt code w hw
theorem instrRefines_tltu (rs rt code : W32) : InstrRefines (.tltu rs rt code) :=
  fun s w hg _ hw => tltu_refines s hg.1 rs rt code w hw
theorem instrRefines_tgeu (rs rt code : W32) : InstrRefines (.tgeu rs rt code) :=
  fun s w hg _ hw => tgeu_refines s hg.1 rs rt code w hw
theorem instrRefines_break (code : W32) : InstrRefines (.break code) :=
  fun s w hg _ hw => break_refines s hg.1 code w hw
theorem instrRefines_sync (stype : W32) : InstrRefines (.sync stype) :=
  fun s w hg _ hw => sync_refines s hg.1 stype w hw
theorem instrRefines_pref (base hint off : W32) : InstrRefines (.pref base hint off) :=
  fun s w hg _ hw => pref_refines s hg.1 base hint off w hw
theorem instrRefines_mfc0 (rt rd sel : W32) : InstrRefines (.mfc0 rt rd sel) :=
  fun s w hg _ hw => mfc0_refines s hg.1 rt rd sel w hw
theorem instrRefines_mtc0 (rt rd sel : W32) : InstrRefines (.mtc0 rt rd sel) :=
  fun s w hg _ hw => mtc0_refines s hg.1 rt rd sel w hw
theorem instrRefines_di (rt : W32) : InstrRefines (.di rt) :=
  fun s w hg _ hw => di_refines s hg.1 rt w hw
theorem instrRefines_ei (rt : W32) : InstrRefines (.ei rt) :=
  fun s w hg _ hw => ei_refines s hg.1 rt w hw
theorem instrRefines_eret : InstrRefines .eret :=
  fun s w _ _ hw => eret_refines s w hw
theorem instrRefines_wait (code : W32) : InstrRefines (.wait code) :=
  fun s w _ _ hw => wait_refines s code w hw
theorem instrRefines_rdpgpr (rd rt : W32) : InstrRefines (.rdpgpr rd rt) :=
  fun s w hg _ hw => rdpgpr_refines s hg.1 rd rt w hw
theorem instrRefines_wrpgpr (rd rt : W32) : InstrRefines (.wrpgpr rd rt) :=
  fun s w hg _ hw => wrpgpr_refines s hg.1 rd rt w hw
theorem instrRefines_mfc1 (rt fs : W32) : InstrRefines (.mfc1 rt fs) :=
  fun s w hg _ hw => mfc1_refines s hg.1 rt fs w hw
theorem instrRefines_mtc1 (rt fs : W32) : InstrRefines (.mtc1 rt fs) :=
  fun s w hg _ hw => mtc1_refines s hg.1 rt fs w hw
theorem instrRefines_mfhc1 (rt fs : W32) : InstrRefines (.mfhc1 rt fs) :=
  fun s w hg _ hw => mfhc1_refines s hg.1 rt fs w hw
theorem instrRefines_mthc1 (rt fs : W32) : InstrRefines (.mthc1 rt fs) :=
  fun s w hg _ hw => mthc1_refines s hg.1 rt fs w hw
theorem instrRefines_cfc1 (rt fs : W32) : InstrRefines (.cfc1 rt fs) :=
  fun s w hg _ hw => cfc1_refines s hg.1 hg.2.1 rt fs w hw
theorem instrRefines_ctc1 (rt fs : W32) : InstrRefines (.ctc1 rt fs) :=
  fun s w hg _ hw => ctc1_refines s hg.1 rt fs w hw
theorem instrRefines_lwc1 (base ft off : W32) : InstrRefines (.lwc1 base ft off) :=
  fun s w hg _ hw => lwc1_refines s hg.1 base ft off w hw
theorem instrRefines_swc1 (base ft off : W32) : InstrRefines (.swc1 base ft off) :=
  fun s w hg _ hw => swc1_refines s hg.1 base ft off w hw
theorem instrRefines_ldc1 (base ft off : W32) : InstrRefines (.ldc1 base ft off) :=
  fun s w hg _ hw => ldc1_refines s hg.1 base ft off w hw
theorem instrRefines_sdc1 (base ft off : W32) : InstrRefines (.sdc1 base ft off) :=
  fun s w hg _ hw => sdc1_refines s hg.1 base ft off w hw
theorem instrRefines_addS (fd fs ft : W32) : InstrRefines (.addS fd fs ft) :=
  fun s w hg _ hw => addS_refines s hg.1 fd fs ft w hw
theorem instrRefines_subS (fd fs ft : W32) : InstrRefines (.subS fd fs ft) :=
  fun s w hg _ hw => subS_refines s hg.1 fd fs ft w hw
theorem instrRefines_mulS (fd fs ft : W32) : InstrRefines (.mulS fd fs ft) :=
  fun s w hg _ hw => mulS_refines s hg.1 fd fs ft w hw
theorem instrRefines_divS (fd fs ft : W32) : InstrRefines (.divS fd fs ft) :=
  fun s w hg _ hw => divS_refines s hg.1 fd fs ft w hw
theorem instrRefines_sqrtS (fd fs : W32) : InstrRefines (.sqrtS fd fs) :=
  fun s w hg _ hw => sqrtS_refines s hg.1 fd fs w hw
theorem instrRefines_absS (fd fs : W32) : InstrRefines (.absS fd fs) :=
  fun s w hg _ hw => absS_refines s hg.1 fd fs w hw
theorem instrRefines_movS (fd fs : W32) : InstrRefines (.movS fd fs) :=
  fun s w hg _ hw => movS_refines s hg.1 fd fs w hw
theorem instrRefines_negS (fd fs : W32) : InstrRefines (.negS fd fs) :=
  fun s w hg _ hw => negS_refines s hg.1 fd fs w hw
theorem instrRefines_recipS (fd fs : W32) : InstrRefines (.recipS fd fs) :=
  fun s w hg _ hw => recipS_refines s hg.1 fd fs w hw
theorem instrRefines_rsqrtS (fd fs : W32) : InstrRefines (.rsqrtS fd fs) :=
  fun s w hg _ hw => rsqrtS_refines s hg.1 fd fs w hw
theorem instrRefines_roundWS (fd fs : W32) : InstrRefines (.roundWS fd fs) :=
  fun s w hg _ hw => roundWS_refines s hg.1 fd fs w hw
theorem instrRefines_truncWS (fd fs : W32) : InstrRefines (.truncWS fd fs) :=
  fun s w hg _ hw => truncWS_refines s hg.1 fd fs w hw
theorem instrRefines_ceilWS (fd fs : W32) : InstrRefines (.ceilWS fd fs) :=
  fun s w hg _ hw => ceilWS_refines s hg.1 fd fs w hw
theorem instrRefines_floorWS (fd fs : W32) : InstrRefines (.floorWS fd fs) :=
  fun s w hg _ hw => floorWS_refines s hg.1 fd fs w hw
theorem instrRefines_cvtWS (fd fs : W32) : InstrRefines (.cvtWS fd fs) :=
  fun s w hg _ hw => cvtWS_refines s hg.1 fd fs w hw
theorem instrRefines_cvtDS (fd fs : W32) : InstrRefines (.cvtDS fd fs) :=
  fun s w hg _ hw => cvtDS_refines s hg.1 fd fs w hw
theorem instrRefines_cvtSW (fd fs : W32) : InstrRefines (.cvtSW fd fs) :=
  fun s w hg _ hw => cvtSW_refines s hg.1 fd fs w hw
theorem instrRefines_cvtDW (fd fs : W32) : InstrRefines (.cvtDW fd fs) :=
  fun s w hg _ hw => cvtDW_refines s hg.1 fd fs w hw
theorem instrRefines_addD (fd fs ft : W32) : InstrRefines (.addD fd fs ft) :=
  fun s w hg _ hw => addD_refines s hg.1 fd fs ft w hw
theorem instrRefines_subD (fd fs ft : W32) : InstrRefines (.subD fd fs ft) :=
  fun s w hg _ hw => subD_refines s hg.1 fd fs ft w hw
theorem instrRefines_mulD (fd fs ft : W32) : InstrRefines (.mulD fd fs ft) :=
  fun s w hg _ hw => mulD_refines s hg.1 fd fs ft w hw
theorem instrRefines_divD (fd fs ft : W32) : InstrRefines (.divD fd fs ft) :=
  fun s w hg _ hw => divD_refines s hg.1 fd fs ft w hw
theorem instrRefines_sqrtD (fd fs : W32) : InstrRefines (.sqrtD fd fs) :=
  fun s w hg _ hw => sqrtD_refines s hg.1 fd fs w hw
theorem instrRefines_absD (fd fs : W32) : InstrRefines (.absD fd fs) :=
  fun s w hg _ hw => absD_refines s hg.1 fd fs w hw
theorem instrRefines_movD (fd fs : W32) : InstrRefines (.movD fd fs) :=
  fun s w hg _ hw => movD_refines s hg.1 fd fs w hw
theorem instrRefines_negD (fd fs : W32) : InstrRefines (.negD fd fs) :=
  fun s w hg _ hw => negD_refines s hg.1 fd fs w hw
theorem instrRefines_recipD (fd fs : W32) : InstrRefines (.recipD fd fs) :=
  fun s w hg _ hw => recipD_refines s hg.1 fd fs w hw
theorem instrRefines_rsqrtD (fd fs : W32) : InstrRefines (.rsqrtD fd fs) :=
  fun s w hg _ hw => rsqrtD_refines s hg.1 fd fs w hw
theorem instrRefines_roundWD (fd fs : W32) : InstrRefines (.roundWD fd fs) :=
  fun s w hg _ hw => roundWD_refines s hg.1 fd fs w hw
theorem instrRefines_truncWD (fd fs : W32) : InstrRefines (.truncWD fd fs) :=
  fun s w hg _ hw => truncWD_refines s hg.1 fd fs w hw
theorem instrRefines_ceilWD (fd fs : W32) : InstrRefines (.ceilWD fd fs) :=
  fun s w hg _ hw => ceilWD_refines s hg.1 fd fs w hw
theorem instrRefines_floorWD (fd fs : W32) : InstrRefines (.floorWD fd fs) :=
  fun s w hg _ hw => floorWD_refines s hg.1 fd fs w hw
theorem instrRefines_cvtWD (fd fs : W32) : InstrRefines (.cvtWD fd fs) :=
  fun s w hg _ hw => cvtWD_refines s hg.1 fd fs w hw
theorem instrRefines_cvtSD (fd fs : W32) : InstrRefines (.cvtSD fd fs) :=
  fun s w hg _ hw => cvtSD_refines s hg.1 fd fs w hw

theorem allInstrRefines (i : Instruction) : InstrRefines i := by
  cases i
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
  case sll rd rt shamt => exact instrRefines_sll rd rt shamt
  case pause => exact instrRefines_pause
  case srl rd rt shamt => exact instrRefines_srl rd rt shamt
  case sra rd rt shamt => exact instrRefines_sra rd rt shamt
  case sllv rd rt rs => exact instrRefines_sllv rd rt rs
  case srlv rd rt rs => exact instrRefines_srlv rd rt rs
  case srav rd rt rs => exact instrRefines_srav rd rt rs
  case rotr rd rt sa => exact instrRefines_rotr rd rt sa
  case rotrv rd rt rs => exact instrRefines_rotrv rd rt rs
  case jalr rs rd => exact instrRefines_jalr rs rd
  case jalrHb rs rd => exact instrRefines_jalrHb rs rd
  case clo rs rd => exact instrRefines_clo rs rd
  case clz rs rd => exact instrRefines_clz rs rd
  case seb rd rt => exact instrRefines_seb rd rt
  case seh rd rt => exact instrRefines_seh rd rt
  case wsbh rd rt => exact instrRefines_wsbh rd rt
  case ext rt rs pos size => exact instrRefines_ext rt rs pos size
  case ins rt rs pos size => exact instrRefines_ins rt rs pos size
  case rdhwr rt rd sel => exact instrRefines_rdhwr rt rd sel
  case addiu rs rt imm => exact instrRefines_addiu rs rt imm
  case slti rs rt imm => exact instrRefines_slti rs rt imm
  case sltiu rs rt imm => exact instrRefines_sltiu rs rt imm
  case andi rs rt imm => exact instrRefines_andi rs rt imm
  case ori rs rt imm => exact instrRefines_ori rs rt imm
  case xori rs rt imm => exact instrRefines_xori rs rt imm
  case aui rs rt imm => exact instrRefines_aui rs rt imm
  case lw base rt off => exact instrRefines_lw base rt off
  case sw base rt off => exact instrRefines_sw base rt off
  case lb base rt off => exact instrRefines_lb base rt off
  case lbu base rt off => exact instrRefines_lbu base rt off
  case lh base rt off => exact instrRefines_lh base rt off
  case lhu base rt off => exact instrRefines_lhu base rt off
  case sh base rt off => exact instrRefines_sh base rt off
  case sb base rt off => exact instrRefines_sb base rt off
  case ll base rt off => exact instrRefines_ll base rt off
  case sc base rt off => exact instrRefines_sc base rt off
  case beq rs rt off => exact instrRefines_beq rs rt off
  case bne rs rt off => exact instrRefines_bne rs rt off
  case blez rs off => exact instrRefines_blez rs off
  case bgtz rs off => exact instrRefines_bgtz rs off
  case bltz rs off => exact instrRefines_bltz rs off
  case bgez rs off => exact instrRefines_bgez rs off
  case nal off => exact instrRefines_nal off
  case bal off => exact instrRefines_bal off
  case synci base off => exact instrRefines_synci base off
  case j target => exact instrRefines_j target
  case jal target => exact instrRefines_jal target
  case syscall code => exact instrRefines_syscall code
  case teq rs rt code => exact instrRefines_teq rs rt code
  case tne rs rt code => exact instrRefines_tne rs rt code
  case tlt rs rt code => exact instrRefines_tlt rs rt code
  case tge rs rt code => exact instrRefines_tge rs rt code
  case tltu rs rt code => exact instrRefines_tltu rs rt code
  case tgeu rs rt code => exact instrRefines_tgeu rs rt code
  case «break» code => exact instrRefines_break code
  case sync stype => exact instrRefines_sync stype
  case pref base hint off => exact instrRefines_pref base hint off
  case mfc0 rt rd sel => exact instrRefines_mfc0 rt rd sel
  case mtc0 rt rd sel => exact instrRefines_mtc0 rt rd sel
  case di rt => exact instrRefines_di rt
  case ei rt => exact instrRefines_ei rt
  case eret => exact instrRefines_eret
  case wait code => exact instrRefines_wait code
  case rdpgpr rd rt => exact instrRefines_rdpgpr rd rt
  case wrpgpr rd rt => exact instrRefines_wrpgpr rd rt
  case mfc1 rt fs => exact instrRefines_mfc1 rt fs
  case mtc1 rt fs => exact instrRefines_mtc1 rt fs
  case mfhc1 rt fs => exact instrRefines_mfhc1 rt fs
  case mthc1 rt fs => exact instrRefines_mthc1 rt fs
  case cfc1 rt fs => exact instrRefines_cfc1 rt fs
  case ctc1 rt fs => exact instrRefines_ctc1 rt fs
  case lwc1 base ft off => exact instrRefines_lwc1 base ft off
  case swc1 base ft off => exact instrRefines_swc1 base ft off
  case ldc1 base ft off => exact instrRefines_ldc1 base ft off
  case sdc1 base ft off => exact instrRefines_sdc1 base ft off
  case addS fd fs ft => exact instrRefines_addS fd fs ft
  case subS fd fs ft => exact instrRefines_subS fd fs ft
  case mulS fd fs ft => exact instrRefines_mulS fd fs ft
  case divS fd fs ft => exact instrRefines_divS fd fs ft
  case sqrtS fd fs => exact instrRefines_sqrtS fd fs
  case absS fd fs => exact instrRefines_absS fd fs
  case movS fd fs => exact instrRefines_movS fd fs
  case negS fd fs => exact instrRefines_negS fd fs
  case recipS fd fs => exact instrRefines_recipS fd fs
  case rsqrtS fd fs => exact instrRefines_rsqrtS fd fs
  case roundWS fd fs => exact instrRefines_roundWS fd fs
  case truncWS fd fs => exact instrRefines_truncWS fd fs
  case ceilWS fd fs => exact instrRefines_ceilWS fd fs
  case floorWS fd fs => exact instrRefines_floorWS fd fs
  case cvtWS fd fs => exact instrRefines_cvtWS fd fs
  case cvtDS fd fs => exact instrRefines_cvtDS fd fs
  case cvtSW fd fs => exact instrRefines_cvtSW fd fs
  case cvtDW fd fs => exact instrRefines_cvtDW fd fs
  case addD fd fs ft => exact instrRefines_addD fd fs ft
  case subD fd fs ft => exact instrRefines_subD fd fs ft
  case mulD fd fs ft => exact instrRefines_mulD fd fs ft
  case divD fd fs ft => exact instrRefines_divD fd fs ft
  case sqrtD fd fs => exact instrRefines_sqrtD fd fs
  case absD fd fs => exact instrRefines_absD fd fs
  case movD fd fs => exact instrRefines_movD fd fs
  case negD fd fs => exact instrRefines_negD fd fs
  case recipD fd fs => exact instrRefines_recipD fd fs
  case rsqrtD fd fs => exact instrRefines_rsqrtD fd fs
  case roundWD fd fs => exact instrRefines_roundWD fd fs
  case truncWD fd fs => exact instrRefines_truncWD fd fs
  case ceilWD fd fs => exact instrRefines_ceilWD fd fs
  case floorWD fd fs => exact instrRefines_floorWD fd fs
  case cvtWD fd fs => exact instrRefines_cvtWD fd fs
  case cvtSD fd fs => exact instrRefines_cvtSD fd fs

end Refine
