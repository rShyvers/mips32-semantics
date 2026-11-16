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
-- BEGIN R6-4
import Semantics.Refine.PcRel
-- END R6-4
-- BEGIN R6-3
import Semantics.Refine.CompactBranch
-- END R6-3
-- BEGIN R6-6B
import Semantics.Refine.FpuR6
-- END R6-6B

/-!
# Refine.Instr — the per-instruction refinement of every constructor (7D)

`InstrRefines i` is the shape of the per-instruction theorems `Refine.<ctor>_refines`
(`docs/MANUAL-SPEC.md` I.2 item 9), quantified over the states the cycle executes an instruction
in: the invariant `Inv s` (`Refine/Defs.lean`), and `w` is a fetched word
that `decode`s to `i` (so `enc i = some w` by `decode_enc`, `Refine/Decode.lean`).

`instrRefines_<ctor>` restates `<ctor>_refines` in that shape, one theorem per constructor of
`Instruction` (201, generated in constructor order; the 12 Release 6 `L`-format conversions of R6-5 and the 26 Release 6 FP instructions of R6-6 in their own blocks), and `allInstrRefines` collects them by
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
  fun s w hg _ hw => ctc1_refines s hg.1 hg.2.1 rt fs w hw  -- R6-5: `FcsrReservedZero`
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
-- BEGIN R6-2
theorem instrRefines_eretnc : InstrRefines .eretnc :=
  fun s w _ _ hw => eretnc_refines s w hw
theorem instrRefines_sigrie (code : W32) : InstrRefines (.sigrie code) :=
  fun s w hg _ hw => sigrie_refines s hg.1 code w hw
theorem instrRefines_cache (base op off : W32) : InstrRefines (.cache base op off) :=
  fun s w hg _ hw => cache_refines s hg.1 base op off w hw
-- END R6-2

-- BEGIN R6-4
theorem instrRefines_mul (rs rt rd : W32) : InstrRefines (.mul rs rt rd) :=
  fun s w hg _ hw => mul_refines s hg.1 rs rt rd w hw
theorem instrRefines_muh (rs rt rd : W32) : InstrRefines (.muh rs rt rd) :=
  fun s w hg _ hw => muh_refines s hg.1 rs rt rd w hw
theorem instrRefines_mulu (rs rt rd : W32) : InstrRefines (.mulu rs rt rd) :=
  fun s w hg _ hw => mulu_refines s hg.1 rs rt rd w hw
theorem instrRefines_muhu (rs rt rd : W32) : InstrRefines (.muhu rs rt rd) :=
  fun s w hg _ hw => muhu_refines s hg.1 rs rt rd w hw
theorem instrRefines_div (rs rt rd : W32) : InstrRefines (.div rs rt rd) :=
  fun s w hg _ hw => div_refines s hg.1 rs rt rd w hw
theorem instrRefines_mod (rs rt rd : W32) : InstrRefines (.mod rs rt rd) :=
  fun s w hg _ hw => mod_refines s hg.1 rs rt rd w hw
theorem instrRefines_divu (rs rt rd : W32) : InstrRefines (.divu rs rt rd) :=
  fun s w hg _ hw => divu_refines s hg.1 rs rt rd w hw
theorem instrRefines_modu (rs rt rd : W32) : InstrRefines (.modu rs rt rd) :=
  fun s w hg _ hw => modu_refines s hg.1 rs rt rd w hw
theorem instrRefines_seleqz (rs rt rd : W32) : InstrRefines (.seleqz rs rt rd) :=
  fun s w hg _ hw => seleqz_refines s hg.1 rs rt rd w hw
theorem instrRefines_selnez (rs rt rd : W32) : InstrRefines (.selnez rs rt rd) :=
  fun s w hg _ hw => selnez_refines s hg.1 rs rt rd w hw
theorem instrRefines_lsa (rs rt rd sa : W32) : InstrRefines (.lsa rs rt rd sa) :=
  fun s w hg _ hw => lsa_refines s hg.1 rs rt rd sa w hw
theorem instrRefines_align (rs rt rd bp : W32) : InstrRefines (.align rs rt rd bp) :=
  fun s w hg _ hw => align_refines s hg.1 rs rt rd bp w hw
theorem instrRefines_bitswap (rd rt : W32) : InstrRefines (.bitswap rd rt) :=
  fun s w hg _ hw => bitswap_refines s hg.1 rd rt w hw
theorem instrRefines_addiupc (rs imm : W32) : InstrRefines (.addiupc rs imm) :=
  fun s w hg _ hw => addiupc_refines s hg.1 rs imm w hw
theorem instrRefines_lwpc (rs off : W32) : InstrRefines (.lwpc rs off) :=
  fun s w hg _ hw => lwpc_refines s hg.1 rs off w hw
theorem instrRefines_auipc (rs imm : W32) : InstrRefines (.auipc rs imm) :=
  fun s w hg _ hw => auipc_refines s hg.1 rs imm w hw
theorem instrRefines_aluipc (rs imm : W32) : InstrRefines (.aluipc rs imm) :=
  fun s w hg _ hw => aluipc_refines s hg.1 rs imm w hw
-- END R6-4
-- BEGIN R6-5
theorem instrRefines_cvtLS (fd fs : W32) : InstrRefines (.cvtLS fd fs) :=
  fun s w hg _ hw => cvtLS_refines s hg.1 fd fs w hw
theorem instrRefines_cvtLD (fd fs : W32) : InstrRefines (.cvtLD fd fs) :=
  fun s w hg _ hw => cvtLD_refines s hg.1 fd fs w hw
theorem instrRefines_roundLS (fd fs : W32) : InstrRefines (.roundLS fd fs) :=
  fun s w hg _ hw => roundLS_refines s hg.1 fd fs w hw
theorem instrRefines_roundLD (fd fs : W32) : InstrRefines (.roundLD fd fs) :=
  fun s w hg _ hw => roundLD_refines s hg.1 fd fs w hw
theorem instrRefines_truncLS (fd fs : W32) : InstrRefines (.truncLS fd fs) :=
  fun s w hg _ hw => truncLS_refines s hg.1 fd fs w hw
theorem instrRefines_truncLD (fd fs : W32) : InstrRefines (.truncLD fd fs) :=
  fun s w hg _ hw => truncLD_refines s hg.1 fd fs w hw
theorem instrRefines_ceilLS (fd fs : W32) : InstrRefines (.ceilLS fd fs) :=
  fun s w hg _ hw => ceilLS_refines s hg.1 fd fs w hw
theorem instrRefines_ceilLD (fd fs : W32) : InstrRefines (.ceilLD fd fs) :=
  fun s w hg _ hw => ceilLD_refines s hg.1 fd fs w hw
theorem instrRefines_floorLS (fd fs : W32) : InstrRefines (.floorLS fd fs) :=
  fun s w hg _ hw => floorLS_refines s hg.1 fd fs w hw
theorem instrRefines_floorLD (fd fs : W32) : InstrRefines (.floorLD fd fs) :=
  fun s w hg _ hw => floorLD_refines s hg.1 fd fs w hw
theorem instrRefines_cvtSL (fd fs : W32) : InstrRefines (.cvtSL fd fs) :=
  fun s w hg _ hw => cvtSL_refines s hg.1 fd fs w hw
theorem instrRefines_cvtDL (fd fs : W32) : InstrRefines (.cvtDL fd fs) :=
  fun s w hg _ hw => cvtDL_refines s hg.1 fd fs w hw
-- END R6-5
-- BEGIN R6-6B
theorem instrRefines_cmpS (cond fd fs ft : W32) : InstrRefines (.cmpS cond fd fs ft) :=
  fun s w hg _ hw => cmpS_refines s hg.1 cond fd fs ft w hw
theorem instrRefines_cmpD (cond fd fs ft : W32) : InstrRefines (.cmpD cond fd fs ft) :=
  fun s w hg _ hw => cmpD_refines s hg.1 cond fd fs ft w hw
theorem instrRefines_bc1eqz (ft off : W32) : InstrRefines (.bc1eqz ft off) :=
  fun s w hg _ hw => bc1eqz_refines s hg.1 ft off w hw
theorem instrRefines_bc1nez (ft off : W32) : InstrRefines (.bc1nez ft off) :=
  fun s w hg _ hw => bc1nez_refines s hg.1 ft off w hw
theorem instrRefines_selS (fd fs ft : W32) : InstrRefines (.selS fd fs ft) :=
  fun s w hg _ hw => selS_refines s hg.1 fd fs ft w hw
theorem instrRefines_selD (fd fs ft : W32) : InstrRefines (.selD fd fs ft) :=
  fun s w hg _ hw => selD_refines s hg.1 fd fs ft w hw
theorem instrRefines_seleqzS (fd fs ft : W32) : InstrRefines (.seleqzS fd fs ft) :=
  fun s w hg _ hw => seleqzS_refines s hg.1 fd fs ft w hw
theorem instrRefines_seleqzD (fd fs ft : W32) : InstrRefines (.seleqzD fd fs ft) :=
  fun s w hg _ hw => seleqzD_refines s hg.1 fd fs ft w hw
theorem instrRefines_selnezS (fd fs ft : W32) : InstrRefines (.selnezS fd fs ft) :=
  fun s w hg _ hw => selnezS_refines s hg.1 fd fs ft w hw
theorem instrRefines_selnezD (fd fs ft : W32) : InstrRefines (.selnezD fd fs ft) :=
  fun s w hg _ hw => selnezD_refines s hg.1 fd fs ft w hw
theorem instrRefines_maddfS (fd fs ft : W32) : InstrRefines (.maddfS fd fs ft) :=
  fun s w hg _ hw => maddfS_refines s hg.1 fd fs ft w hw
theorem instrRefines_maddfD (fd fs ft : W32) : InstrRefines (.maddfD fd fs ft) :=
  fun s w hg _ hw => maddfD_refines s hg.1 fd fs ft w hw
theorem instrRefines_msubfS (fd fs ft : W32) : InstrRefines (.msubfS fd fs ft) :=
  fun s w hg _ hw => msubfS_refines s hg.1 fd fs ft w hw
theorem instrRefines_msubfD (fd fs ft : W32) : InstrRefines (.msubfD fd fs ft) :=
  fun s w hg _ hw => msubfD_refines s hg.1 fd fs ft w hw
theorem instrRefines_maxS (fd fs ft : W32) : InstrRefines (.maxS fd fs ft) :=
  fun s w hg _ hw => maxS_refines s hg.1 fd fs ft w hw
theorem instrRefines_maxD (fd fs ft : W32) : InstrRefines (.maxD fd fs ft) :=
  fun s w hg _ hw => maxD_refines s hg.1 fd fs ft w hw
theorem instrRefines_minS (fd fs ft : W32) : InstrRefines (.minS fd fs ft) :=
  fun s w hg _ hw => minS_refines s hg.1 fd fs ft w hw
theorem instrRefines_minD (fd fs ft : W32) : InstrRefines (.minD fd fs ft) :=
  fun s w hg _ hw => minD_refines s hg.1 fd fs ft w hw
theorem instrRefines_maxaS (fd fs ft : W32) : InstrRefines (.maxaS fd fs ft) :=
  fun s w hg _ hw => maxaS_refines s hg.1 fd fs ft w hw
theorem instrRefines_maxaD (fd fs ft : W32) : InstrRefines (.maxaD fd fs ft) :=
  fun s w hg _ hw => maxaD_refines s hg.1 fd fs ft w hw
theorem instrRefines_minaS (fd fs ft : W32) : InstrRefines (.minaS fd fs ft) :=
  fun s w hg _ hw => minaS_refines s hg.1 fd fs ft w hw
theorem instrRefines_minaD (fd fs ft : W32) : InstrRefines (.minaD fd fs ft) :=
  fun s w hg _ hw => minaD_refines s hg.1 fd fs ft w hw
theorem instrRefines_classS (fd fs : W32) : InstrRefines (.classS fd fs) :=
  fun s w hg _ hw => classS_refines s hg.1 fd fs w hw
theorem instrRefines_classD (fd fs : W32) : InstrRefines (.classD fd fs) :=
  fun s w hg _ hw => classD_refines s hg.1 fd fs w hw
theorem instrRefines_rintS (fd fs : W32) : InstrRefines (.rintS fd fs) :=
  fun s w hg _ hw => rintS_refines s hg.1 fd fs w hw
theorem instrRefines_rintD (fd fs : W32) : InstrRefines (.rintD fd fs) :=
  fun s w hg _ hw => rintD_refines s hg.1 fd fs w hw
-- END R6-6B

-- BEGIN R6-3
theorem instrRefines_bc (off : W32) : InstrRefines (.bc off) :=
  fun s w hg _ hw => bc_refines s hg.1 off w hw
theorem instrRefines_balc (off : W32) : InstrRefines (.balc off) :=
  fun s w hg _ hw => balc_refines s hg.1 off w hw
theorem instrRefines_beqc (rs rt off : W32) : InstrRefines (.beqc rs rt off) :=
  fun s w hg _ hw => beqc_refines s hg.1 rs rt off w hw
theorem instrRefines_bnec (rs rt off : W32) : InstrRefines (.bnec rs rt off) :=
  fun s w hg _ hw => bnec_refines s hg.1 rs rt off w hw
theorem instrRefines_bltc (rs rt off : W32) : InstrRefines (.bltc rs rt off) :=
  fun s w hg _ hw => bltc_refines s hg.1 rs rt off w hw
theorem instrRefines_bgec (rs rt off : W32) : InstrRefines (.bgec rs rt off) :=
  fun s w hg _ hw => bgec_refines s hg.1 rs rt off w hw
theorem instrRefines_bltuc (rs rt off : W32) : InstrRefines (.bltuc rs rt off) :=
  fun s w hg _ hw => bltuc_refines s hg.1 rs rt off w hw
theorem instrRefines_bgeuc (rs rt off : W32) : InstrRefines (.bgeuc rs rt off) :=
  fun s w hg _ hw => bgeuc_refines s hg.1 rs rt off w hw
theorem instrRefines_blezc (rt off : W32) : InstrRefines (.blezc rt off) :=
  fun s w hg _ hw => blezc_refines s hg.1 rt off w hw
theorem instrRefines_bgezc (rt off : W32) : InstrRefines (.bgezc rt off) :=
  fun s w hg _ hw => bgezc_refines s hg.1 rt off w hw
theorem instrRefines_bgtzc (rt off : W32) : InstrRefines (.bgtzc rt off) :=
  fun s w hg _ hw => bgtzc_refines s hg.1 rt off w hw
theorem instrRefines_bltzc (rt off : W32) : InstrRefines (.bltzc rt off) :=
  fun s w hg _ hw => bltzc_refines s hg.1 rt off w hw
theorem instrRefines_beqzc (rs off : W32) : InstrRefines (.beqzc rs off) :=
  fun s w hg _ hw => beqzc_refines s hg.1 rs off w hw
theorem instrRefines_bnezc (rs off : W32) : InstrRefines (.bnezc rs off) :=
  fun s w hg _ hw => bnezc_refines s hg.1 rs off w hw
theorem instrRefines_blezalc (rt off : W32) : InstrRefines (.blezalc rt off) :=
  fun s w hg _ hw => blezalc_refines s hg.1 rt off w hw
theorem instrRefines_bgezalc (rt off : W32) : InstrRefines (.bgezalc rt off) :=
  fun s w hg _ hw => bgezalc_refines s hg.1 rt off w hw
theorem instrRefines_bgtzalc (rt off : W32) : InstrRefines (.bgtzalc rt off) :=
  fun s w hg _ hw => bgtzalc_refines s hg.1 rt off w hw
theorem instrRefines_bltzalc (rt off : W32) : InstrRefines (.bltzalc rt off) :=
  fun s w hg _ hw => bltzalc_refines s hg.1 rt off w hw
theorem instrRefines_beqzalc (rt off : W32) : InstrRefines (.beqzalc rt off) :=
  fun s w hg _ hw => beqzalc_refines s hg.1 rt off w hw
theorem instrRefines_bnezalc (rt off : W32) : InstrRefines (.bnezalc rt off) :=
  fun s w hg _ hw => bnezalc_refines s hg.1 rt off w hw
theorem instrRefines_bovc (rs rt off : W32) : InstrRefines (.bovc rs rt off) :=
  fun s w hg _ hw => bovc_refines s hg.1 rs rt off w hw
theorem instrRefines_bnvc (rs rt off : W32) : InstrRefines (.bnvc rs rt off) :=
  fun s w hg _ hw => bnvc_refines s hg.1 rs rt off w hw
theorem instrRefines_jic (rt off : W32) : InstrRefines (.jic rt off) :=
  fun s w hg _ hw => jic_refines s hg.1 rt off w hw
theorem instrRefines_jialc (rt off : W32) : InstrRefines (.jialc rt off) :=
  fun s w hg _ hw => jialc_refines s hg.1 rt off w hw
-- END R6-3

theorem allInstrRefines (i : Instruction) : InstrRefines i := by
  cases i
  -- BEGIN R6-4
  case mul rs rt rd => exact instrRefines_mul rs rt rd
  case muh rs rt rd => exact instrRefines_muh rs rt rd
  case mulu rs rt rd => exact instrRefines_mulu rs rt rd
  case muhu rs rt rd => exact instrRefines_muhu rs rt rd
  case div rs rt rd => exact instrRefines_div rs rt rd
  case mod rs rt rd => exact instrRefines_mod rs rt rd
  case divu rs rt rd => exact instrRefines_divu rs rt rd
  case modu rs rt rd => exact instrRefines_modu rs rt rd
  case seleqz rs rt rd => exact instrRefines_seleqz rs rt rd
  case selnez rs rt rd => exact instrRefines_selnez rs rt rd
  case lsa rs rt rd sa => exact instrRefines_lsa rs rt rd sa
  case align rs rt rd bp => exact instrRefines_align rs rt rd bp
  case bitswap rd rt => exact instrRefines_bitswap rd rt
  case addiupc rs imm => exact instrRefines_addiupc rs imm
  case lwpc rs off => exact instrRefines_lwpc rs off
  case auipc rs imm => exact instrRefines_auipc rs imm
  case aluipc rs imm => exact instrRefines_aluipc rs imm
  -- END R6-4
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
  -- BEGIN R6-2
  case eretnc => exact instrRefines_eretnc
  case sigrie code => exact instrRefines_sigrie code
  case cache base op off => exact instrRefines_cache base op off
  -- END R6-2
  -- BEGIN R6-3
  case bc off => exact instrRefines_bc off
  case balc off => exact instrRefines_balc off
  case beqc rs rt off => exact instrRefines_beqc rs rt off
  case bnec rs rt off => exact instrRefines_bnec rs rt off
  case bltc rs rt off => exact instrRefines_bltc rs rt off
  case bgec rs rt off => exact instrRefines_bgec rs rt off
  case bltuc rs rt off => exact instrRefines_bltuc rs rt off
  case bgeuc rs rt off => exact instrRefines_bgeuc rs rt off
  case blezc rt off => exact instrRefines_blezc rt off
  case bgezc rt off => exact instrRefines_bgezc rt off
  case bgtzc rt off => exact instrRefines_bgtzc rt off
  case bltzc rt off => exact instrRefines_bltzc rt off
  case beqzc rs off => exact instrRefines_beqzc rs off
  case bnezc rs off => exact instrRefines_bnezc rs off
  case blezalc rt off => exact instrRefines_blezalc rt off
  case bgezalc rt off => exact instrRefines_bgezalc rt off
  case bgtzalc rt off => exact instrRefines_bgtzalc rt off
  case bltzalc rt off => exact instrRefines_bltzalc rt off
  case beqzalc rt off => exact instrRefines_beqzalc rt off
  case bnezalc rt off => exact instrRefines_bnezalc rt off
  case bovc rs rt off => exact instrRefines_bovc rs rt off
  case bnvc rs rt off => exact instrRefines_bnvc rs rt off
  case jic rt off => exact instrRefines_jic rt off
  case jialc rt off => exact instrRefines_jialc rt off
  -- END R6-3
  -- BEGIN R6-5
  case cvtLS fd fs => exact instrRefines_cvtLS fd fs
  case cvtLD fd fs => exact instrRefines_cvtLD fd fs
  case roundLS fd fs => exact instrRefines_roundLS fd fs
  case roundLD fd fs => exact instrRefines_roundLD fd fs
  case truncLS fd fs => exact instrRefines_truncLS fd fs
  case truncLD fd fs => exact instrRefines_truncLD fd fs
  case ceilLS fd fs => exact instrRefines_ceilLS fd fs
  case ceilLD fd fs => exact instrRefines_ceilLD fd fs
  case floorLS fd fs => exact instrRefines_floorLS fd fs
  case floorLD fd fs => exact instrRefines_floorLD fd fs
  case cvtSL fd fs => exact instrRefines_cvtSL fd fs
  case cvtDL fd fs => exact instrRefines_cvtDL fd fs
  -- END R6-5
  -- BEGIN R6-6B
  case cmpS cond fd fs ft => exact instrRefines_cmpS cond fd fs ft
  case cmpD cond fd fs ft => exact instrRefines_cmpD cond fd fs ft
  case bc1eqz ft off => exact instrRefines_bc1eqz ft off
  case bc1nez ft off => exact instrRefines_bc1nez ft off
  case selS fd fs ft => exact instrRefines_selS fd fs ft
  case selD fd fs ft => exact instrRefines_selD fd fs ft
  case seleqzS fd fs ft => exact instrRefines_seleqzS fd fs ft
  case seleqzD fd fs ft => exact instrRefines_seleqzD fd fs ft
  case selnezS fd fs ft => exact instrRefines_selnezS fd fs ft
  case selnezD fd fs ft => exact instrRefines_selnezD fd fs ft
  case maddfS fd fs ft => exact instrRefines_maddfS fd fs ft
  case maddfD fd fs ft => exact instrRefines_maddfD fd fs ft
  case msubfS fd fs ft => exact instrRefines_msubfS fd fs ft
  case msubfD fd fs ft => exact instrRefines_msubfD fd fs ft
  case maxS fd fs ft => exact instrRefines_maxS fd fs ft
  case maxD fd fs ft => exact instrRefines_maxD fd fs ft
  case minS fd fs ft => exact instrRefines_minS fd fs ft
  case minD fd fs ft => exact instrRefines_minD fd fs ft
  case maxaS fd fs ft => exact instrRefines_maxaS fd fs ft
  case maxaD fd fs ft => exact instrRefines_maxaD fd fs ft
  case minaS fd fs ft => exact instrRefines_minaS fd fs ft
  case minaD fd fs ft => exact instrRefines_minaD fd fs ft
  case classS fd fs => exact instrRefines_classS fd fs
  case classD fd fs => exact instrRefines_classD fd fs
  case rintS fd fs => exact instrRefines_rintS fd fs
  case rintD fd fs => exact instrRefines_rintD fd fs
  -- END R6-6B

end Refine
