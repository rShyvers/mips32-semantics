import Semantics.FpCompareFacts
import Semantics.Specs.FpuCommon
import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# FpuCompare — FPU compare (`c.cond.fmt`)

Constructors: `cCondS` `cCondD`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  C.cond.fmt p.110-113; C.cond.fmt p.110-113.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Floating point (coprocessor 1)".

## Theorems in this file (11)

  `cCondS_spec_raw` `cCondD_spec_raw` `cCondS_sets_cc` `cCondD_sets_cc` `c_lt_s_sets_cc`
  `c_olt_s_sets_cc` `c_eq_s_sets_cc` `c_le_s_sets_cc` `c_un_s_sets_cc` `c_lt_d_sets_cc`
  `c_eq_d_sets_cc`
-/

set_option maxRecDepth 4000

/-! ## Compare -/

/-- **`c.cond.s`** writes `FCC[cc]` with predicate `cond` (its low four bits) of the two singles:
`Mips.Fp.f32Compare`, completing per `fpCompletesCmp` (MD00086 Vol II-A Rev 6.06,
C.cond.fmt, p.110-113). `fpCompletesCmp_ok` says only `FCC[cc]` changes -/
theorem cCondS_spec_raw (s : State) (w cond cc fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cCondS cond cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      fpCompletesCmp s cc
        (Mips.Fp.f32Compare (cond.setWidth 4) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  fp_step_spec

/-- **`c.cond.d`**: as `cCondS_spec_raw`, on doubles (`Mips.Fp.f64Compare`) -/
theorem cCondD_spec_raw (s : State) (w cond cc fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cCondD cond cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      fpCompletesCmp s cc (Mips.Fp.f64Compare (cond.setWidth 4) (readFpD s fs) (readFpD s ft))) := by
  fp_step_spec

/-! ## What ends up in the condition code

`cCondS_spec_raw` / `cCondD_spec_raw` say which function is applied; the theorems below say what
the instruction leaves in `FCC[cc]` when it does not trap, and — for the common predicates — what
that bit means (`Semantics/FpCompareFacts.lean`: `F32Lt`, `F32Eq`, `F32Unordered`, … are the IEEE
relations written on the sign / exponent / fraction fields, for all operands). The hypothesis
`hen` says no *enabled* exception is raised; a compare raises only Invalid Operation, on a
signaling NaN or, for the signaling predicates, on any NaN (`fpCompareInvalid`). -/

/-- **`c.cond.s` without a trap sets `FCC[cc]` to the predicate's value.** -/
theorem cCondS_sets_cc (s s' : State) (w cond cc fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cCondS cond cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hen : Mips.Fp.fpeEnabled s.fcsr (Mips.Fp.f32Compare (cond.setWidth 4)
      (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))).2 = false)
    (hstep : step s = s') :
    Mips.Fp.getCC s'.fcsr (ccIdx cc) =
      (Mips.Fp.f32Compare (cond.setWidth 4) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))).1 := by
  rw [cCondS_spec_raw s w cond cc fs ft hfetch hdecode hpb hcu] at hstep
  subst hstep
  rw [timerTick_fcsr, (fpCompletesCmp_ok s _ cc _ hen rfl (ccIdx cc)).1, ite_of_pos rfl]

/-- **`c.cond.d` without a trap sets `FCC[cc]` to the predicate's value.** -/
theorem cCondD_sets_cc (s s' : State) (w cond cc fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cCondD cond cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hen : Mips.Fp.fpeEnabled s.fcsr (Mips.Fp.f64Compare (cond.setWidth 4)
      (readFpD s fs) (readFpD s ft)).2 = false)
    (hstep : step s = s') :
    Mips.Fp.getCC s'.fcsr (ccIdx cc) =
      (Mips.Fp.f64Compare (cond.setWidth 4) (readFpD s fs) (readFpD s ft)).1 := by
  rw [cCondD_spec_raw s w cond cc fs ft hfetch hdecode hpb hcu] at hstep
  subst hstep
  rw [timerTick_fcsr, (fpCompletesCmp_ok s _ cc _ hen rfl (ccIdx cc)).1, ite_of_pos rfl]

/-- **`c.lt.s` (cond = 12) sets `FCC[cc]` iff `fs < ft` and neither is a NaN.** -/
theorem c_lt_s_sets_cc (s s' : State) (w cc fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cCondS 12#32 cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hen : Mips.Fp.fpeEnabled s.fcsr (Mips.Fp.f32Compare Mips.Fp.Cond.lt
      (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))).2 = false)
    (hstep : step s = s') :
    Mips.Fp.getCC s'.fcsr (ccIdx cc) = true ↔
      Mips.Fp.F32Lt (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)) := by
  rw [cCondS_sets_cc s s' w 12#32 cc fs ft hfetch hdecode hpb hcu hen hstep]
  exact (Mips.Fp.f32Compare_lt _ _).2

/-- **`c.olt.s` (cond = 4): as `c.lt.s`** (it differs only in not signaling on a quiet NaN). -/
theorem c_olt_s_sets_cc (s s' : State) (w cc fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cCondS 4#32 cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hen : Mips.Fp.fpeEnabled s.fcsr (Mips.Fp.f32Compare Mips.Fp.Cond.olt
      (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))).2 = false)
    (hstep : step s = s') :
    Mips.Fp.getCC s'.fcsr (ccIdx cc) = true ↔
      Mips.Fp.F32Lt (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)) := by
  rw [cCondS_sets_cc s s' w 4#32 cc fs ft hfetch hdecode hpb hcu hen hstep]
  exact (Mips.Fp.f32Compare_lt _ _).1

/-- **`c.eq.s` (cond = 2) sets `FCC[cc]` iff `fs = ft` (with `−0 = +0`) and neither is a NaN.** -/
theorem c_eq_s_sets_cc (s s' : State) (w cc fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cCondS 2#32 cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hen : Mips.Fp.fpeEnabled s.fcsr (Mips.Fp.f32Compare Mips.Fp.Cond.eq
      (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))).2 = false)
    (hstep : step s = s') :
    Mips.Fp.getCC s'.fcsr (ccIdx cc) = true ↔
      Mips.Fp.F32Eq (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)) := by
  rw [cCondS_sets_cc s s' w 2#32 cc fs ft hfetch hdecode hpb hcu hen hstep]
  exact (Mips.Fp.f32Compare_eq _ _).1

/-- **`c.le.s` (cond = 14) sets `FCC[cc]` iff `fs ≤ ft` and neither is a NaN.** -/
theorem c_le_s_sets_cc (s s' : State) (w cc fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cCondS 14#32 cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hen : Mips.Fp.fpeEnabled s.fcsr (Mips.Fp.f32Compare Mips.Fp.Cond.le
      (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))).2 = false)
    (hstep : step s = s') :
    Mips.Fp.getCC s'.fcsr (ccIdx cc) = true ↔
      (Mips.Fp.F32Eq (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)) ∨
        Mips.Fp.F32Lt (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) := by
  rw [cCondS_sets_cc s s' w 14#32 cc fs ft hfetch hdecode hpb hcu hen hstep]
  exact (Mips.Fp.f32Compare_le _ _).2

/-- **`c.un.s` (cond = 1) sets `FCC[cc]` iff an operand is a NaN.** -/
theorem c_un_s_sets_cc (s s' : State) (w cc fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cCondS 1#32 cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hen : Mips.Fp.fpeEnabled s.fcsr (Mips.Fp.f32Compare Mips.Fp.Cond.un
      (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))).2 = false)
    (hstep : step s = s') :
    Mips.Fp.getCC s'.fcsr (ccIdx cc) = true ↔
      Mips.Fp.F32Unordered (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)) := by
  rw [cCondS_sets_cc s s' w 1#32 cc fs ft hfetch hdecode hpb hcu hen hstep]
  exact (Mips.Fp.f32Compare_un _ _).1

/-- **`c.lt.d` (cond = 12) sets `FCC[cc]` iff `fs < ft` and neither is a NaN** (doubles). -/
theorem c_lt_d_sets_cc (s s' : State) (w cc fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cCondD 12#32 cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hen : Mips.Fp.fpeEnabled s.fcsr (Mips.Fp.f64Compare Mips.Fp.Cond.lt
      (readFpD s fs) (readFpD s ft)).2 = false)
    (hstep : step s = s') :
    Mips.Fp.getCC s'.fcsr (ccIdx cc) = true ↔ Mips.Fp.F64Lt (readFpD s fs) (readFpD s ft) := by
  rw [cCondD_sets_cc s s' w 12#32 cc fs ft hfetch hdecode hpb hcu hen hstep]
  exact (Mips.Fp.f64Compare_lt _ _).2

/-- **`c.eq.d` (cond = 2) sets `FCC[cc]` iff `fs = ft` and neither is a NaN** (doubles). -/
theorem c_eq_d_sets_cc (s s' : State) (w cc fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cCondD 2#32 cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hen : Mips.Fp.fpeEnabled s.fcsr (Mips.Fp.f64Compare Mips.Fp.Cond.eq
      (readFpD s fs) (readFpD s ft)).2 = false)
    (hstep : step s = s') :
    Mips.Fp.getCC s'.fcsr (ccIdx cc) = true ↔ Mips.Fp.F64Eq (readFpD s fs) (readFpD s ft) := by
  rw [cCondD_sets_cc s s' w 2#32 cc fs ft hfetch hdecode hpb hcu hen hstep]
  exact (Mips.Fp.f64Compare_eq _ _).1
