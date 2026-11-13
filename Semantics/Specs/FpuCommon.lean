import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures
import Semantics.Specs.Exception

/-!
# FpuCommon — facts shared by all FPU instructions

Coprocessor Unusable when `Status.CU1 = 0`, and what the `fpCompletes*` right-hand sides of the
arithmetic specs mean: an enabled exception traps (destination not written), otherwise the result is
written and the flags accumulate.

## Theorems in this file (8)

  `fp_coprocessor_unusable` `takeCoprocessorUnusable_spec` `fpCompletesS_trap` `fpCompletesD_trap`
  `fpCompletesCmp_trap` `fpCompletesS_ok` `fpCompletesCmp_ok` `fpCompletesS_exact`
-/

set_option maxRecDepth 4000

/-! ## Floating point (coprocessor 1): common facts

Every coprocessor-1 instruction is specified in terms of the bit-level
functions of `Semantics/FpOps.lean` (`Mips.Fp`). Every theorem takes
`hcu : cu1Enabled s = true` (`Status.CU1 = 1`); `fp_coprocessor_unusable`
covers `CU1 = 0` for all of them at once.

How an FP computational instruction completes is stated once, by
`fpCompletesS` / `fpCompletesD` / `fpCompletesCmp` (`Defs.lean`; written with
`fpeEnabled` / `raiseFlags`, independently of `Step.lean`'s `fpFinish*`,
which go through `fpUpdate`); the per-instruction theorems then only name
the `Mips.Fp` function applied to the operands. -/

/-! ## General theorems -/

/-- **Coprocessor Unusable.** Any instruction that needs coprocessor 1
(`usesCop1`: every COP1/COP1X instruction, `lwc1`/`swc1`/`ldc1`/`sdc1`,
`movf`/`movt`) executed with `Status.CU1 = 0` raises Coprocessor Unusable and
does nothing else (MD00090 Vol III Rev 6.02 §6.2.22, p.100). -/
theorem fp_coprocessor_unusable (p : Program) (s : State) (w : W32) (instr : Instruction)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some instr)
    (huses : usesCop1 instr = true)
    (hnb : isBranchLike instr = false ∨ s.pendingBranch = none)
    (hcu : cu1Enabled s = false) :
    step p s = takeCoprocessorUnusable s := by
  have h1 : (isBranchLike instr && s.pendingBranch.isSome) = false := by
    rcases hnb with h | h <;> simp [h]
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  unfold execInstr
  rw [h1, huses, hcu]
  rfl

/-- **What Coprocessor Unusable does**: `Cause.ExcCode = 11` (CpU),
`Cause.CE = 1` (bits 29..28 = `01`), `Status.EXL` set, `pc` at the general
exception vector — and **no FP register, no FCSR bit, no general register and
no memory changes**. -/
theorem takeCoprocessorUnusable_spec (s s' : State)
    (h : takeCoprocessorUnusable s = StepResult.next s') :
    causeExcCode s' = 11#32 ∧ s'.cp0Cause &&& causeCeMask = 0x10000000#32 ∧
      s'.fpRegs = s.fpRegs ∧ s'.fcsr = s.fcsr ∧ s'.regs = s.regs ∧ s'.mem = s.mem ∧
      s'.pc = exceptionVector s ∧ s'.cp0Status = s.cp0Status ||| statusExlMask := by
  injection h with h
  subst h
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [exceptionEntry_excCode]; decide
  · rw [exceptionEntry_ce]; decide

/-- **The FP trap.** If the operation raised an exception that is enabled in
FCSR, the instruction takes the Floating Point exception: `Cause.ExcCode =
15`, `pc` at the general exception vector, FCSR.Cause = this operation's
exceptions with FCSR.Flags untouched (`fcsrTrapped`) — and **no FP register is
written** (nor any general register or memory). -/
theorem fpCompletesS_trap (s s' : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags)
    (hen : Mips.Fp.fpeEnabled s.fcsr r.2 = true)
    (h : fpCompletesS s fd r = StepResult.next s') :
    causeExcCode s' = 15#32 ∧ s'.fpRegs = s.fpRegs ∧ s'.fcsr = fcsrTrapped s.fcsr r.2 ∧
      s'.regs = s.regs ∧ s'.mem = s.mem ∧ s'.pc = exceptionVector s := by
  unfold fpCompletesS at h
  rw [ite_of_pos hen] at h
  injection h with h
  subst h
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  rw [exceptionEntry_excCode]; decide

/-- The FP trap, for a double result: neither register of the pair is written. -/
theorem fpCompletesD_trap (s s' : State) (fd : W32) (r : BitVec 64 × Mips.Fp.Flags)
    (hen : Mips.Fp.fpeEnabled s.fcsr r.2 = true)
    (h : fpCompletesD s fd r = StepResult.next s') :
    causeExcCode s' = 15#32 ∧ s'.fpRegs = s.fpRegs ∧ s'.fcsr = fcsrTrapped s.fcsr r.2 ∧
      s'.regs = s.regs ∧ s'.mem = s.mem ∧ s'.pc = exceptionVector s := by
  unfold fpCompletesD at h
  rw [ite_of_pos hen] at h
  injection h with h
  subst h
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  rw [exceptionEntry_excCode]; decide

/-- The FP trap, for a compare: no condition code is written. -/
theorem fpCompletesCmp_trap (s s' : State) (cc : W32) (r : Bool × Mips.Fp.Flags)
    (hen : Mips.Fp.fpeEnabled s.fcsr r.2 = true)
    (h : fpCompletesCmp s cc r = StepResult.next s') :
    causeExcCode s' = 15#32 ∧ s'.fpRegs = s.fpRegs ∧ s'.fcsr = fcsrTrapped s.fcsr r.2 ∧
      s'.pc = exceptionVector s := by
  unfold fpCompletesCmp at h
  rw [ite_of_pos hen] at h
  injection h with h
  subst h
  refine ⟨?_, rfl, rfl, rfl⟩
  rw [exceptionEntry_excCode]; decide

/-- **No trap: result bits and FCSR.** When no enabled exception was raised,
the instruction completes: `FPR[fd]` holds exactly the result bits (given a
32-entry FP register file), FCSR is `raiseFlags` of the old FCSR (Cause =
this operation's exceptions, Flags accumulated), and `pc` advances. -/
theorem fpCompletesS_ok (s s' : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags)
    (hen : Mips.Fp.fpeEnabled s.fcsr r.2 = false) (hsize : s.fpRegs.size = 32)
    (h : fpCompletesS s fd r = StepResult.next s') :
    readFpReg s' (regIdx fd) = r.1 ∧ s'.fcsr = Mips.Fp.raiseFlags s.fcsr r.2 ∧
      s'.pc = s.pc + 4#32 ∧ s'.regs = s.regs := by
  unfold fpCompletesS at h
  rw [ite_of_neg (by simp [hen])] at h
  injection h with h
  subst h
  refine ⟨?_, rfl, rfl, rfl⟩
  exact writeFpReg_reads_back s (regIdx fd) r.1 hsize

/-- **A compare writes exactly `FCC[cc]`.** When it does not trap, condition
code `cc` becomes the comparison result and every other condition code keeps
its value; no FP register changes. -/
theorem fpCompletesCmp_ok (s s' : State) (cc : W32) (r : Bool × Mips.Fp.Flags)
    (hen : Mips.Fp.fpeEnabled s.fcsr r.2 = false)
    (h : fpCompletesCmp s cc r = StepResult.next s') (cc' : Fin 8) :
    Mips.Fp.getCC s'.fcsr cc' = (if cc' = ccIdx cc then r.1 else Mips.Fp.getCC s.fcsr cc') ∧
      s'.fpRegs = s.fpRegs ∧ s'.pc = s.pc + 4#32 := by
  unfold fpCompletesCmp at h
  rw [ite_of_neg (by simp [hen])] at h
  injection h with h
  subst h
  exact ⟨Mips.Fp.getCC_setCC_raiseFlags _ _ _ _ _, rfl, rfl⟩

/-- An operation that raises no exception never traps, and leaves
FCSR.Flags, the condition codes, the enables and the rounding mode alone
(it clears FCSR.Cause). -/
theorem fpCompletesS_exact (s : State) (fd : W32) (v : BitVec 32) :
    fpCompletesS s fd (v, Mips.Fp.Flags.none) =
      StepResult.next
        { s with fpRegs := s.fpRegs.set! (regIdx fd).val v,
                 fcsr := Mips.Fp.raiseFlags s.fcsr Mips.Fp.Flags.none, pc := s.pc + 4#32 } := by
  unfold fpCompletesS
  rw [ite_of_neg (by simp [Mips.Fp.fpeEnabled_none])]
