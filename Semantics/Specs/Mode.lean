import Semantics.Specs.Cp0
import Semantics.Specs.Exception

/-!
# Mode — Kernel Mode and User Mode

The two operating modes MD00090 Vol III Rev 6.02 ch.3 (p.21-23) requires ("The MIPS32 and
microMIPS32 PRA requires two operating modes: User Mode and Kernel Mode", p.21), as
`Step.lean` defines them: `kernelMode` (§3.2: `KSU = 0b00` or `EXL = 1` or `ERL = 1`; without
Supervisor Mode `KSU = UM ‖ 0`), `userMode` (§3.4: `UM = 1`, `EXL = 0`, `ERL = 0`), and
`cp0Usable` (§3.5.3: Kernel Mode or `Status.CU0 = 1`).

What the theorems say: exactly one of the two modes holds; exception entry always enters Kernel
Mode and leaves `Status.UM` alone (so the handler runs in Kernel Mode, and `eret` returns to the
mode the exception came from); `eret` from a handler that interrupted User Mode returns to User
Mode at `EPC`. Coprocessor Unusable for coprocessor-0 instructions outside Kernel Mode is
`cp0_instruction_user_mode_unusable` (`Cp0.lean`) and `step_reserved_cop0_unusable` (`Fetch.lean`).

User-Mode address checks (a reference to kseg0/kseg1/kseg2/kseg3 from User Mode raises Address
Error, Vol III Table 4.2, p.30) belong to the MMU and are not modeled yet.

`orMask_and_self`, `or_and_disjoint` are bit-mask proof devices.

## Theorems in this file (10)

  `orMask_and_self` `or_and_disjoint` `userMode_iff` `kernelMode_or_userMode`
  `cp0Usable_false_iff` `exceptionEntry_enters_kernel_mode` `exceptionEntry_keeps_um`
  `exception_from_user_mode_enters_kernel_mode` `eret_to_user_mode` `mtc0_status_enters_user_mode`
-/

set_option maxRecDepth 4000

/-- Bit-mask fact: setting the bits `m` and reading them back gives `m`. -/
theorem orMask_and_self (x m : W32) : (x ||| m) &&& m = m := by
  ext i hi; simp; intro h; exact Or.inr h

/-- Bit-mask fact: setting the bits `m` does not change the field `k` when `m` and `k` are
disjoint. -/
theorem or_and_disjoint (x m k : W32) (h : m &&& k = 0#32) : (x ||| m) &&& k = x &&& k := by
  rw [BitVec.and_or_distrib_right, h, BitVec.or_zero]

/-- **User Mode** is `Status.UM = 1`, `Status.EXL = 0`, `Status.ERL = 0` (MD00090 Vol III
Rev 6.02 §3.4, p.22, with `KSU = UM ‖ 0` since Supervisor Mode is not implemented, Table 9.47
p.195). -/
theorem userMode_iff (s : State) :
    userMode s = true ↔
      (s.cp0Status &&& statusUmMask ≠ 0#32 ∧ s.cp0Status &&& statusExlMask = 0#32 ∧
        s.cp0Status &&& statusErlMask = 0#32) := by
  unfold userMode kernelMode
  simp [and_assoc]

/-- The processor is always in exactly one of the two modes: Kernel Mode or User Mode (there is no
Supervisor or Debug Mode in this implementation). -/
theorem kernelMode_or_userMode (s : State) :
    (kernelMode s = true ∨ userMode s = true) ∧ ¬(kernelMode s = true ∧ userMode s = true) := by
  unfold userMode
  cases kernelMode s <;> simp

/-- **Coprocessor 0 is unusable exactly in User Mode with `Status.CU0 = 0`** (MD00090 Vol III
Rev 6.02 §3.5.3, p.23). -/
theorem cp0Usable_false_iff (s : State) :
    cp0Usable s = false ↔ (userMode s = true ∧ s.cp0Status &&& statusCu0Mask = 0#32) := by
  unfold cp0Usable userMode
  cases kernelMode s <;> simp

/-- **Exception entry always enters Kernel Mode**: it sets `Status.EXL` (MD00090 Vol III Rev 6.02
§6.2.3, p.86-88; §3.2, p.21: "The processor enters Kernel Mode ... as the result of an interrupt,
exception, or error"). So every exception handler runs in Kernel Mode, whatever mode the
exception was taken from. -/
theorem exceptionEntry_enters_kernel_mode (s : State) (code ce : W32) :
    kernelMode (exceptionEntry s code ce) = true := by
  unfold kernelMode exceptionEntry
  dsimp only
  rw [orMask_and_self]
  have h : statusExlMask ≠ 0#32 := by decide
  simp [h]

/-- **Exception entry leaves `Status.UM` unchanged**: an exception taken from User Mode leaves
`UM = 1` (the processor is in Kernel Mode because `EXL = 1`), so `eret`, which clears `EXL`,
returns to User Mode. -/
theorem exceptionEntry_keeps_um (s : State) (code ce : W32) :
    (exceptionEntry s code ce).cp0Status &&& statusUmMask = s.cp0Status &&& statusUmMask :=
  or_and_disjoint _ _ _ (by decide)

/-- **An exception taken from User Mode enters Kernel Mode, with `Status.UM` still 1 and
`Status.EXL = 1`.** -/
theorem exception_from_user_mode_enters_kernel_mode (s : State) (code ce : W32)
    (hu : userMode s = true) :
    kernelMode (exceptionEntry s code ce) = true ∧ userMode (exceptionEntry s code ce) = false ∧
      (exceptionEntry s code ce).cp0Status &&& statusUmMask ≠ 0#32 ∧
      (exceptionEntry s code ce).cp0Status &&& statusExlMask = statusExlMask := by
  have hk := exceptionEntry_enters_kernel_mode s code ce
  refine ⟨hk, by unfold userMode; rw [hk]; rfl, ?_, orMask_and_self _ _⟩
  rw [exceptionEntry_keeps_um]
  exact ((userMode_iff s).mp hu).1

/-- **`eret` returns to User Mode** when the handler it ends interrupted User Mode: if
`Status.ERL = 0`, `Status.EXL = 1` (so the processor is in Kernel Mode and coprocessor 0 is
usable) and `Status.UM = 1`, then `eret` goes to `EPC` with `EXL` cleared, and the processor is
in User Mode (MD00086 Vol II-A Rev 6.06, ERET, p.177: "else temp ← EPC; StatusEXL ← 0";
MD00090 Vol III Rev 6.02 §3.2, p.21: the processor leaves Kernel Mode "usually as the result of
an ERET instruction"). -/
theorem eret_to_user_mode (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none)
    (herl : s.cp0Status &&& statusErlMask = 0#32) (hexl : s.cp0Status &&& statusExlMask ≠ 0#32)
    (hum : s.cp0Status &&& statusUmMask ≠ 0#32) :
    (step s).pc = s.cp0Epc ∧ userMode (step s) = true := by
  have hcp0 : cp0Usable s = true := by
    unfold cp0Usable kernelMode; simp [hexl]
  rw [eret_spec_raw s w hfetch hdecode hpb hcp0]
  have herl' : (s.cp0Status &&& statusErlMask != 0#32) = false := by simp [herl]
  rw [herl', ite_of_neg Bool.false_ne_true]
  refine ⟨rfl, ?_⟩
  rw [userMode_iff]
  dsimp only [timerTick_cp0Status]
  refine ⟨?_, ?_, ?_⟩
  · rw [BitVec.and_assoc, show ~~~statusExlMask &&& statusUmMask = statusUmMask by decide]
    exact hum
  · rw [BitVec.and_assoc, show ~~~statusExlMask &&& statusExlMask = 0#32 by decide,
      BitVec.and_zero]
  · rw [BitVec.and_assoc, show ~~~statusExlMask &&& statusErlMask = statusErlMask by decide]
    exact herl

/-- **`mtc0` to `Status` can enter User Mode**: `UM` is writable (MD00090 Vol III Rev 6.02
Table 9.47, p.195, "R/W"), so from Kernel Mode writing a value with `UM = 1`, `EXL = 0`, `ERL = 0`
puts the processor in User Mode at the next instruction. (The usual way is to set `UM` and `EXL`
and then `eret`; `eret_to_user_mode`.) -/
theorem mtc0_status_enters_user_mode (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt 12#32 0#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true)
    (hum : readReg s (regIdxSpec rt) &&& statusUmMask ≠ 0#32)
    (hexl : readReg s (regIdxSpec rt) &&& statusExlMask = 0#32)
    (herl : readReg s (regIdxSpec rt) &&& statusErlMask = 0#32) :
    userMode (step s) = true := by
  rw [mtc0_spec_raw s w rt 12#32 0#32 hfetch hdecode hpb hcp0]
  show userMode (timerTick
    { s with cp0Status := readReg s (regIdxSpec rt) &&& statusWriteMask, pc := s.pc + 4#32 }) = true
  rw [userMode_iff]
  dsimp only [timerTick_cp0Status]
  refine ⟨?_, ?_, ?_⟩
  · rw [BitVec.and_assoc, show statusWriteMask &&& statusUmMask = statusUmMask by decide]
    exact hum
  · rw [BitVec.and_assoc, show statusWriteMask &&& statusExlMask = statusExlMask by decide]
    exact hexl
  · rw [BitVec.and_assoc, show statusWriteMask &&& statusErlMask = statusErlMask by decide]
    exact herl
