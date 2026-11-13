import Semantics.Specs.Mode
import Semantics.Specs.Fixtures

/-!
# Reset — the Reset exception, the reset state, and the hosted boot convention

`resetException s` (`Step.lean`) is the Reset exception of MD00090 Vol III Rev 6.02 §6.2.5
(p.89-90) taken from `s`; `resetState` is `resetException powerOnState`. The hosted environment's
start state is the reset state followed by a named boot convention (`Env.lean`:
`hostedStart = bootConvention textBase resetState`), and that is the old `initialState textBase`.

## Theorems in this file (6)

  `resetException_spec` `resetException_keeps` `resetState_spec` `hostedStart_is_reset_then_boot`
  `bootConvention_spec` `load_is_reset_then_boot`
-/

set_option maxRecDepth 4000

/-- **What the Reset exception defines** (MD00090 Vol III Rev 6.02 §6.2.5, p.89-90), from any
state `s`: `PC ← 0xBFC0_0000`; `Status.BEV ← 1`, `Status.ERL ← 1` (so the processor is in Kernel
Mode, §3.2 p.21, and the bootstrap exception vector `0xBFC0_0380` is in use); `Cause.DC ← 0`;
`EBase` reads `0x8000_0000` (`EBaseExceptionBase ← 0`); `Config` is its configuration state with
`K0 = 2` (`0x8000_8402`); `ErrorEPC ←` the restart PC (the branch, if `s` was in a delay slot);
no branch is pending. `Status.RP/TS/SR/NMI ← 0` hold because those bits are not implemented and
read 0. -/
theorem resetException_spec (s : State) :
    (resetException s).pc = 0xBFC00000#32 ∧
    (resetException s).cp0Status &&& statusBevMask = statusBevMask ∧
    (resetException s).cp0Status &&& statusErlMask = statusErlMask ∧
    (resetException s).cp0Cause &&& causeDcMask = 0#32 ∧
    ebaseValue (resetException s) = 0x80000000#32 ∧
    configValue (resetException s) = 0x80008402#32 ∧
    (resetException s).cp0ErrorEpc = (if s.pendingBranch.isSome then s.pc - 4#32 else s.pc) ∧
    (resetException s).pendingBranch = none ∧
    kernelMode (resetException s) = true ∧
    exceptionVector (resetException s) = 0xBFC00380#32 := by
  have hbev : (s.cp0Status ||| statusBevMask ||| statusErlMask) &&& statusBevMask = statusBevMask := by
    rw [or_and_disjoint _ _ _ (by decide), orMask_and_self]
  have herl : (s.cp0Status ||| statusBevMask ||| statusErlMask) &&& statusErlMask = statusErlMask :=
    orMask_and_self _ _
  refine ⟨rfl, hbev, herl, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · show s.cp0Cause &&& ~~~causeDcMask &&& causeDcMask = 0#32
    rw [BitVec.and_assoc, show ~~~causeDcMask &&& causeDcMask = 0#32 by decide, BitVec.and_zero]
  · show (ebaseFixedBits &&& ebaseWriteMask) ||| ebaseFixedBits = _
    decide
  · show 0x80008400#32 ||| (2#3).setWidth 32 = _
    decide
  · unfold kernelMode
    show (_ || _ || (s.cp0Status ||| statusBevMask ||| statusErlMask) &&& statusErlMask != 0#32) = true
    rw [herl]
    have h : statusErlMask ≠ 0#32 := by decide
    simp [h]
  · unfold exceptionVector
    show (if (s.cp0Status ||| statusBevMask ||| statusErlMask) &&& statusBevMask == 0#32 then _
      else exceptionVectorBevAddr) = _
    rw [hbev]
    rfl

/-- **What the Reset exception leaves alone**: every register whose reset state the manual
leaves undefined keeps its value (a pin; any value is legal): the GPRs, `HI`/`LO`, the FPRs,
`FCSR`, memory, `EPC`, `BadVAddr`, and every `Status` bit other than `BEV` and `ERL`. -/
theorem resetException_keeps (s : State) :
    (resetException s).regs = s.regs ∧ (resetException s).hi = s.hi ∧
    (resetException s).lo = s.lo ∧ (resetException s).fpRegs = s.fpRegs ∧
    (resetException s).fcsr = s.fcsr ∧ (resetException s).mem = s.mem ∧
    (resetException s).cp0Epc = s.cp0Epc ∧ (resetException s).cp0BadVAddr = s.cp0BadVAddr ∧
    (resetException s).cp0Status &&& ~~~(statusBevMask ||| statusErlMask) =
      s.cp0Status &&& ~~~(statusBevMask ||| statusErlMask) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  show (s.cp0Status ||| statusBevMask ||| statusErlMask) &&& ~~~(statusBevMask ||| statusErlMask) = _
  rw [BitVec.or_assoc, or_and_disjoint _ _ _ (by decide)]

/-- **The state after a cold reset** (`resetState = resetException powerOnState`): `pc =
0xBFC0_0000`, `Status = 0x0040_0004` (`BEV = ERL = 1`, every other bit 0: Kernel Mode, `CU0 =
CU1 = 0`), `Cause = 0`, `EPC = BadVAddr = ErrorEPC = 0`, `EBase` reads `0x8000_0000`, `Config`
reads `0x8000_8402` (`K0 = 2`), the general exception vector is the bootstrap one
(`0xBFC0_0380`), no branch is pending, `LLbit` clear, and every GPR, `HI`, `LO`, FPR and `FCSR`
is 0 (pins of undefined reset values, `powerOnState`). -/
theorem resetState_spec :
    resetState.pc = 0xBFC00000#32 ∧ resetState.cp0Status = 0x00400004#32 ∧
    resetState.cp0Cause = 0#32 ∧ resetState.cp0Epc = 0#32 ∧ resetState.cp0BadVAddr = 0#32 ∧
    resetState.cp0ErrorEpc = 0#32 ∧ ebaseValue resetState = 0x80000000#32 ∧
    configValue resetState = 0x80008402#32 ∧ kernelMode resetState = true ∧
    exceptionVector resetState = 0xBFC00380#32 ∧ resetState.pendingBranch = none ∧
    resetState.llBit = false ∧ resetState.regs = Array.replicate 32 0#32 ∧
    resetState.hi = 0#32 ∧ resetState.lo = 0#32 ∧
    resetState.fpRegs = Array.replicate 32 0#32 ∧ resetState.fcsr = 0#32 := by
  decide

/-- **The boot convention** (`Env.lean`): the program starts at `entry` in Kernel Mode with
`Status = CU1` only (`BEV = ERL = EXL = UM = 0`), `$sp = spInit`, no branch pending; nothing else
changes. -/
theorem bootConvention_spec (entry : W32) (s : State) :
    (bootConvention entry s).pc = entry ∧ (bootConvention entry s).cp0Status = 0x20000000#32 ∧
    kernelMode (bootConvention entry s) = true ∧
    readReg (bootConvention entry s) 29 = readReg (writeReg s 29 spInit) 29 ∧
    (bootConvention entry s).pendingBranch = none ∧
    (bootConvention entry s).cp0Cause = s.cp0Cause ∧ (bootConvention entry s).cp0Epc = s.cp0Epc ∧
    (bootConvention entry s).cp0ErrorEpc = s.cp0ErrorEpc ∧
    (bootConvention entry s).cp0EBase = s.cp0EBase ∧ (bootConvention entry s).mem = s.mem ∧
    (bootConvention entry s).fcsr = s.fcsr ∧ (bootConvention entry s).fpRegs = s.fpRegs := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold kernelMode
    show (statusCu1Mask &&& statusUmMask == 0#32 || statusCu1Mask &&& statusExlMask != 0#32 ||
      statusCu1Mask &&& statusErlMask != 0#32) = true
    decide
  all_goals simp [bootConvention, writeReg]

/-- **The hosted start state is the reset state followed by the boot convention**, and it is the
state the hosted environment always used (`initialState textBase`: `pc = 0x0040_0000`,
`$sp = 0x7FFF_EFFC`, `Status = CU1`, everything else as after reset). The machine starts at
reset; what happens between reset and the program's first instruction is the environment's
boot convention, outside the architecture. -/
theorem hostedStart_is_reset_then_boot :
    hostedStart = bootConvention textBase resetState ∧ hostedStart = initialState textBase :=
  ⟨rfl, rfl⟩

/-- **The loader** writes the image into the boot-convention state reached from reset. -/
theorem load_is_reset_then_boot (p : Program) :
    load p = loadImage p (bootConvention textBase resetState) := rfl

/-! ### Satisfiable examples -/

-- A reset taken in a delay slot records the branch (at `pc - 4`) in ErrorEPC.
#guard (resetException { (initialState 0x400008#32) with pendingBranch := some 0x400100#32 }).cp0ErrorEpc
  == 0x400004#32
-- A reset from User Mode with CU0/CU1/UM/IE set keeps those bits (undefined at reset) but is in
-- Kernel Mode (ERL = 1) at the reset vector.
#guard (let r := resetException { (initialState textBase) with cp0Status := 0x30000011#32 }
        r.cp0Status == 0x30400015#32 && kernelMode r && r.pc == 0xbfc00000#32)
-- From the reset state, `eret` (ERL = 1) jumps to ErrorEPC and clears ERL (what a boot ROM may use
-- to leave the reset state).
#guard (let s := stepIn (prog1Spec .eret) { resetState with pc := textBase, cp0ErrorEpc := 0x400100#32 }
        s.pc == 0x400100#32 && s.cp0Status == statusBevMask)
