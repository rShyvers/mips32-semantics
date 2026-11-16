import Semantics.Refine.Fetch

/-!
# Refine.Cycle — the non-instruction paths of one instruction time (7D)

`Manual.InstructionTime` against `step`, path by path, for every path that is not the Operation of a
decoded instruction:

* the timer (`timerTick` against `Manual.TimerTick`): `timerTick_abs`;
* the interrupt check and the Interrupt exception (`interruptTaken`/`takeInterrupt` against
  `Manual.InterruptTaken` and the general exception processing with `ExcCode = Int`):
  `interruptTaken_abs`, `takeInterrupt_abs`;
* the lower power mode of `WAIT` (`standbyStep` against `Manual.LowPowerTime`): `standbyStep_abs`;
* instruction fetch (`readMemWord s s.pc` against `Manual.InstructionFetch`; a misaligned `PC` or a
  kernel address in User Mode is an Address Error): `fetch_run`, `fetchError_abs`;
* a word `decode` rejects (Reserved Instruction, Coprocessor Unusable by encoding space, and the
  `UnpredictableEncoding` oracle path): `undecodable_abs`.

The decoded-instruction path is `Refine.InstrRefines` (the per-instruction theorems, assembled in
`Refine/Step.lean`). None of these theorems needs an invariant of the state.
-/

namespace Refine

open Manual

/-! ## Timer -/

theorem countEnabled_abs (s : State) : countEnabled s = !CauseDC (abs s) := by
  rw [countEnabled, CauseDC, show causeDcMask = BitVec.twoPow 32 27 by decide,
    and_twoPow_eq _ 27 (by omega)]; rfl

/-- **The timer**: `timerTick` is `Manual.TimerTick` with the model's rate (`CountIncrement = 1`). -/
theorem timerTick_abs (s : State) : abs (timerTick s) = TimerTick modelImpl (abs s) := by
  simp only [timerTick, TimerTick, countEnabled_abs]
  cases CauseDC (abs s) <;> rfl

/-! ## Interrupt requests -/

theorem intCtlIPTI_model : IntCtlIPTI modelImpl = 7 := by decide

/-- `Cause` as read: the model's `causeValue` is the manual's `CauseRead`. -/
theorem causeValue_abs (s : State) : causeValue s = CauseRead modelImpl (abs s) := by
  simp only [causeValue, CauseRead, hwIntBits, intCtlIPTI_model]
  rfl

theorem shl8_eq_zero (b : BitVec 8) : (b.setWidth 32 <<< 8 = 0#32) ↔ b = 0#8 := by
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h'
    apply BitVec.eq_of_toNat_eq
    have := b.isLt
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    rw [Nat.shiftLeft_eq] at h'
    omega
  · intro h; subst h; rfl

theorem im_and (x y : W32) :
    x &&& y &&& statusImMask = (x.extractLsb' 8 8 &&& y.extractLsb' 8 8).setWidth 32 <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [statusImMask, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb']
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-- The model's interrupt requests are nonzero exactly when the manual's are. -/
theorem interruptRequests_abs (s : State) :
    (interruptRequests s != 0#32) = decide (InterruptRequests modelImpl (abs s) ≠ 0#8) := by
  rw [interruptRequests, im_and, causeValue_abs, InterruptRequests, StatusIM]
  rw [Bool.eq_iff_iff]; simp only [bne_iff_ne, ne_eq, decide_eq_true_eq, shl8_eq_zero]; rfl

theorem interruptsEnabled_abs (s : State) : interruptsEnabled s = InterruptsEnabled (abs s) := by
  simp only [interruptsEnabled, InterruptsEnabled, StatusIE, StatusEXL, StatusERL, bit, abs,
    show statusIeMask = BitVec.twoPow 32 0 by decide, show statusExlMask = BitVec.twoPow 32 1 by decide,
    show statusErlMask = BitVec.twoPow 32 2 by decide, and_twoPow_ne _ 0 (by omega),
    and_twoPow_eq _ 1 (by omega), and_twoPow_eq _ 2 (by omega)]

/-- **The interrupt check**: `interruptTaken` is `Manual.InterruptTaken`. -/
theorem interruptTaken_abs (s : State) : InterruptTaken modelImpl (abs s) = interruptTaken s := by
  rw [InterruptTaken, interruptTaken, interruptsEnabled_abs, interruptRequests_abs]

/-! ## The Interrupt exception -/

theorem iv_abs (s : State) : CauseIV (abs s) = !(s.cp0Cause &&& causeIvMask == 0#32) := by
  rw [show causeIvMask = BitVec.twoPow 32 23 by decide, and_twoPow_eq _ 23 (by omega)]
  simp [CauseIV, abs, bit]

theorem intCtlVS_model : IntCtlVS modelImpl = 0#5 := by decide

/-- The vector of the Interrupt exception, the manual's sum against the model's `interruptVector`
(with `Status.EXL = 0`, which holds whenever an interrupt is taken). -/
theorem intVector_eq (s : State) (hexl : StatusEXL (abs s) = false) :
    (vectorBase (abs s)).extractLsb' 30 2 ++
        ((vectorBase (abs s)).extractLsb' 0 30 +
          (vectorOffset modelImpl (abs s) .Interrupt).extractLsb' 0 30) = interruptVector s := by
  unfold interruptVector
  cases hiv : (s.cp0Cause &&& causeIvMask == 0#32)
  · have hiv' : CauseIV (abs s) = true := by rw [iv_abs, hiv]; rfl
    simp only [vectorOffset, hexl, hiv', intCtlVS_model, Bool.false_eq_true, ite_false,
      Bool.not_true, beq_self_eq_true, Bool.or_true, ite_true]
    unfold vectorBase
    rw [bev_abs]
    cases hb : (s.cp0Status &&& statusBevMask == 0#32)
    · simp; decide
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true, EBaseRead, fieldOnes_29_12,
        ebaseValue, ebaseWriteMask, ebaseFixedBits, interruptVectorOffset, abs]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [BitVec.add_eq_or_of_and_eq_zero]
      · simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_append,
          BitVec.getLsbD_extractLsb']
        rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega
      · apply BitVec.eq_of_getLsbD_eq
        intro j hj
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_extractLsb',
          BitVec.getLsbD_or, BitVec.getLsbD_zero]
        rcases j with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|j <;> simp <;> omega
  · have hiv' : CauseIV (abs s) = false := by rw [iv_abs, hiv]; rfl
    have hoff : vectorOffset modelImpl (abs s) .Interrupt = 0x180#32 := by
      simp [vectorOffset, hexl, hiv']
    rw [hoff, vector_eq]; simp

/-- **The Interrupt exception**: `takeInterrupt` is the general exception processing with
`ExcCode = Int`, and the processor leaves the lower power mode (`Manual.InstructionTime`, point 1). -/
theorem takeInterrupt_abs (s : State) (h : interruptTaken s = true) :
    abs (takeInterrupt s) =
      { GeneralExceptionProcessing modelImpl modelOracle .Interrupt (abs s) with LowPower := false } := by
  have hexl : StatusEXL (abs s) = false := by
    rw [← interruptTaken_abs] at h
    simp only [InterruptTaken, InterruptsEnabled, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1.2
  have hv := intVector_eq s hexl
  have hce := ce_eq (s := s) .Interrupt (fun u h => by cases h)
  have hexl' : StatusEXL (abs s) = (s.cp0Status &&& statusExlMask != 0#32) := exl_abs s
  have hm : (s.cp0Status &&& statusExlMask != 0#32) = false := by rw [← hexl', hexl]
  simp only [GeneralExceptionProcessing, AdditionalState, hv, hexl, Bool.false_eq_true, ite_false]
  rw [← cause_update, ← hce]
  simp only [takeInterrupt, exceptionEntry, hm, Bool.false_eq_true, ite_false]
  rfl

/-! ## Lower power mode -/

/-- **The lower power mode of `WAIT`**: `standbyStep` is `Manual.LowPowerTime` with the model's
`WaitRestartsOnNotEnabled = true`. -/
theorem standbyStep_abs (s : State) : abs (standbyStep s) = LowPowerTime modelImpl (abs s) := by
  unfold standbyStep LowPowerTime
  rw [interruptRequests_abs]
  by_cases h : InterruptRequests modelImpl (abs s) = 0#8
  · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false, Bool.and_false]
  · simp only [h, ne_eq, not_false_eq_true, decide_true, ite_true, Bool.and_true,
      show modelImpl.WaitRestartsOnNotEnabled = true from rfl]
    rfl

/-! ## Instruction fetch -/

/-- `readMemWord` of a misaligned address is `none`. -/
theorem readMemWord_misaligned (s : State) (va : W32) (h : ¬ va.toNat % 4 = 0) :
    readMemWord s va = none := by
  unfold readMemWord; simp [h]

/-- **Instruction fetch** (`Manual.InstructionFetch`, under the model's choices) against the model's
`readMemWord s s.pc`: the fetched word, or an Address Error (AdEL) with the `PC`, the state
unchanged either way. -/
theorem fetch_run (s : State) :
    InstructionFetch.run modelCtx { arch := abs s } =
      match readMemWord s s.pc with
      | none => (.signal (.AddressErrorLoad s.pc), { arch := abs s })
      | some w => (.ok w, { arch := abs s }) := by
  by_cases ha : s.pc.toNat % 4 = 0
  · have hb : (bits s.pc 1 0 != 0#2) = false := by rw [misaligned_eq]; simp [ha]
    rw [readMemWord_eq s s.pc ha]
    have ht := addrTrans_run s s.pc .INSTRUCTION .LOAD modelCtx { arch := abs s } rfl
    simp only [Pseudo.run, InstructionFetch, bind, PC, memory_address, abs_PC, hb,
      Bool.false_eq_true, ite_false]
    rw [ht]
    cases translate s s.pc <;> simp [loadMemory_model]
  · have hb : (bits s.pc 1 0 != 0#2) = true := by rw [misaligned_eq]; simp [ha]
    rw [readMemWord_misaligned s s.pc ha]
    simp only [Pseudo.run, InstructionFetch, bind, PC, memory_address, abs_PC, hb, ite_true]
    rfl

/-- **The Address Error of a failed fetch**: the general exception processing of AdEL with
`BadVAddr = PC` is the model's `takeAddressException`. -/
theorem fetchError_abs (s : State) :
    GeneralExceptionProcessing modelImpl modelOracle (.AddressErrorLoad s.pc) (abs s) =
      abs (takeAddressException s excCodeAdEL s.pc) := by
  rw [gep_eq s _ (by intro h; cases h) (by intro u h; cases h)]
  rfl

/-! ## Words that do not decode -/

theorem opcode_eq (w : W32) : opcode w = opcodeOf w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [opcode, opcodeOf, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem funct_eq (w : W32) : w &&& 0x3F#32 = functOf w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [functOf, BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem opcode_toNat (w : W32) : fldOf w 31 26 = (opcode w).toNat := by
  simp only [fldOf, opcode, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight]
  have := w.isLt; rw [Nat.shiftRight_eq_div_pow]; omega

theorem isCop0Word_eq (w : W32) : isCop0Word w = InCop0Space w := by
  rw [isCop0Word, InCop0Space, opcode_eq, funct_eq]

theorem isCop2Word_eq (w : W32) : isCop2Word w = InCop2Space w := by
  rw [isCop2Word, InCop2Space, opcode_eq]

theorem op_ne_of_decode_none (w : W32) (hd : decode w = none) (n : Nat)
    (hn : n = 0x31 ∨ n = 0x39 ∨ n = 0x35 ∨ n = 0x3D) : (opcodeOf w == BitVec.ofNat 32 n) = false := by
  rw [beq_eq_false_iff_ne]; intro h
  have ht : (opcodeOf w).toNat = n := by rw [h]; simp; omega
  rcases hn with rfl | rfl | rfl | rfl <;> simp [decode, decodeFor, decodePrimary, ht] at hd

/-- For a word `decode` rejects, the COP1 encoding space is the model's `isCop1Word` (the words of
opcodes `LWC1`, `SWC1`, `LDC1`, `SDC1` all decode). -/
theorem isCop1Word_eq (w : W32) (hd : decode w = none) : isCop1Word w = InCop1Space w := by
  rw [isCop1Word, InCop1Space, opcode_eq,
    op_ne_of_decode_none w hd 0x31 (by omega), op_ne_of_decode_none w hd 0x39 (by omega),
    op_ne_of_decode_none w hd 0x35 (by omega), op_ne_of_decode_none w hd 0x3D (by omega)]
  simp only [Bool.or_false]

theorem cop01_disjoint (w : W32) : (InCop0Space w && InCop1Space w) = false := by
  simp only [InCop0Space, InCop1Space]
  cases h : opcode w == 0x10#32 <;> cases h' : opcode w == 0x1F#32 <;> simp_all

/-- An UNPREDICTABLE encoding is in no coprocessor 2 space. -/
theorem cop2_of_unpredictable (w : W32) (hu : UnpredictableEncoding w = true) :
    InCop2Space w = false := by
  rw [Bool.eq_false_iff]; intro h
  simp only [InCop2Space, beq_iff_eq] at h
  have hf := opcode_toNat w
  rw [h] at hf; simp only [BitVec.toNat_ofNat] at hf; simp [UnpredictableEncoding, hf] at hu

/-- **A word `decode` rejects** (`Manual.FetchExecute`, the `dec w = none` arm, under the model's
choices) against the model's `execute`: Coprocessor Unusable for the space of an unusable coprocessor
(COP0, COP1; COP2 always), else Reserved Instruction; an `UnpredictableEncoding` word takes the
model's oracle choice (Reserved Instruction) after the same coprocessor checks. -/
theorem undecodable_abs (s : State) (w : W32) (hd : decode w = none) :
    (if UnpredictableEncoding w then Unpredictable modelCtx w (abs s)
      else GeneralExceptionProcessing modelImpl modelOracle (Undecodable w (abs s)) (abs s)) =
    abs (if isCop0Word w && !cp0Usable s then takeCop0Unusable s
      else if isCop1Word w && !cu1Enabled s then takeCoprocessorUnusable s
      else if isCop2Word w then exceptionEntry s excCodeCpU 2#32
      else takeException s excCodeRI) := by
  have g0 : GeneralExceptionProcessing modelImpl modelOracle (.CoprocessorUnusable 0) (abs s) =
      abs (takeCop0Unusable s) := by
    rw [gep_eq s _ (by intro h; cases h) (by intro u h; cases h; omega)]; rfl
  have g1 : GeneralExceptionProcessing modelImpl modelOracle (.CoprocessorUnusable 1) (abs s) =
      abs (takeCoprocessorUnusable s) := by
    rw [gep_eq s _ (by intro h; cases h) (by intro u h; cases h; omega)]; rfl
  have g2 : GeneralExceptionProcessing modelImpl modelOracle (.CoprocessorUnusable 2) (abs s) =
      abs (exceptionEntry s excCodeCpU 2#32) := by
    rw [gep_eq s _ (by intro h; cases h) (by intro u h; cases h; omega)]; rfl
  have gr : GeneralExceptionProcessing modelImpl modelOracle .ReservedInstruction (abs s) =
      abs (takeException s excCodeRI) := gep_take s _ rfl _ (by decide)
  have hdis := cop01_disjoint w
  rw [isCop0Word_eq, isCop1Word_eq w hd, isCop2Word_eq, ← cu1_abs, ← cp0usable_abs]
  simp only [Unpredictable, Undecodable, modelCtx]
  cases hu : UnpredictableEncoding w
  · cases h0 : InCop0Space w <;> cases h1 : InCop1Space w <;> cases h2 : InCop2Space w <;>
      cases StatusCU1 (abs s) <;> cases CP0Usable (abs s) <;> simp_all
  · have h2 := cop2_of_unpredictable w hu
    cases h0 : InCop0Space w <;> cases h1 : InCop1Space w <;>
      cases StatusCU1 (abs s) <;> cases CP0Usable (abs s) <;> simp_all [modelOracle]

end Refine
