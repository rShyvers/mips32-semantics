import Semantics.Word
import Semantics.Types
import Semantics.State
import Semantics.Instruction
import Semantics.Step
import Semantics.Specs.DecodeSpec
import Lean.Elab.Tactic

/-!
# StepSpec — a reviewable specification for `step`

This file is meant to be **read**: every theorem states a plain-English
property of the simulator and cites the `docs/spec/INSTRUCTION-REF.md`
section it encodes.

## How to read the statements

Each per-instruction theorem is an equation `step p s = …` whose right-hand
side is written out in terms of the state primitives (`readReg`, `writeReg`,
`readMemWord`, …) and `Step.lean`'s small helpers. The names ending in
`Spec` (`regIdxSpec`, `addOverflowsSpec`, …) are **abbreviations for the
real `Step.lean` definitions** — not copies — kept so statements read the
same way throughout; there is exactly one definition of each helper.

Hypotheses of the form `fetchWord p s.pc = some w` / `decode w = some instr`
stand for "the next instruction the simulator will run is `instr`".
`hpb : s.pendingBranch = none` restricts a theorem to an instruction that is
*not* in a branch delay slot; `delay_slot_commits_target` (Group 0) lifts
any such equation to the delay-slot case, and `exceptionEntry_*` describe
exception entry in both cases.

Exceptions (overflow, address error, reserved instruction, syscall,
breakpoint, trap) appear on right-hand sides as `takeException s code` /
`takeAddressException s code addr`; Group 0 states exactly what those do.

Every theorem in this file is fully proved.
-/

set_option maxRecDepth 4000

/-- Spec-side name for `Step.lean`'s `regIdx` — the same definition, not a copy. -/
abbrev regIdxSpec := regIdx

/-- Spec-side name for `Step.lean`'s `addOverflows` — the same definition, not a copy. -/
abbrev addOverflowsSpec := addOverflows

/-- Spec-side name for `Step.lean`'s `subOverflows` — the same definition, not a copy. -/
abbrev subOverflowsSpec := subOverflows

/-- Spec-side name for `Step.lean`'s `isBranchLike` — the same definition, not a copy. -/
abbrev isBranchLikeSpec := isBranchLike

/-- Spec-side name for `Step.lean`'s `zeroExtByte` — the same definition, not a copy. -/
abbrev zeroExtByteSpec := zeroExtByte

/-- Spec-side name for `Step.lean`'s `setByteSlot` — the same definition, not a copy. -/
abbrev setByteSlotSpec := setByteSlot

/-- Spec-side name for `Step.lean`'s `getByteSlot` — the same definition, not a copy. -/
abbrev getByteSlotSpec := getByteSlot


/-- Spec-side name for `Step.lean`'s `countLeadingZerosFrom` — the same definition, not a copy. -/
abbrev countLeadingZerosFromSpec := countLeadingZerosFrom

/-- Spec-side name for `Step.lean`'s `countLeadingZeros` — the same definition, not a copy. -/
abbrev countLeadingZerosSpec := countLeadingZeros

/-- Spec-side name for `Step.lean`'s `countLeadingOnes` — the same definition, not a copy. -/
abbrev countLeadingOnesSpec := countLeadingOnes

/-- Spec-side name for `Step.lean`'s `signExtLowByte` — the same definition, not a copy. -/
abbrev signExtLowByteSpec := signExtLowByte

/-- Spec-side name for `Step.lean`'s `lowBitsMask` — the same definition, not a copy. -/
abbrev lowBitsMaskSpec := lowBitsMask


/-- `if c then t else e = t` when `c` holds. -/
theorem ite_of_pos {c : Prop} [Decidable c] {α : Sort _} {t e : α} (h : c) :
    (if c then t else e) = t := by simp [h]

/-- `if c then t else e = e` when `c` fails. -/
theorem ite_of_neg {c : Prop} [Decidable c] {α : Sort _} {t e : α} (h : ¬ c) :
    (if c then t else e) = e := by simp [h]

/-! ## Group 0 — exception entry, delay slots, fetch and decode

These are the general facts every per-instruction theorem below leans on.
None of them assumes `s.pendingBranch = none`. -/

/-! ### Exception entry (MD00090 "General Exception Processing")

`takeException s code` is `StepResult.next (exceptionEntry s code)`;
`takeAddressException s code addr` additionally sets `BadVAddr := addr`
first. The theorems below say what `exceptionEntry` does in each of the
cases `Status.EXL = 0/1` × in a delay slot / not, and with `Status.BEV`. -/

/-- **What exception entry always does**, whatever `EXL`, the delay-slot
status and the coprocessor number `ce`: `PC ←` the general vector (`EBase`'s
base with offset `0x180` — `0x80000180` at reset — or `0xBFC00380` when
`Status.BEV = 1`); `Status.EXL ← 1` (no other `Status` bit changes); **the
pending branch is abandoned**; **`LLbit ← 0`** (MD00086 Rev 6.06 "SC",
programming notes: "Exceptions between the LL and SC cause SC to fail");
and nothing else outside `EPC`/`Cause` is touched — no general register,
`hi`/`lo`, memory, output, FP register, `FCSR`, `BadVAddr`, `ErrorEPC`,
`EBase` or the LL address. -/
theorem exceptionEntry_always (s : State) (code ce : W32) :
    (exceptionEntry s code ce).pc =
        (if s.cp0Status &&& statusBevMask == 0#32 then
          ((s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32) ||| 0x180#32
         else 0xBFC00380#32) ∧
      (exceptionEntry s code ce).cp0Status = s.cp0Status ||| statusExlMask ∧
      (exceptionEntry s code ce).pendingBranch = none ∧
      (exceptionEntry s code ce).regs = s.regs ∧
      (exceptionEntry s code ce).hi = s.hi ∧ (exceptionEntry s code ce).lo = s.lo ∧
      (exceptionEntry s code ce).mem = s.mem ∧ (exceptionEntry s code ce).out = s.out ∧
      (exceptionEntry s code ce).fpRegs = s.fpRegs ∧
      (exceptionEntry s code ce).fcsr = s.fcsr ∧
      (exceptionEntry s code ce).llBit = false ∧
      (exceptionEntry s code ce).cp0BadVAddr = s.cp0BadVAddr ∧
      (exceptionEntry s code ce).cp0ErrorEpc = s.cp0ErrorEpc ∧
      (exceptionEntry s code ce).cp0EBase = s.cp0EBase ∧
      (exceptionEntry s code ce).llAddr = s.llAddr :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- With `EBase` at its reset value the general vector is the classic
`0x80000180`. -/
theorem exceptionVector_reset (s : State) (hbev : s.cp0Status &&& statusBevMask = 0#32)
    (heb : s.cp0EBase = 0x80000000#32) : exceptionVector s = 0x80000180#32 := by
  simp [exceptionVector, ebaseValue, hbev, heb]; decide

/-- **Every exception clears `LLbit`**, so an `sc` after any exception
fails even if the handler returns without `eret` (MD00086 Rev 6.06 "SC",
programming notes, p. 350: "Exceptions between the LL and SC cause SC to
fail"). Stated for both exception forms `step` uses. -/
theorem exception_clears_llBit (s s' : State) (code addr : W32)
    (h : takeException s code = StepResult.next s' ∨
      takeAddressException s code addr = StepResult.next s') :
    s'.llBit = false := by
  rcases h with h | h <;> (injection h with h; rw [← h]; rfl)

/-- **`EXL = 0`, not in a delay slot**: `EPC ← PC` (the faulting
instruction), `Cause.BD ← 0`, `Cause.ExcCode ← code`, `Cause.CE ← ce`. -/
theorem exceptionEntry_exl0_not_in_delay_slot (s : State) (code ce : W32)
    (hexl : s.cp0Status &&& statusExlMask = 0#32) (hpb : s.pendingBranch = none) :
    (exceptionEntry s code ce).cp0Epc = s.pc ∧
      (exceptionEntry s code ce).cp0Cause =
        (((s.cp0Cause &&& ~~~causeBdMask) &&& ~~~(causeExcCodeMask ||| causeCeMask))
          ||| ((code <<< 2) &&& causeExcCodeMask)) ||| ((ce <<< 28) &&& causeCeMask) := by
  simp [exceptionEntry, hexl, hpb]

/-- **`EXL = 0`, in a branch delay slot** (after a taken *or* not-taken
branch — `pendingBranch = some t` either way): `EPC ← PC − 4` (the branch),
`Cause.BD ← 1`, `Cause.ExcCode ← code`, `Cause.CE ← ce`. -/
theorem exceptionEntry_exl0_in_delay_slot (s : State) (code ce t : W32)
    (hexl : s.cp0Status &&& statusExlMask = 0#32) (hpb : s.pendingBranch = some t) :
    (exceptionEntry s code ce).cp0Epc = s.pc - 4#32 ∧
      (exceptionEntry s code ce).cp0Cause =
        (((s.cp0Cause ||| causeBdMask) &&& ~~~(causeExcCodeMask ||| causeCeMask))
          ||| ((code <<< 2) &&& causeExcCodeMask)) ||| ((ce <<< 28) &&& causeCeMask) := by
  simp [exceptionEntry, hexl, hpb]

/-- **`EXL = 1`** (an exception inside an exception handler), in a delay
slot or not: `EPC` is left unchanged and so is `Cause.BD`; only
`Cause.ExcCode ← code` and `Cause.CE ← ce`. -/
theorem exceptionEntry_exl1 (s : State) (code ce : W32)
    (hexl : s.cp0Status &&& statusExlMask ≠ 0#32) :
    (exceptionEntry s code ce).cp0Epc = s.cp0Epc ∧
      (exceptionEntry s code ce).cp0Cause =
        ((s.cp0Cause &&& ~~~(causeExcCodeMask ||| causeCeMask))
          ||| ((code <<< 2) &&& causeExcCodeMask)) ||| ((ce <<< 28) &&& causeCeMask) := by
  simp [exceptionEntry, hexl]

/-- Bit-mask fact: writing field `m` of `x` from `y` gives back `y`'s field. -/
theorem mask_field_written (x y m : W32) : ((x &&& ~~~m) ||| (y &&& m)) &&& m = y &&& m := by
  ext i hi; simp; grind

/-- Bit-mask fact: writing field `m` of `x` leaves any disjoint field `k`
of `x` alone. -/
theorem mask_field_kept (x y m k : W32) (h : k &&& m = 0#32) :
    ((x &&& ~~~m) ||| (y &&& m)) &&& k = x &&& k := by
  have hb : ∀ i (hi : i < 32), (k[i] && m[i]) = false := by
    intro i hi; have := congrArg (·[i]) h; simpa using this
  ext i hi; have := hb i hi; simp at this ⊢; grind

/-- Bit-mask fact for the two fields exception entry writes (`m` from `y`,
`c` from `z`, disjoint): reading `m` back gives `y`'s field. -/
theorem two_fields_first (x y z m c : W32) (h : m &&& c = 0#32) :
    (((x &&& ~~~(m ||| c)) ||| (y &&& m)) ||| (z &&& c)) &&& m = y &&& m := by
  have hb : ∀ i (hi : i < 32), (m[i] && c[i]) = false := by
    intro i hi; have := congrArg (·[i]) h; simpa using this
  ext i hi; have := hb i hi; simp at this ⊢; grind

/-- … reading `c` back gives `z`'s field. -/
theorem two_fields_second (x y z m c : W32) (h : m &&& c = 0#32) :
    (((x &&& ~~~(m ||| c)) ||| (y &&& m)) ||| (z &&& c)) &&& c = z &&& c := by
  have hb : ∀ i (hi : i < 32), (m[i] && c[i]) = false := by
    intro i hi; have := congrArg (·[i]) h; simpa using this
  ext i hi; have := hb i hi; simp at this ⊢; grind

/-- … and any field `k` disjoint from both is `x`'s. -/
theorem two_fields_kept (x y z m c k : W32) (hm : k &&& m = 0#32) (hc : k &&& c = 0#32) :
    (((x &&& ~~~(m ||| c)) ||| (y &&& m)) ||| (z &&& c)) &&& k = x &&& k := by
  have hb : ∀ i (hi : i < 32), (k[i] && m[i]) = false := by
    intro i hi; have := congrArg (·[i]) hm; simpa using this
  have hb' : ∀ i (hi : i < 32), (k[i] && c[i]) = false := by
    intro i hi; have := congrArg (·[i]) hc; simpa using this
  ext i hi; have := hb i hi; have := hb' i hi; simp at * ; grind

theorem bit_of_31 : ∀ i : Fin 32, (31#32).getLsbD i.val = decide (i.val < 5) := by decide
theorem bit_of_124 : ∀ i : Fin 32, (124#32).getLsbD (2 + i.val) = decide (i.val < 5) := by decide

/-- Placing a value in bits 6..2 and reading those bits back gives its low
five bits. -/
theorem excCode_field_roundtrip (c : W32) : ((c <<< 2) &&& 124#32) >>> 2 = c &&& 31#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h31 := bit_of_31 ⟨i, hi⟩
  have h124 := bit_of_124 ⟨i, hi⟩
  simp only at h31 h124
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, h31, h124]
  by_cases h5 : i < 5
  · have : 2 + i < 32 := by omega
    have h2 : ¬ (2 + i < 2) := by omega
    simp [h5, this, h2]
  · simp [h5]

/-- **After exception entry, `Cause.ExcCode` (bits 6..2) is `code`** (its
low five bits), in every case. -/
theorem exceptionEntry_excCode (s : State) (code ce : W32) :
    causeExcCode (exceptionEntry s code ce) = code &&& 31#32 := by
  show ((_ &&& ~~~(causeExcCodeMask ||| causeCeMask) ||| (code <<< 2) &&& causeExcCodeMask
    ||| (ce <<< 28) &&& causeCeMask) &&& causeExcCodeMask) >>> 2 = _
  rw [two_fields_first _ _ _ _ _ (by decide)]
  exact excCode_field_roundtrip code

/-- **After exception entry, `Cause.CE` (bits 29..28) is `ce`**: the
coprocessor unit number for Coprocessor Unusable, `0` for every other
exception the model raises. -/
theorem exceptionEntry_ce (s : State) (code ce : W32) :
    (exceptionEntry s code ce).cp0Cause &&& causeCeMask = (ce <<< 28) &&& causeCeMask := by
  show (_ &&& ~~~(causeExcCodeMask ||| causeCeMask) ||| (code <<< 2) &&& causeExcCodeMask
    ||| (ce <<< 28) &&& causeCeMask) &&& causeCeMask = _
  exact two_fields_second _ _ _ _ _ (by decide)

/-- **Exception entry leaves every `Cause` bit other than `ExcCode`, `CE`
and `BD` intact** — `IV`, `DC`, the `IP` bits, everything: for any mask `k`
disjoint from the three fields, the `k` bits of `Cause` are unchanged. -/
theorem exceptionEntry_cause_other_bits (s : State) (code ce k : W32)
    (hk : k &&& causeExcCodeMask = 0#32) (hce : k &&& causeCeMask = 0#32)
    (hbd : k &&& causeBdMask = 0#32) :
    (exceptionEntry s code ce).cp0Cause &&& k = s.cp0Cause &&& k := by
  have h1 : ∀ x : W32, (x ||| causeBdMask) &&& k = x &&& k := by
    intro x
    have hb : ∀ i (hi : i < 32), (k[i] && causeBdMask[i]) = false := by
      intro i hi; have := congrArg (·[i]) hbd; simpa using this
    ext i hi; have := hb i hi; simp at this ⊢; grind
  have h2 : ∀ x : W32, (x &&& ~~~causeBdMask) &&& k = x &&& k := by
    intro x
    have hb : ∀ i (hi : i < 32), (k[i] && causeBdMask[i]) = false := by
      intro i hi; have := congrArg (·[i]) hbd; simpa using this
    ext i hi; have := hb i hi; simp at this ⊢; grind
  show (_ &&& ~~~(causeExcCodeMask ||| causeCeMask) ||| (code <<< 2) &&& causeExcCodeMask
    ||| (ce <<< 28) &&& causeCeMask) &&& k = _
  rw [two_fields_kept _ _ _ _ _ _ hk hce]
  split
  · rfl
  · split
    · exact h1 _
    · exact h2 _

-- `Cause = 0x00800300` (IV and IP1..0 set) becomes `0x00800324` on `break`.
example : (exceptionEntry { (initialState textBase) with cp0Cause := 0x00800300#32 } excCodeBp).cp0Cause
    = 0x00800324#32 := by decide

/-! ### Fetch and decode failures -/

/-- **A misaligned `pc` raises Address Error (AdEL)** with `BadVAddr = pc`
(and `EPC = pc`, by `exceptionEntry_*`). -/
theorem step_misaligned_pc (p : Program) (s : State) (h : s.pc.toNat % 4 ≠ 0) :
    step p s = takeAddressException s excCodeAdEL s.pc := by
  unfold step
  rw [show fetchWord p s.pc = none by unfold fetchWord; rw [ite_of_pos h]]
  dsimp only
  rw [ite_of_pos h]

/-- **A word that does not decode** raises Reserved Instruction (ExcCode
10) — unless it lies in a coprocessor's encoding space and that coprocessor
is unusable, in which case Coprocessor Unusable takes precedence (MD00090
Vol III Rev 6.02 §6.2.21, p.99): coprocessor 1 (`isCop1Word`) when
`Status.CU1 = 0`, with `Cause.CE = 1`; coprocessor 2 (`isCop2Word`), which
the model does not have, always, with `Cause.CE = 2`. -/
theorem step_undecodable (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = none) :
    step p s =
      if isCop1Word w && !cu1Enabled s then StepResult.next (exceptionEntry s excCodeCpU 1#32)
      else if isCop2Word w then StepResult.next (exceptionEntry s excCodeCpU 2#32)
      else takeException s excCodeRI := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  rfl

/-- **A word that does not decode and is in no coprocessor's encoding space
raises Reserved Instruction** (ExcCode 10). -/
theorem step_reserved_instruction (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = none)
    (hc1 : isCop1Word w = false) (hc2 : isCop2Word w = false) :
    step p s = takeException s excCodeRI := by
  rw [step_undecodable p s w hfetch hdecode, hc1, hc2]
  rfl

/-- **A reserved coprocessor-1 encoding with `Status.CU1 = 0` raises
Coprocessor Unusable**, not Reserved Instruction. -/
theorem step_reserved_cop1_unusable (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = none)
    (hc1 : isCop1Word w = true) (hcu : cu1Enabled s = false) :
    step p s = takeCoprocessorUnusable s := by
  rw [step_undecodable p s w hfetch hdecode, hc1, hcu]
  rfl

/-- **No handler installed** (model-level convention): if an exception has
been taken (`Status.EXL = 1`) and `pc` is the exception vector but the
program holds no instruction there, `step` halts with
`unhandledException`, reporting `Cause.ExcCode`, `EPC` and `BadVAddr`. -/
theorem step_unhandled_exception (p : Program) (s : State)
    (hfetch : fetchWord p s.pc = none) (haligned : s.pc.toNat % 4 = 0)
    (hvec : atUnhandledVector s = true) :
    step p s = StepResult.halt (.unhandledException (causeExcCode s) s.cp0Epc s.cp0BadVAddr) := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [ite_of_neg (by omega), ite_of_pos hvec]

/-- **Running off the program** (model boundary): an aligned `pc` holding
no instruction, when not at the exception vector with `EXL = 1`, halts with
`noInstruction pc`. -/
theorem step_no_instruction (p : Program) (s : State)
    (hfetch : fetchWord p s.pc = none) (haligned : s.pc.toNat % 4 = 0)
    (hvec : atUnhandledVector s = false) :
    step p s = StepResult.halt (.noInstruction s.pc) := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [ite_of_neg (by omega), ite_of_neg (by simp [hvec])]

/-! ### Delay slots -/

/-- Outside a delay slot, completing an instruction advances `pc` by 4. -/
theorem advance_not_in_delay_slot (orig result : State) (h : orig.pendingBranch = none) :
    advance orig result = { result with pc := result.pc + 4#32 } := by
  unfold advance; rw [h]

/-- **In a delay slot, completing an instruction commits the pending
target**: `pc` becomes `t` and the machine is no longer in a delay slot.
`result` — the instruction's effect on registers, memory and everything
else — is used exactly as computed. -/
theorem advance_in_delay_slot (orig result : State) (t : W32) (h : orig.pendingBranch = some t) :
    advance orig result = { result with pc := t, pendingBranch := none } := by
  unfold advance; rw [h]

/-! #### The general delay-slot theorem

For a non-control-transfer instruction, being in a delay slot changes
nothing about what the instruction *does*; it only changes where `pc` goes
afterwards. Formally: run the instruction once **not** in a delay slot
(`pendingBranch := none`) and once **in** one with pending target `t`
(`pendingBranch := some t`), from otherwise the same state. If the first
run completes normally — it yields a state `s'` with `s'.pc = s.pc + 4` —
then the second run yields exactly `{ s' with pc := t }`: the same
registers, memory, `hi`/`lo`, output, FP state, CP0 state and `LLbit`, with
`pc` on the branch target and no branch pending.

"Completes normally" is expressed as `s'.pc = s.pc + 4`. Exception entry
puts `pc` on the exception vector instead, so the side condition
`s.pc + 4 ≠ exceptionVector s` (the delay slot is not the word just below
the vector) makes that test exact. The exception case is covered by
`exceptionEntry_exl0_in_delay_slot`; a control-transfer instruction in a
delay slot by `branch_in_delay_slot_halts`. -/

/-- `DelaySlotRel pcNext t r0 r1`: if `r0` is normal completion at
`pcNext`, then `r1` is the same state with `pc := t`. (Proof device for
`execInstr_delay_slot`.) -/
def DelaySlotRel (pcNext t : W32) (r0 r1 : StepResult) : Prop :=
  match r0 with
  | .next s' => s'.pc = pcNext → r1 = StepResult.next { s' with pc := t }
  | .halt _ => True

theorem DelaySlotRel_ite (c : Prop) [Decidable c] (pcNext t : W32) (a b a' b' : StepResult)
    (h1 : c → DelaySlotRel pcNext t a a') (h2 : ¬ c → DelaySlotRel pcNext t b b') :
    DelaySlotRel pcNext t (if c then a else b) (if c then a' else b') := by
  by_cases h : c
  · rw [ite_of_pos h, ite_of_pos h]; exact h1 h
  · rw [ite_of_neg h, ite_of_neg h]; exact h2 h

/-- `readCString` only looks at memory. -/
theorem readCString_mem (s s' : State) (h : s.mem = s'.mem) (a : W32) (f : Nat) :
    readCString s a f = readCString s' a f := by
  induction f generalizing a with
  | zero => rfl
  | succ n ih => unfold readCString; rw [h, ih]

/-- `readCString` as a function of the memory alone (proof device). -/
def readCStringOfMem (m : Std.HashMap W32 UInt8) (a : W32) (f : Nat) : String :=
  readCString { initialState 0#32 with mem := m } a f

theorem readCString_eq_ofMem (pc : W32) (regs : Array W32) (hi lo : W32) (fpRegs : Array W32)
    (fcsr : W32) (mem : Std.HashMap W32 UInt8) (out : String) (pb : Option W32) (llBit : Bool)
    (st ca epc bva eepc lla eb a : W32) (f : Nat) :
    readCString ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, st, ca, epc, bva, eepc, lla, eb⟩ a f
      = readCStringOfMem mem a f :=
  readCString_mem ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, st, ca, epc, bva, eepc, lla, eb⟩
    { initialState 0#32 with mem := mem } rfl a f

theorem writeReg_proj_pc (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).pc = s.pc := by
  unfold writeReg; split <;> rfl
theorem writeReg_proj_hi (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).hi = s.hi := by
  unfold writeReg; split <;> rfl
theorem writeReg_proj_lo (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).lo = s.lo := by
  unfold writeReg; split <;> rfl
theorem writeReg_proj_fpRegs (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).fpRegs = s.fpRegs := by
  unfold writeReg; split <;> rfl
theorem writeReg_proj_fcsr (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).fcsr = s.fcsr := by
  unfold writeReg; split <;> rfl
theorem writeReg_proj_mem (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).mem = s.mem := by
  unfold writeReg; split <;> rfl
theorem writeReg_proj_out (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).out = s.out := by
  unfold writeReg; split <;> rfl
theorem writeReg_proj_pendingBranch (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).pendingBranch = s.pendingBranch := by
  unfold writeReg; split <;> rfl
theorem writeReg_proj_llBit (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).llBit = s.llBit := by
  unfold writeReg; split <;> rfl
theorem writeReg_proj_cp0Status (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0Status = s.cp0Status := by
  unfold writeReg; split <;> rfl
theorem writeReg_proj_cp0Cause (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0Cause = s.cp0Cause := by
  unfold writeReg; split <;> rfl
theorem writeReg_proj_cp0Epc (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0Epc = s.cp0Epc := by
  unfold writeReg; split <;> rfl
theorem writeReg_proj_cp0BadVAddr (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0BadVAddr = s.cp0BadVAddr := by
  unfold writeReg; split <;> rfl
theorem writeReg_proj_cp0ErrorEpc (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0ErrorEpc = s.cp0ErrorEpc := by
  unfold writeReg; split <;> rfl
theorem writeReg_proj_llAddr (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).llAddr = s.llAddr := by
  unfold writeReg; split <;> rfl
theorem writeReg_proj_cp0EBase (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0EBase = s.cp0EBase := by
  unfold writeReg; split <;> rfl
theorem writeReg_proj_regs (s : State) (i : Fin 32) (v : W32) :
    (writeReg s i v).regs = if i == 0 then s.regs else s.regs.set! i.val v := by
  unfold writeReg; split <;> rfl

set_option maxHeartbeats 0 in
/-- The delay-slot relation holds for every non-control-transfer
instruction. Proved structurally: after unfolding, both runs have the same
shape and are compared leaf by leaf. -/
theorem execInstr_delaySlotRel (s : State) (t : W32) (instr : Instruction)
    (hnb : isBranchLike instr = false) (hvec : s.pc + 4#32 ≠ exceptionVector s) :
    DelaySlotRel (s.pc + 4#32) t
      (execInstr { s with pendingBranch := none } instr)
      (execInstr { s with pendingBranch := some t } instr) := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  cases instr <;> first | exact Bool.noConfusion (hnb : true = false) | skip
  all_goals (
    unfold execInstr execBody
    dsimp only [isBranchLike]
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, mkNext, advance,
      takeException, takeAddressException, readReg, readFpReg, readMemWord, readMemHalf, readMemByte,
      writeMemWord, writeMemHalf, writeMemByte, writeFpReg, readFpD, writeFpD, fpFinishS, fpFinishD,
      fpFinishCmp, takeCoprocessorUnusable, readFcc,
      Option.getD_some, readCString_eq_ofMem, writeReg_proj_pc, writeReg_proj_hi, writeReg_proj_lo,
      writeReg_proj_fpRegs, writeReg_proj_fcsr, writeReg_proj_mem, writeReg_proj_out,
      writeReg_proj_pendingBranch, writeReg_proj_llBit, writeReg_proj_cp0Status,
      writeReg_proj_cp0Cause, writeReg_proj_cp0Epc, writeReg_proj_cp0BadVAddr,
      writeReg_proj_cp0ErrorEpc, writeReg_proj_llAddr, writeReg_proj_cp0EBase, writeReg_proj_regs]
    repeat' (first
      | exact (trivial : True)
      | (show (_ : State).pc = _ → _ = StepResult.next _
         intro hnorm
         first
          | exact absurd hnorm.symm hvec
          | rfl)
      | refine DelaySlotRel_ite _ _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      | split
      | (rename_i h; obtain ⟨_, rfl⟩ : _ ∧ _ = _ := by simpa using h)
      | (rename_i h; obtain rfl : _ = _ := by simpa using h)
      | (simp_all <;> (repeat (obtain ⟨_, rfl⟩ := ‹_ ∧ _›)) <;> try subst_vars)))

/-- **The general delay-slot theorem** (at the level of `execInstr`): see
the section comment above. -/
theorem execInstr_delay_slot (s : State) (t : W32) (instr : Instruction) (s' : State)
    (hnb : isBranchLike instr = false) (hvec : s.pc + 4#32 ≠ exceptionVector s)
    (h0 : execInstr { s with pendingBranch := none } instr = StepResult.next s')
    (hnormal : s'.pc = s.pc + 4#32) :
    execInstr { s with pendingBranch := some t } instr = StepResult.next { s' with pc := t } := by
  have h := execInstr_delaySlotRel s t instr hnb hvec
  rw [h0] at h
  exact h hnormal

/-- **The general delay-slot theorem, for `step`.** If the instruction at
`pc` is not a control transfer and, executed outside a delay slot, it
completes normally with result `s'`, then executed in a delay slot with
pending branch target `t` it produces `{ s' with pc := t }`: **the
resulting `pc` is `t`, and every other effect is identical.** This lifts
every `hpb : s.pendingBranch = none` theorem in this file to the
delay-slot case. -/
theorem delay_slot_commits_target (p : Program) (s : State) (t w : W32) (instr : Instruction)
    (s' : State)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some instr)
    (hnb : isBranchLike instr = false) (hvec : s.pc + 4#32 ≠ exceptionVector s)
    (h0 : step p { s with pendingBranch := none } = StepResult.next s')
    (hnormal : s'.pc = s.pc + 4#32) :
    step p { s with pendingBranch := some t } = StepResult.next { s' with pc := t } := by
  unfold step at h0 ⊢
  rw [show fetchWord p ({ s with pendingBranch := none } : State).pc = some w from hfetch] at h0
  rw [show fetchWord p ({ s with pendingBranch := some t } : State).pc = some w from hfetch]
  dsimp only at h0 ⊢
  rw [hdecode] at h0 ⊢
  exact execInstr_delay_slot s t instr s' hnb hvec h0 hnormal

/-! ## Group 1 — global invariants preserved by one step -/

/-- A `writeReg` call never moves the program counter: it only ever touches
the register file. Used throughout to simplify the "next state" shape that
`step` produces after an instruction writes a register. -/
theorem writeReg_pc (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).pc = s.pc := by
  unfold writeReg; split <;> rfl

/-- A `writeReg` call never changes `hi`, `lo`, `mem`, or `out` — only the
register file. -/
theorem writeReg_hi (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).hi = s.hi := by
  unfold writeReg; split <;> rfl

theorem writeReg_lo (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).lo = s.lo := by
  unfold writeReg; split <;> rfl

theorem writeReg_out (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).out = s.out := by
  unfold writeReg; split <;> rfl

/-- **`$zero` is never actually written.** Writing any value to any register
never changes what register `0` reads back: either the write targets `0`
itself (ignored outright, INSTRUCTION-REF Global rule §2) or it targets a
different register, which cannot disturb slot `0`. This is the building
block for "`$zero` always reads `0`" as a full-run invariant: every write in
the simulator goes through `writeReg`, so register `0` can never pick up a
nonzero value no matter how many steps run, as long as it started at `0`
(which `initialState` guarantees — see `State.lean`). -/
theorem writeReg_preserves_zero_slot (s : State) (i : Fin 32) (v : W32) :
    readReg (writeReg s i v) 0 = readReg s 0 := by
  unfold writeReg readReg
  split
  · rfl
  · next h =>
    have hne : i ≠ (0 : Fin 32) := by
      intro heq; exact h (by simp [heq])
    simp [Array.set!, Array.getD_eq_getD_getElem?, hne]

/-- Writing `v` to a nonzero register `i` and immediately reading `i` back
gives exactly `v` (the one register `writeReg` actually changes). -/
theorem writeReg_reads_back (s : State) (i : Fin 32) (v : W32) (hne : i ≠ 0)
    (hsize : s.regs.size = 32) :
    readReg (writeReg s i v) i = v := by
  unfold writeReg readReg
  rw [ite_of_neg (by simpa using hne)]
  simp [Array.set!, Array.getD_eq_getD_getElem?, hsize, i.isLt]

/-- Two states with the same `regs` field read `$zero` the same —
the register-file-only half of `readReg`: any state change that leaves
`regs` alone (`pc`/`pendingBranch`/`hi`/`lo`/`mem`/`out`/…) cannot disturb
`$zero`. -/
theorem readReg_zero_of_regs_eq {s1 s2 : State} (h : s1.regs = s2.regs) :
    readReg s1 0 = readReg s2 0 := by
  unfold readReg
  rw [h]

/-- `writeMemWord` never changes `regs` when it succeeds — it only ever
touches `mem` (INSTRUCTION-REF "sw"/"sc" sections' effective-address write).
-/
theorem writeMemWord_regs (s stored : State) (addr v : W32)
    (h : writeMemWord s addr v = some stored) : stored.regs = s.regs := by
  unfold writeMemWord at h
  split at h
  · cases h
  · injection h with h'
    rw [← h']

/-- `writeMemHalf` never changes `regs` when it succeeds — the halfword
counterpart of `writeMemWord_regs` (INSTRUCTION-REF "sh" section). -/
theorem writeMemHalf_regs (s stored : State) (addr v : W32)
    (h : writeMemHalf s addr v = some stored) : stored.regs = s.regs := by
  unfold writeMemHalf at h
  split at h
  · cases h
  · injection h with h'
    rw [← h']

/-- `writeMemByte` never changes `regs` — the byte-write counterpart of
`writeMemWord_regs`/`writeMemHalf_regs`, completing the trio. Unlike
`writeMemWord`/`writeMemHalf` it has no alignment check at all
(`writeMemByte`'s own docstring: "always succeeds"), so this is even
simpler to prove: no `split`, just unfold-and-read-off the `{ s with
mem := ... }` field. -/
theorem writeMemByte_regs (s stored : State) (addr : W32) (v : UInt8)
    (h : writeMemByte s addr v = some stored) : stored.regs = s.regs := by
  unfold writeMemByte at h
  injection h with h'
  rw [← h']

/-! ### `$zero` is preserved by every step — structural proof

The proof below does **not** go instruction by instruction. It shows that
the only ways `execInstr` (`step`'s dispatch) ever builds a
`StepResult` — `mkNext`, `takeException`, a literal `StepResult.next`/
`StepResult.halt` — keep register slot `0` intact as long as the result
state's register file was produced from `s`'s by `writeReg` (which ignores
writes to register `0`), `writeFpReg`/`writeFpD`/`writeMem*` (which
never touch `regs`), or a `{ s with … }` update of non-`regs` fields. One
generic tactic loop (`split` on every `if`/`match`, then simplify with
those facts) then discharges every `Instruction` constructor at once.

Because the loop is generic, **an instruction added to `Instruction`/
`execInstr` later is covered automatically** provided its register writes go
through `writeReg` — no new case is needed here. If a future instruction
wrote `regs` some other way, `execInstr_zeroKept` would fail to compile,
which is the desired behavior (the invariant would need a real argument). -/

/-- `ZeroKept s r`: if the step result `r` is a next state, register `0`
reads the same there as in `s`. (A halt satisfies this vacuously.) -/
def ZeroKept (s : State) (r : StepResult) : Prop :=
  ∀ s', r = StepResult.next s' → readReg s' 0 = readReg s 0

/-- `writeReg_preserves_zero_slot`, restated on the raw `regs` array (the
normal form the `zk_simp` simp set below works in). -/
theorem writeReg_regs_zero (s : State) (i : Fin 32) (v : W32) :
    (writeReg s i v).regs.getD 0 0#32 = s.regs.getD 0 0#32 :=
  writeReg_preserves_zero_slot s i v

/-- `writeFpReg` only touches `fpRegs`. -/
theorem writeFpReg_regs (s : State) (i : Fin 32) (v : W32) :
    (writeFpReg s i v).regs = s.regs := rfl

/-- `Step.lean`'s `writeFpD` (two `writeFpReg` calls) only touches
`fpRegs`. -/
theorem writeFpD_regs (s : State) (f : W32) (v : BitVec 64) :
    (writeFpD s f v).regs = s.regs := rfl

/-- `(writeMemByte s a v).getD d` (the shape `swl`/`swr` use) keeps `regs`. -/
theorem writeMemByte_getD_regs (s d : State) (a : W32) (v : UInt8) :
    ((writeMemByte s a v).getD d).regs = s.regs := rfl

/-- `Step.lean`'s `advance` (delay-slot resolution / `pc + 4`) only
touches `pc` and `pendingBranch`. -/
theorem advance_regs (orig result : State) : (advance orig result).regs = result.regs := by
  unfold advance; split <;> rfl

theorem zeroKept_halt (s : State) (h : HaltReason) : ZeroKept s (.halt h) ↔ True :=
  iff_true_intro (fun _ h' => by cases h')

theorem zeroKept_next (s r : State) :
    ZeroKept s (.next r) ↔ r.regs.getD 0 0#32 = s.regs.getD 0 0#32 :=
  ⟨fun h => h r rfl, fun h _ h' => by cases h'; exact h⟩

theorem zeroKept_mkNext (s r : State) :
    ZeroKept s (mkNext s r) ↔ r.regs.getD 0 0#32 = s.regs.getD 0 0#32 := by
  unfold mkNext
  rw [zeroKept_next, advance_regs]

theorem zeroKept_takeException (s : State) (c : W32) :
    ZeroKept s (takeException s c) ↔ True :=
  iff_true_intro (fun _ h' => by cases h'; rfl)

/-- An exception taken from a state `t` that differs from `s` outside `regs`
(the FP paths record FCSR first). -/
theorem zeroKept_takeException' (s t : State) (c : W32) :
    ZeroKept s (takeException t c) ↔ t.regs.getD 0 0#32 = s.regs.getD 0 0#32 :=
  ⟨fun h => h (exceptionEntry t c) rfl, fun h _ h' => by cases h'; exact h⟩

theorem zeroKept_takeAddressException (s : State) (c a : W32) :
    ZeroKept s (takeAddressException s c a) ↔ True :=
  iff_true_intro (fun _ h' => by cases h'; rfl)

theorem zeroKept_exceptionEntry (s : State) (c ce : W32) :
    ZeroKept s (StepResult.next (exceptionEntry s c ce)) ↔ True :=
  iff_true_intro (fun _ h' => by cases h'; rfl)

theorem zeroKept_takeCoprocessorUnusable (s : State) :
    ZeroKept s (takeCoprocessorUnusable s) ↔ True :=
  iff_true_intro (fun _ h' => by cases h'; rfl)

/-- The three ways an FP computational instruction completes
(`fpFinishS`/`fpFinishD`/`fpFinishCmp`: Floating Point exception, or FCSR
update plus an FP-register / condition-code write) never touch `regs`. -/
theorem zeroKept_fpFinishS (s : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags) :
    ZeroKept s (fpFinishS s fd r) ↔ True :=
  iff_true_intro (by
    intro s' h
    unfold fpFinishS at h
    dsimp only at h
    split at h
    · cases h; rfl
    · cases h
      show (advance _ _).regs.getD 0 0#32 = _
      rw [advance_regs]; rfl)

theorem zeroKept_fpFinishD (s : State) (fd : W32) (r : BitVec 64 × Mips.Fp.Flags) :
    ZeroKept s (fpFinishD s fd r) ↔ True :=
  iff_true_intro (by
    intro s' h
    unfold fpFinishD at h
    dsimp only at h
    split at h
    · cases h; rfl
    · cases h
      show (advance _ _).regs.getD 0 0#32 = _
      rw [advance_regs]; rfl)

theorem zeroKept_fpFinishCmp (s : State) (cc : W32) (r : Bool × Mips.Fp.Flags) :
    ZeroKept s (fpFinishCmp s cc r) ↔ True :=
  iff_true_intro (by
    intro s' h
    unfold fpFinishCmp at h
    dsimp only at h
    split at h
    · cases h; rfl
    · cases h
      show (advance _ _).regs.getD 0 0#32 = _
      rw [advance_regs]; rfl)

/-- Forward step for the tactic loop below: for every hypothesis of the
form `writeMem{Byte,Half,Word} s a v = some s'` in the context (these
appear when `split` case-splits a store instruction's `match` on the write
result), add the fact `s'.regs = s.regs`. -/
elab "zk_fwd" : tactic => Lean.Elab.Tactic.withMainContext do
  for d in (← Lean.getLCtx) do
    if d.isImplementationDetail then continue
    for lem in [``writeMemByte_regs, ``writeMemHalf_regs, ``writeMemWord_regs] do
      try
        let pf ← Lean.Meta.mkAppOptM lem #[none, none, none, none, some d.toExpr]
        let ty ← Lean.Meta.inferType pf
        Lean.Elab.Tactic.liftMetaTactic fun g => do
          let (_, g) ← (← g.assert `hregs ty pf).intro1
          return [g]
      catch _ => pure ()

/-- Simp set for the tactic loop below: reduce a `ZeroKept` goal about one
of `execInstr`'s result shapes to a statement about `regs[0]`, and push
that through every state-update primitive (plus any `regs` equations
`zk_fwd` put in the context). -/
macro "zk_simp" : tactic => `(tactic|
  simp only [zeroKept_halt, zeroKept_next, zeroKept_mkNext, zeroKept_takeException,
    zeroKept_takeException', zeroKept_takeAddressException, zeroKept_takeCoprocessorUnusable, zeroKept_fpFinishS,
    zeroKept_fpFinishD, zeroKept_fpFinishCmp,
    writeReg_regs_zero, writeFpReg_regs, writeFpD_regs, writeMemByte_getD_regs, *])

-- ~180 constructors through one generic tactic loop
set_option maxHeartbeats 4000000 in
/-- **Every instruction keeps `$zero`.** `execInstr` (the dispatch
`step` calls after fetch/decode) never changes what register `0` reads,
for any instruction and any state — including states with a pending
delay-slot transfer. Proved structurally (see the section comment above),
not by a per-instruction case list. -/
theorem execInstr_zeroKept (s : State) (instr : Instruction) :
    ZeroKept s (execInstr s instr) := by
  unfold execInstr
  split
  · exact (zeroKept_halt _ _).mpr trivial
  · split
    · exact (zeroKept_takeCoprocessorUnusable _).mpr trivial
    · unfold execBody
      cases instr <;> dsimp only <;> repeat' (first | (zk_fwd; zk_simp; done) | split)

/-- **Global invariant: `$zero` is never changed by a step.** If `step`
produces a next state, register `0` reads the same thing after the step as
before — for **every** instruction, with no side conditions (INSTRUCTION-REF
Global rule 2, "writes to `$zero` are a no-op"). Proof: `step` is
fetch/decode followed by `execInstr`; see `execInstr_zeroKept`. -/
theorem step_preserves_zero_register (p : Program) (s s' : State)
    (hstep : step p s = StepResult.next s') : readReg s' 0 = readReg s 0 := by
  unfold step at hstep
  split at hstep
  · split at hstep
    · exact (zeroKept_takeAddressException s _ _).mpr trivial _ hstep
    · split at hstep <;> cases hstep
  · split at hstep
    · split at hstep
      · exact (zeroKept_takeCoprocessorUnusable s).mpr trivial _ hstep
      · split at hstep
        · exact (zeroKept_exceptionEntry s _ _).mpr trivial _ hstep
        · exact (zeroKept_takeException s _).mpr trivial _ hstep
    · exact execInstr_zeroKept _ _ _ hstep

/-- **`$zero` reads `0` after any step**, given it read `0` before
(which `initialState` guarantees). The plain-English form of
`step_preserves_zero_register`. -/
theorem step_zero_register_reads_zero (p : Program) (s s' : State)
    (hzero : readReg s 0 = 0#32) (hstep : step p s = StepResult.next s') :
    readReg s' 0 = 0#32 := by
  rw [step_preserves_zero_register p s s' hstep, hzero]

/-- The state a `run` ended in (halted or out of step budget). -/
def RunResult.finalState : RunResult → State
  | .halted _ s _ => s
  | .limitReached s _ => s

/-- `run`'s inner loop never changes `$zero`: each iteration is one `step`
(`step_preserves_zero_register`). -/
theorem run_go_preserves_zero_register (p : Program) (fuel : Nat) (s : State) (steps : Nat) :
    readReg (run.go p fuel s steps).finalState 0 = readReg s 0 := by
  induction fuel generalizing s steps with
  | zero => rfl
  | succ n ih =>
    unfold run.go
    split
    · rfl
    · next s1 h =>
      rw [ih s1 (steps + 1)]
      exact step_preserves_zero_register p s s1 h

/-- **Whole-run invariant: `$zero` is the same at the end of any run as at
its start**, for any program, any start state, any step budget. -/
theorem run_preserves_zero_register (p : Program) (s₀ : State) (maxSteps : Nat) :
    readReg (run p s₀ maxSteps).finalState 0 = readReg s₀ 0 :=
  run_go_preserves_zero_register p maxSteps s₀ 0

/-- **`$zero` reads `0` at the end of every run started from
`initialState`.** -/
theorem run_initialState_zero_register (p : Program) (pc : W32) (maxSteps : Nat) :
    readReg (run p (initialState pc) maxSteps).finalState 0 = 0#32 := by
  rw [run_preserves_zero_register]; rfl


/-! ## Group 2 — per-instruction specs (semantics-critical subset) -/

/-- **`add` computes the exact sum, or traps exactly on signed overflow.**
This is `step`'s own code, restated with public names: the raw sum is
formed, `addOverflowsSpec` is INSTRUCTION-REF's Java-derived overflow test
("add" section), and the instruction either raises
Integer Overflow (`takeException s excCodeOv`) or writes the sum and advances the program counter by
4. Every other `add`-related theorem is a corollary of this one. -/
theorem add_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.add rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let av := readReg s (regIdxSpec rs)
      let bv := readReg s (regIdxSpec rt)
      let sumBV := av + bv
      if addOverflowsSpec (asSigned av) (asSigned bv) (asSigned sumBV) then
        takeException s excCodeOv
      else
        StepResult.next
          { (writeReg s (regIdxSpec rd) sumBV) with
            pc := (writeReg s (regIdxSpec rd) sumBV).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Closed weaker version of `step_preserves_zero_register`, for the
representative case of `add` (the trickiest arithmetic instruction, since it
has both a halting branch and a register-writing branch): whichever branch
`step` takes, register `0` reads the same value before and after. -/
theorem step_add_preserves_zero_register (p : Program) (s s' : State) (w rs rt rd : W32)
    (hfw : fetchWord p s.pc = some w) (hdw : decode w = some (.add rs rt rd))
    (hpb : s.pendingBranch = none)
    (hstep : step p s = StepResult.next s') : readReg s' 0 = readReg s 0 := by
  rw [add_spec_raw p s w rs rt rd hfw hdw hpb] at hstep
  dsimp only at hstep
  split at hstep
  · cases hstep; rfl
  · injection hstep with hs
    rw [← hs]
    exact writeReg_preserves_zero_slot s _ _

/-- **`sub` computes the exact difference, or traps exactly on signed
overflow.** Mirrors `add_spec_raw`; `subOverflowsSpec` is INSTRUCTION-REF's
"sub" overflow test. -/
theorem sub_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sub rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let av := readReg s (regIdxSpec rs)
      let bv := readReg s (regIdxSpec rt)
      let diffBV := av - bv
      if subOverflowsSpec (asSigned av) (asSigned bv) (asSigned diffBV) then
        takeException s excCodeOv
      else
        StepResult.next
          { (writeReg s (regIdxSpec rd) diffBV) with
            pc := (writeReg s (regIdxSpec rd) diffBV).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`addi` computes `$rs + sext16(imm)` exactly, or traps exactly on
signed overflow.** The immediate is sign-extended first (INSTRUCTION-REF
"addi" section), then the same overflow test as `add` applies. -/
theorem addi_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.addi rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let av := readReg s (regIdxSpec rs)
      let bv := signExt16 imm
      let sumBV := av + bv
      if addOverflowsSpec (asSigned av) (asSigned bv) (asSigned sumBV) then
        takeException s excCodeOv
      else
        StepResult.next
          { (writeReg s (regIdxSpec rt) sumBV) with
            pc := (writeReg s (regIdxSpec rt) sumBV).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`add` overflow raises Integer Overflow (ExcCode 12), in or out of a
delay slot** — no `pendingBranch` hypothesis. `$rd` is not written
(`exceptionEntry_always`: exception entry changes no general register);
`EPC`/`Cause.BD` follow `exceptionEntry_*`. -/
theorem add_overflow_raises_ov (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.add rs rt rd))
    (hov : addOverflowsSpec (asSigned (readReg s (regIdxSpec rs))) (asSigned (readReg s (regIdxSpec rt)))
      (asSigned (readReg s (regIdxSpec rs) + readReg s (regIdxSpec rt))) = true) :
    step p s = takeException s excCodeOv := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  show (if addOverflows _ _ _ = true then takeException s excCodeOv else _) = _
  rw [ite_of_pos hov]

/-- **`sub` overflow raises Integer Overflow**, in or out of a delay slot. -/
theorem sub_overflow_raises_ov (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sub rs rt rd))
    (hov : subOverflowsSpec (asSigned (readReg s (regIdxSpec rs))) (asSigned (readReg s (regIdxSpec rt)))
      (asSigned (readReg s (regIdxSpec rs) - readReg s (regIdxSpec rt))) = true) :
    step p s = takeException s excCodeOv := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  show (if subOverflows _ _ _ = true then takeException s excCodeOv else _) = _
  rw [ite_of_pos hov]

/-- **`addi` overflow raises Integer Overflow**, in or out of a delay slot. -/
theorem addi_overflow_raises_ov (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.addi rs rt imm))
    (hov : addOverflowsSpec (asSigned (readReg s (regIdxSpec rs))) (asSigned (signExt16 imm))
      (asSigned (readReg s (regIdxSpec rs) + signExt16 imm)) = true) :
    step p s = takeException s excCodeOv := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  show (if addOverflows _ _ _ = true then takeException s excCodeOv else _) = _
  rw [ite_of_pos hov]

/-- **`div` by a nonzero divisor truncates toward zero; the remainder takes
the dividend's sign** (Lean's `Int.tdiv`/`Int.tmod`, matching Java's `/`/`%`
used by MARS — INSTRUCTION-REF "div" section). **`div` by zero leaves `hi`
and `lo` untouched and does not halt** (SPEC-NOTES §9.2 / INSTRUCTION-REF
"div" MARS-note: this is a deliberate MIPS32-spec reading, not a MARS bug).
Both cases always advance the program counter by 4. -/
theorem div_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.div rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      if b == 0 then
        StepResult.next { s with pc := s.pc + 4#32 }
      else
        StepResult.next { s with lo := ofInt32 (a.tdiv b), hi := ofInt32 (a.tmod b), pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Corollary of `div_spec_raw`: dividing by `0` leaves `hi`/`lo` exactly as
they were and does not halt — INSTRUCTION-REF "div" MARS-note, SPEC-NOTES
§9.2. -/
theorem div_by_zero_spec (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.div rs rt))
    (hpb : s.pendingBranch = none)
    (hzero : readReg s (regIdxSpec rt) = 0#32) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [div_spec_raw p s w rs rt hfetch hdecode hpb, hzero]
  rfl

/-- Corollary of `div_spec_raw`: with a **negative dividend** and a nonzero
divisor, `div` rounds toward zero, so the remainder written to `hi`
(`Int.tmod`) is **never positive** — it takes the dividend's sign, whatever
the divisor's sign (INSTRUCTION-REF "div" section). A floor-rounding
division would give a positive remainder for a positive divisor. -/
theorem div_negative_dividend_spec (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.div rs rt))
    (hpb : s.pendingBranch = none)
    (hnz : asSigned (readReg s (regIdxSpec rt)) ≠ 0)
    (hneg : asSigned (readReg s (regIdxSpec rs)) < 0) :
    step p s =
      StepResult.next
        { s with
          lo := ofInt32 ((asSigned (readReg s (regIdxSpec rs))).tdiv (asSigned (readReg s (regIdxSpec rt))))
          hi := ofInt32 ((asSigned (readReg s (regIdxSpec rs))).tmod (asSigned (readReg s (regIdxSpec rt))))
          pc := s.pc + 4#32 } ∧
      (asSigned (readReg s (regIdxSpec rs))).tmod (asSigned (readReg s (regIdxSpec rt))) ≤ 0 := by
  constructor
  · rw [div_spec_raw p s w rs rt hfetch hdecode hpb]
    simp [hnz]
  · have h1 := Int.tmod_nonneg (a := -asSigned (readReg s (regIdxSpec rs)))
      (asSigned (readReg s (regIdxSpec rt))) (by omega)
    rw [Int.neg_tmod] at h1
    omega

/-- **`beq`/`bne` branch target and condition, in one equation — real
MIPS32 one-delay-slot semantics.** Mirrors `step`'s own code: the
comparison `$rs == $rt` picks between an ordinary fallthrough to `PC_next`
and *scheduling* (not jumping to) `PC_next + (sext16(offset) << 2)` via
`pendingBranch`, with `beq` and `bne` using the comparison the opposite way
around. A taken branch never updates `pc` past `PC_next` in this same step
— the delay-slot instruction at `PC_next` always executes first; the
schedule is committed by the *next* step's `advance` (`Step.lean`), see
`beq_taken_delay_slot_lands_on_target` below for the two-step composition
(SPEC-NOTES §9 item 1; INSTRUCTION-REF Global rule 3 — this supersedes the
old no-delay-slot MARS-default behavior). The hypothesis `hpb` restricts
this equation to the ordinary case where `s` is not itself sitting in
another pending delay slot; see `branch_in_delay_slot_halts` for that other
case. -/
theorem beq_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

theorem bne_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bne rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        StepResult.next { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }
      else
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`beq`, taken**: when `$rs = $rt`, `beq` schedules
`PC_next + (offset << 2)` as the pending delay-slot transfer and itself
falls through to `PC_next` — it does **not** jump immediately
(INSTRUCTION-REF Global rule 3: real MIPS32 always executes one delay-slot
instruction first). -/
theorem beq_taken_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rs) = readReg s (regIdxSpec rt)) :
    step p s = StepResult.next
      { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [beq_spec_raw p s w rs rt imm hfetch hdecode hpb, ite_of_pos (by simpa using htaken)]

/-- **`beq`, not taken**: when `$rs ≠ $rt`, control simply falls through to
`PC_next`, exactly as an ordinary instruction — no `pendingBranch` is ever
set (INSTRUCTION-REF "beq" section). -/
theorem beq_not_taken_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt)) :
    step p s = StepResult.next { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  rw [beq_spec_raw p s w rs rt imm hfetch hdecode hpb, ite_of_neg (by simpa using hnot)]

/-- **`bne`, taken**: when `$rs ≠ $rt`, schedules `PC_next + (offset << 2)`
— the mirror image of `beq`, same one-delay-slot discipline. -/
theorem bne_taken_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bne rs rt imm))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt)) :
    step p s = StepResult.next
      { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bne_spec_raw p s w rs rt imm hfetch hdecode hpb, ite_of_neg (by simpa using htaken)]

/-- **`bne`, not taken**: when `$rs = $rt`, falls through to `PC_next`. -/
theorem bne_not_taken_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bne rs rt imm))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rs) = readReg s (regIdxSpec rt)) :
    step p s = StepResult.next { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  rw [bne_spec_raw p s w rs rt imm hfetch hdecode hpb, ite_of_pos (by simpa using hnot)]

/-- **Two-step delay-slot composition for a taken `beq`**: the branch's own
step only schedules the target (`beq_taken_spec`); it is the *following*
step — executing the delay-slot instruction — that actually lands `pc` on
it (`advance` in `Step.lean`, triggered by any ordinary, non-branch-like
instruction; demonstrated concretely here with `sll $zero,$zero,0` i.e.
`nop` as the delay-slot filler). This is the theorem that directly
witnesses "real MIPS32 branch delay slot" as a two-instruction behavior,
matching the task's exact semantics rather than only the one-step schedule
captured by `beq_taken_spec`. -/
theorem beq_taken_delay_slot_lands_on_target (p : Program) (s : State) (w w2 rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rs) = readReg s (regIdxSpec rt))
    (hfetch2 : fetchWord p (s.pc + 4#32) = some w2)
    (hdecode2 : decode w2 = some (.sll 0#32 0#32 0#32)) :
    ∃ s1 s2,
      step p s = StepResult.next s1 ∧
      step p s1 = StepResult.next s2 ∧
      s2.pc = (s.pc + 4#32) + (signExt16 imm <<< 2) := by
  have h1 := beq_taken_spec p s w rs rt imm hfetch hdecode hpb htaken
  have h2 : step p { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } = StepResult.next { s with pc := (s.pc + 4#32) + (signExt16 imm <<< 2), pendingBranch := none } := by
    unfold step
    rw [show fetchWord p ({ s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } : State).pc = some w2 from hfetch2]
    dsimp only
    rw [hdecode2]
    dsimp only
    rfl
  exact ⟨_, _, h1, h2, rfl⟩

/-- **`jal` links `$ra` to `pc + 8` — past the delay slot, not `PC_next`
(`pc + 4`) — and schedules a jump to a target whose top 4 bits come from
`PC_next`, not from `jal`'s own address** (INSTRUCTION-REF Global rule 3:
real MIPS32's `jal` link value is the address of the instruction *after*
the delay slot, since the delay-slot instruction itself still executes
before control can return to `$ra`). Like `beq`/`bne`, `jal` schedules the
jump via `pendingBranch` and itself falls through to `PC_next`; it never
jumps in the same step. -/
theorem jal_spec_raw (p : Program) (s : State) (w target : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jal target))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      StepResult.next
        { (writeReg s 31 (pcNext + 4#32)) with
          pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Corollary of `jal_spec_raw`: `$ra` (register 31) reads back exactly
`pc + 8`, i.e. the address of the instruction *after* the delay slot
(`jal`'s own address plus 8), not `pc + 4`. -/
theorem jal_sets_ra (p : Program) (s : State) (w target : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jal target))
    (hpb : s.pendingBranch = none)
    (hsize32 : s.regs.size = 32) :
    ∃ s', step p s = StepResult.next s' ∧ readReg s' (regIdxSpec 31#32) = s.pc + 8#32 := by
  refine ⟨_, jal_spec_raw p s w target hfetch hdecode hpb, ?_⟩
  show readReg (writeReg s 31 ((s.pc + 4#32) + 4#32)) (regIdxSpec 31#32) = s.pc + 8#32
  have h31 : regIdxSpec 31#32 = (31 : Fin 32) := by decide
  rw [h31, writeReg_reads_back s 31 ((s.pc + 4#32) + 4#32) (by decide) hsize32,
    BitVec.add_assoc]
  congr 1

/-- **A branch, jump or `eret` in a branch delay slot halts.** The
architecture makes this UNPREDICTABLE; rather than pick a behavior, `step`
reports `HaltReason.branchInDelaySlot` whenever the instruction about to
execute is in a delay slot (`s.pendingBranch = some _` — set by *every*
branch/jump, taken or not) and is itself one of the 24
instructions of `isBranchLike` (`isBranchLikeSpec` is that same
definition): the 12 branches/jumps, the 8 branch-likelies, `bc1t`/`bc1f`,
`eret` and `wait` (SPEC-NOTES §9 item 1; INSTRUCTION-REF Global rule 3). -/
theorem branch_in_delay_slot_halts (p : Program) (s : State) (w : W32) (instr : Instruction)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some instr)
    (hpb : s.pendingBranch.isSome = true) (hbr : isBranchLikeSpec instr = true) :
    step p s = StepResult.halt .branchInDelaySlot := by
  have hbr' : isBranchLike instr = true := hbr
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  unfold execInstr
  simp only [hpb, hbr', Bool.and_self, ↓reduceIte]

/-- **`lw` composes a big-endian word from memory at `$rs + sext16(offset)`,
or raises Address Error on a misaligned effective address**
(INSTRUCTION-REF "lw" section; SPEC-NOTES §9.3 — the offset is
sign-extended, unlike MARS's own latent zero-extension bug for raw-decoded
binaries). -/
theorem lw_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) v) with
            pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Corollary of `lw_spec_raw`: a misaligned effective address raises Address
Error, naming that exact address. -/
theorem lw_misaligned_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none)
    (hmisaligned : (readReg s (regIdxSpec rs) + signExt16 imm).toNat % 4 ≠ 0) :
    step p s = takeAddressException s excCodeAdEL (readReg s (regIdxSpec rs) + signExt16 imm) := by
  rw [lw_spec_raw p s w rs rt imm hfetch hdecode hpb]
  dsimp only
  rw [show readMemWord s (readReg s (regIdxSpec rs) + signExt16 imm) = none by
    unfold readMemWord
    rw [ite_of_pos hmisaligned]]

/-- Spec-side name for `Step.lean`'s `readCString` — the same definition, not a copy. -/
abbrev readCStringSpec := readCString

/-- Spec-side name for `Step.lean`'s `printStringFuel` — the same definition, not a copy. -/
abbrev printStringFuelSpec := printStringFuel

/-- `readCStringSpec` is `Step.lean`'s `readCString` (definitionally: it is
an abbreviation, not a copy). -/
theorem readCStringSpec_eq (s : State) (addr : W32) (fuel : Nat) :
    readCStringSpec s addr fuel = readCString s addr fuel := rfl

/-- **`syscall` dispatches on `$v0` (register 2) and implements exactly
four services** (INSTRUCTION-REF syscall section), every other service
number raising the architectural Syscall exception (ExcCode 8) — the
four services are the model's environment-call convention (SPEC-NOTES §9):

* `1` (`PrintInt`): append the signed decimal rendering of `$a0` to `out`;
* `4` (`PrintString`): append the NUL-terminated string at address `$a0`
  (scan bounded by `printStringFuelSpec` bytes) to `out`;
* `10` (`Exit`): halt with `HaltReason.exit`;
* `11` (`PrintChar`): append the character whose code is the low byte of
  `$a0` to `out`.

The three printing services change nothing but `out` and advance `pc` by 4
(given no delay-slot transfer is pending, as in every other `_spec_raw`
theorem). -/
theorem syscall_spec_raw (p : Program) (s : State) (w code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.syscall code))
    (hpb : s.pendingBranch = none) :
    step p s =
      match (readReg s (regIdxSpec 2#32)).toNat with
      | 1 =>
        StepResult.next
          { s with out := s.out ++ toString (asSigned (readReg s (regIdxSpec 4#32))),
                   pc := s.pc + 4#32 }
      | 4 =>
        StepResult.next
          { s with out := s.out ++ readCStringSpec s (readReg s (regIdxSpec 4#32)) printStringFuelSpec,
                   pc := s.pc + 4#32 }
      | 10 => StepResult.halt .exit
      | 11 =>
        StepResult.next
          { s with out := s.out ++ String.singleton
                     (Char.ofNat ((readReg s (regIdxSpec 4#32) &&& 0xff#32).toNat)),
                   pc := s.pc + 4#32 }
      | _ => takeException s excCodeSys := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  unfold execInstr execBody
  have h2 : regIdxSpec 2#32 = 2 := by decide
  rw [h2]
  simp only [show isBranchLike (Instruction.syscall code) = false from rfl,
    show usesCop1 (Instruction.syscall code) = false from rfl, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte]
  -- both sides are now a `match` on the same `$v0` value; name it and
  -- compare the two dispatch tables case by case
  generalize (readReg _ 2).toNat = n
  split <;> first | rfl | (split <;> first | rfl | (exfalso; simp_all))

/-- **syscall 1 (`PrintInt`) appends the signed decimal rendering of `$a0`
to `out`, with no trailing newline**, and advances the program counter by 4
(INSTRUCTION-REF "syscall 1 — PrintInt": `Integer.toString`, decimal,
signed; no other state changes). The `hpb` hypothesis (no delay-slot
transfer pending) is required, as for every other `mkNext`-based theorem:
with `s.pendingBranch = some t` the next `pc` is `t`, not `s.pc + 4`. -/
theorem syscall1_spec (p : Program) (s : State) (w code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.syscall code))
    (hv0 : readReg s (regIdxSpec 2#32) = 1#32) (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next { s with out := s.out ++ toString (asSigned (readReg s (regIdxSpec 4#32))), pc := s.pc + 4#32 } := by
  rw [syscall_spec_raw p s w code hfetch hdecode hpb, hv0]; rfl

/-- **syscall 10 (`Exit`) halts the program cleanly**, ignoring every
register — modeled as `HaltReason.exit`, distinct from every error halt
(INSTRUCTION-REF "syscall 10 — Exit"). Holds whether or not a delay-slot
transfer is pending (no `hpb` hypothesis). -/
theorem syscall10_spec (p : Program) (s : State) (w code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.syscall code))
    (hv0 : readReg s (regIdxSpec 2#32) = 10#32) :
    step p s = StepResult.halt .exit := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  unfold execInstr execBody
  have h2 : regIdxSpec 2#32 = 2 := by decide
  rw [h2] at hv0
  simp only [show isBranchLike (Instruction.syscall code) = false from rfl,
    show usesCop1 (Instruction.syscall code) = false from rfl, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte]
  rw [hv0]
  rfl

/-! Proof note on the syscall theorems. The proofs unfold `execInstr`,
rewrite with the `$v0` hypothesis, and compare the two dispatch tables.
(History:
`syscall1_spec` originally lacked the `hpb` hypothesis and was false as
stated — counterexample `s.pendingBranch = some 0xabcd#32`, where `step`
yields `pc = 0xabcd#32`; `hpb` was added before these proofs were written.) -/


/-- One-instruction program containing `instr` at `textBase`, for building
concrete examples below. -/
def prog1Spec (instr : Instruction) : Program := (∅ : Program).insert textBase (encode instr)

/-- Apply a list of register writes to a state, for building concrete
examples below. -/
def setRegsSpec (s : State) (kvs : List (Fin 32 × W32)) : State :=
  kvs.foldl (fun acc kv => writeReg acc kv.1 kv.2) s

/-- A sequential program starting at `base`, for building concrete
delay-slot examples below (mirrors `Step.lean`'s test-only `buildProg`). -/
def buildProgSpec (base : W32) (instrs : List Instruction) : Program :=
  instrs.zipIdx.foldl (fun acc (instr, i) => acc.insert (base + BitVec.ofNat 32 (4 * i)) (encode instr))
    (∅ : Program)

-- Closed weaker version of `syscall1_spec`: a concrete syscall-1 call
-- appends the decimal rendering of `$a0`, with no trailing newline.
#guard (match step (prog1Spec (.syscall 0#32)) (setRegsSpec (initialState textBase) [(2, 1#32), (4, 5#32)]) with
        | .next s => s.out
        | .halt _ => "unreachable") = "5"

-- Closed weaker version of `syscall10_spec`: a concrete syscall-10 call
-- halts with `.exit`.
#guard (match step (prog1Spec (.syscall 0#32)) (setRegsSpec (initialState textBase) [(2, 10#32)]) with
        | .next _ => false
        | .halt r => r == .exit) = true

/-! ## Group 3 — satisfiable examples

Each theorem above is instantiated on a concrete program/state with every
hypothesis discharged, confirming the hypotheses are not vacuous. Anything
that runs `step` on a concrete `Program`/`State.mem` is checked with
`#guard` (compiled evaluation): `Program`/`State.mem` are `Std.HashMap`s
marked `cbv_opaque`, so `decide`/`rfl` get stuck on them, but the pure
arithmetic side conditions (`decode`, overflow tests, register indices) are
checked with `by decide`. -/

-- `add_spec_raw`: 5 + 7 does not overflow, giving a `.next` state with
-- `$t2 = 12` and `pc` advanced by 4.
example : decode (encode (Instruction.add 8#32 9#32 10#32)) = some (.add 8#32 9#32 10#32) := by decide
#guard (match step (prog1Spec (.add 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with
        | .next s => readReg s 10 == 12#32 && s.pc == textBase + 4#32
        | .halt _ => false) = true

-- `step_add_preserves_zero_register`: a concrete non-overflowing `add`
-- leaves register `0` at `0`.
#guard (match step (prog1Spec (.add 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with
        | .next s => readReg s 0 == 0#32
        | .halt _ => false) = true

-- `sub_spec_raw`: `0x80000000 - 1` overflows (INT_MIN minus a positive is
-- itself non-negative after wraparound), so `sub` halts.
#guard (match step (prog1Spec (.sub 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x80000000#32), (9, 1#32)]) with
        | .next s' => causeExcCode s' == excCodeOv && s'.pc == exceptionVectorAddr
        | .halt _ => false) = true

-- `addi_spec_raw`: `addi $t1, $zero, 5` does not overflow.
#guard (match step (prog1Spec (.addi 0#32 9#32 5#32)) (initialState textBase) with
        | .next s => readReg s 9 == 5#32
        | .halt _ => false) = true

-- `div_by_zero_spec`: dividing by `0` leaves a pre-seeded `hi`/`lo` alone.
#guard (match step (prog1Spec (.div 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 10#32), (9, 0#32)]) with
            hi := 0xdeadbeef#32, lo := 0xcafef00d#32 } with
        | .next s => s.hi == 0xdeadbeef#32 && s.lo == 0xcafef00d#32
        | .halt _ => false) = true

-- `div_negative_dividend_spec`: `-17 / 5` truncates to `-3`; the remainder
-- `-2` carries the dividend's sign (`tdiv`/`tmod`, not Euclidean division).
#guard (match step (prog1Spec (.div 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffef#32), (9, 5#32)]) with
        | .next s => s.lo == 0xfffffffd#32 && s.hi == 0xfffffffe#32
        | .halt _ => false) = true

-- `beq_taken_spec`/`beq_not_taken_spec`: equal registers schedule the
-- target via `pendingBranch` and fall through to the delay slot first
-- (real MIPS32 one-delay-slot semantics); unequal registers fall through
-- exactly as an ordinary instruction.
#guard (match step (prog1Spec (.beq 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.beq 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 8#32)
        | .halt _ => false) = true

-- `bne_taken_spec`/`bne_not_taken_spec`: the mirror image of `beq`.
#guard (match step (prog1Spec (.bne 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true

-- `beq_taken_delay_slot_lands_on_target`: the delay-slot instruction's own
-- step is what actually lands `pc` on the scheduled target.
#guard (match step (buildProgSpec textBase [.beq 8#32 9#32 3#32, .sll 0#32 0#32 0#32])
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)]) with
        | .next s1 =>
          (match step (buildProgSpec textBase [.beq 8#32 9#32 3#32, .sll 0#32 0#32 0#32]) s1 with
            | .next s2 => s2.pc == textBase + 4#32 + 12#32
            | .halt _ => false)
        | .halt _ => false) = true

-- `jal_sets_ra`: `$ra` ends up exactly `pc + 8` (past the delay slot), and
-- the jump is scheduled (not immediate) with its target's top 4 bits
-- coming from `pc + 4`, not from `jal`'s own address.
#guard (match step (prog1Spec (.jal 0x1000#32)) (initialState textBase) with
        | .next s =>
          readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some 0x4000#32
        | .halt _ => false) = true

-- `lw_spec_raw`: a big-endian word loaded back out.
#guard (match
          (writeMemWord (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
            0x10010000#32 0x12345678#32).bind
          (fun s => some (step (prog1Spec (.lw 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0x12345678#32
        | _ => false) = true

-- `lw_misaligned_spec`: an unaligned effective address halts with the
-- exact failing address.
#guard (match step (prog1Spec (.lw 8#32 9#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0x10010000#32)]) with
        | .next s' => s'.cp0BadVAddr == 0x10010001#32 && s'.pc == exceptionVectorAddr
        | .halt _ => false) = true

-- `lb_spec_raw`/`lbu_spec_raw`: the same high-bit byte sign-extends under `lb` and
-- zero-extends under `lbu`.
#guard (match (writeMemByte (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
          0x10010000#32 0x80).bind (fun s => some (step (prog1Spec (.lb 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0xffffff80#32
        | _ => false) = true
#guard (match (writeMemByte (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
          0x10010000#32 0x80).bind (fun s => some (step (prog1Spec (.lbu 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0x00000080#32
        | _ => false) = true

-- `syscall1_concrete_example`/`syscall10`: already given above as the
-- closed weaker versions of `syscall1_spec`/`syscall10_spec`.

/-! ## Group 4 — bad-output rejection

The spec also rejects known-wrong behaviors: outcomes a buggy
implementation might plausibly produce, but which `step` provably does
not. -/

/-- **Overflow does not silently wrap.** A buggy `add` might wrap
`0x7fffffff + 1` to `0x80000000`, write it to `$10` and continue; the real
`add` raises the Integer Overflow exception (ExcCode 12) instead: the step
is exactly exception entry, and exception entry changes no general
register — in particular the destination `$10` is not written. -/
theorem add_overflow_not_wrapped (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.add 8#32 9#32 10#32))
    (hpb : s.pendingBranch = none)
    (ha : readReg s (regIdxSpec 8#32) = 0x7fffffff#32)
    (hb : readReg s (regIdxSpec 9#32) = 1#32) :
    step p s = StepResult.next (exceptionEntry s excCodeOv) ∧
      (exceptionEntry s excCodeOv).regs = s.regs := by
  refine ⟨?_, rfl⟩
  rw [add_spec_raw p s w 8#32 9#32 10#32 hfetch hdecode hpb]
  dsimp only
  rw [ha, hb]
  rfl

-- Concrete witness: `0x7fffffff + 1` raises Integer Overflow (ExcCode 12 at
-- the exception vector, `EPC` = the `add`), and `$10` keeps its old value.
#guard (match step (prog1Spec (.add 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x7fffffff#32), (9, 1#32), (10, 0x55#32)]) with
        | .next s' => causeExcCode s' == excCodeOv && s'.pc == exceptionVectorAddr
            && s'.cp0Epc == textBase && readReg s' 10 == 0x55#32
        | .halt _ => false) = true

/-- **A write to `$zero` is never observable.** No matter what value gets
"written" to register `0`, reading it straight back always gives `0` —
exactly INSTRUCTION-REF Global rule 2, stated as a rejection of the bad
behavior "the write took effect". -/
theorem zero_write_not_observable (s : State) (v : W32) (hv : readReg s 0 ≠ v) :
    readReg (writeReg s 0 v) 0 ≠ v := by
  rw [writeReg_preserves_zero_slot]
  exact hv

#guard decide (readReg (writeReg (initialState textBase) 0 0xdeadbeef#32) 0 ≠ 0xdeadbeef#32) = true

/-- **A misaligned `lw` never loads.** A buggy implementation might round
the address down (or up) and load anyway; the real `lw` raises Address
Error (AdEL) on a misaligned effective address: the step is exactly
exception entry with `BadVAddr` = that address, and no general register —
in particular `$rt` — is written. (Formerly `lw_misaligned_no_next`, from
when address errors were modeled as halts.) -/
theorem lw_misaligned_no_load (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none)
    (hmisaligned : (readReg s (regIdxSpec rs) + signExt16 imm).toNat % 4 ≠ 0) :
    ∃ s', step p s = StepResult.next s' ∧ s'.regs = s.regs ∧
      s'.cp0BadVAddr = readReg s (regIdxSpec rs) + signExt16 imm := by
  rw [lw_misaligned_spec p s w rs rt imm hfetch hdecode hpb hmisaligned]
  exact ⟨_, rfl, rfl, rfl⟩

-- Concrete witness: `lw` from a `+1`-misaligned address raises AdEL with
-- `BadVAddr` = the address; `$9` is not written.
#guard (match step (prog1Spec (.lw 8#32 9#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0x55#32)]) with
        | .next s' => causeExcCode s' == excCodeAdEL && s'.cp0BadVAddr == 0x10010001#32
            && readReg s' 9 == 0x55#32 && s'.pc == exceptionVectorAddr
        | .halt _ => false) = true

/-! ## Group 5 — R-type logic/compare specs (`addu`,`subu`,`and`,`or`,`xor`,
`nor`,`slt`,`sltu`,`movn`,`movz`)

These ten R-type instructions round out Group 2's arithmetic/logic coverage.
`addu`/`subu` are `add`/`sub` with the overflow trap removed entirely — plain
two's-complement wraparound, never a halt (INSTRUCTION-REF "addu"/"subu"
sections). `and`/`or`/`xor`/`nor` are the four bitwise ops, with no overflow
concept whatsoever (INSTRUCTION-REF "and"/"or"/"xor"/"nor" sections).
`slt`/`sltu` write a `0`/`1` comparison result, signed vs. unsigned
(INSTRUCTION-REF "slt"/"sltu" sections). `movn`/`movz` are MIPS32r2
conditional moves whose defining feature — `$rd` left genuinely untouched
(not zeroed) when the condition fails — is exactly what the corollaries
after their raw specs pin down, per this project's CLAUDE.md §4 ("the spec
must reject bad behaviour"): a buggy always-overwrite implementation would
fail `movn_not_taken_unchanged`/`movz_not_taken_unchanged` below. -/

/-- **`addu` computes `$rs + $rt` with plain wraparound and never traps** —
same formula as `add_spec_raw` minus the overflow check entirely
(INSTRUCTION-REF "addu" section). -/
theorem addu_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.addu rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let sumBV := readReg s (regIdxSpec rs) + readReg s (regIdxSpec rt)
      StepResult.next
        { (writeReg s (regIdxSpec rd) sumBV) with
          pc := (writeReg s (regIdxSpec rd) sumBV).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`subu` computes `$rs - $rt` with plain wraparound and never traps**
(INSTRUCTION-REF "subu" section). -/
theorem subu_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.subu rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let diffBV := readReg s (regIdxSpec rs) - readReg s (regIdxSpec rt)
      StepResult.next
        { (writeReg s (regIdxSpec rd) diffBV) with
          pc := (writeReg s (regIdxSpec rd) diffBV).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`and` computes the bitwise AND of `$rs`/`$rt`** — no overflow concept
at all (INSTRUCTION-REF "and" section). -/
theorem and_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.and rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := readReg s (regIdxSpec rs) &&& readReg s (regIdxSpec rt)
      StepResult.next
        { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`or` computes the bitwise OR of `$rs`/`$rt`** (INSTRUCTION-REF "or"
section). -/
theorem or_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.or rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := readReg s (regIdxSpec rs) ||| readReg s (regIdxSpec rt)
      StepResult.next
        { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`xor` computes the bitwise XOR of `$rs`/`$rt`** (INSTRUCTION-REF "xor"
section). -/
theorem xor_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.xor rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := readReg s (regIdxSpec rs) ^^^ readReg s (regIdxSpec rt)
      StepResult.next
        { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`nor` computes the bitwise NOR (`~($rs | $rt)`) of `$rs`/`$rt`**
(INSTRUCTION-REF "nor" section). -/
theorem nor_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.nor rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := ~~~(readReg s (regIdxSpec rs) ||| readReg s (regIdxSpec rt))
      StepResult.next
        { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`slt` writes `1` to `$rd` iff `$rs < $rt` as a signed comparison, else
`0`** (INSTRUCTION-REF "slt" section). -/
theorem slt_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.slt rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := if asSigned (readReg s (regIdxSpec rs)) < asSigned (readReg s (regIdxSpec rt))
               then 1#32 else 0#32
      StepResult.next
        { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`sltu` writes `1` to `$rd` iff `$rs < $rt` as an unsigned comparison,
else `0`** (INSTRUCTION-REF "sltu" section). -/
theorem sltu_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sltu rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := if (readReg s (regIdxSpec rs)).toNat < (readReg s (regIdxSpec rt)).toNat
               then 1#32 else 0#32
      StepResult.next
        { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`movn` moves `$rs` into `$rd` iff `$rt ≠ 0`; otherwise `$rd` is left
completely unchanged** — a true conditional no-op, not "write `0`"
(INSTRUCTION-REF "movn" section). This is the full case split; see
`movn_taken_spec`/`movn_not_taken_spec`/`movn_not_taken_unchanged` below for
the two branches isolated. -/
theorem movn_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movn rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rt) != 0#32 then
        StepResult.next
          { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs))) with
            pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs))).pc + 4#32 }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`movn`, condition true (`$rt ≠ 0`)**: `$rd` actually receives `$rs`'s
value. -/
theorem movn_taken_spec (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movn rs rt rd))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rt) ≠ 0#32) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs))) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs))).pc + 4#32 } := by
  rw [movn_spec_raw p s w rs rt rd hfetch hdecode hpb, ite_of_pos (by simpa using htaken)]

/-- **`movn`, condition false (`$rt = 0`)**: the state advances with no
register write at all — `$rd` is not touched, not zeroed. -/
theorem movn_not_taken_spec (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movn rs rt rd))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rt) = 0#32) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [movn_spec_raw p s w rs rt rd hfetch hdecode hpb, ite_of_neg (by simp [hnot])]

/-- **"Bad output rejection" for `movn`**: whenever the condition fails
(`$rt = 0`), the resulting state's `$rd` reads back *exactly* its pre-step
value — a buggy implementation that always overwrote `$rd` regardless of
`$rt` could never satisfy this. -/
theorem movn_not_taken_unchanged (p : Program) (s s' : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movn rs rt rd))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rt) = 0#32)
    (hstep : step p s = StepResult.next s') :
    readReg s' (regIdxSpec rd) = readReg s (regIdxSpec rd) := by
  rw [movn_not_taken_spec p s w rs rt rd hfetch hdecode hpb hnot] at hstep
  injection hstep with hs
  rw [← hs]
  rfl

/-- **`movz` moves `$rs` into `$rd` iff `$rt = 0`; otherwise `$rd` is left
completely unchanged** — the mirror image of `movn` (INSTRUCTION-REF "movz"
section). -/
theorem movz_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movz rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rt) == 0#32 then
        StepResult.next
          { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs))) with
            pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs))).pc + 4#32 }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`movz`, condition true (`$rt = 0`)**: `$rd` actually receives `$rs`'s
value. -/
theorem movz_taken_spec (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movz rs rt rd))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rt) = 0#32) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs))) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs))).pc + 4#32 } := by
  rw [movz_spec_raw p s w rs rt rd hfetch hdecode hpb, ite_of_pos (by simpa using htaken)]

/-- **`movz`, condition false (`$rt ≠ 0`)**: the state advances with no
register write at all. -/
theorem movz_not_taken_spec (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movz rs rt rd))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rt) ≠ 0#32) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [movz_spec_raw p s w rs rt rd hfetch hdecode hpb, ite_of_neg (by simpa using hnot)]

/-- **"Bad output rejection" for `movz`**: whenever the condition fails
(`$rt ≠ 0`), the resulting state's `$rd` reads back *exactly* its pre-step
value — a buggy implementation that always overwrote `$rd` regardless of
`$rt` could never satisfy this. -/
theorem movz_not_taken_unchanged (p : Program) (s s' : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movz rs rt rd))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rt) ≠ 0#32)
    (hstep : step p s = StepResult.next s') :
    readReg s' (regIdxSpec rd) = readReg s (regIdxSpec rd) := by
  rw [movz_not_taken_spec p s w rs rt rd hfetch hdecode hpb hnot] at hstep
  injection hstep with hs
  rw [← hs]
  rfl

/-! ### Group 5 — satisfiable examples

Same technique as Group 3: each theorem above is instantiated on a concrete
program/state with every hypothesis discharged. -/

-- `addu_spec_raw`: `0xffffffff + 2` wraps to `1`, with no trap (unlike
-- `add`, which would halt on this operand pair's signed overflow reading).
#guard (match step (prog1Spec (.addu 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 2#32)]) with
        | .next s => readReg s 10 == 1#32
        | .halt _ => false) = true

-- `subu_spec_raw`: `0 - 1` wraps to `0xffffffff`, with no trap.
#guard (match step (prog1Spec (.subu 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0#32), (9, 1#32)]) with
        | .next s => readReg s 10 == 0xffffffff#32
        | .halt _ => false) = true

-- `and_spec_raw`/`or_spec_raw`/`xor_spec_raw`/`nor_spec_raw`.
#guard (match step (prog1Spec (.and 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)]) with
        | .next s => readReg s 10 == 0x0f000f00#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.or 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)]) with
        | .next s => readReg s 10 == 0xff0fff0f#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.xor 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)]) with
        | .next s => readReg s 10 == 0xf00ff00f#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.nor 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0#32), (9, 0#32)]) with
        | .next s => readReg s 10 == 0xffffffff#32
        | .halt _ => false) = true

-- `slt_spec_raw`/`sltu_spec_raw`: the same bit pattern (`0xffffffff`, i.e.
-- `-1` signed) compares differently against `1` under signed vs. unsigned
-- interpretation.
#guard (match step (prog1Spec (.slt 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)]) with
        | .next s => readReg s 10 == 1#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.sltu 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)]) with
        | .next s => readReg s 10 == 0#32
        | .halt _ => false) = true

-- `movn_taken_spec`/`movn_not_taken_unchanged`: `$rd` pre-seeded with the
-- sentinel `99` is overwritten when `$rt ≠ 0`, and left at `99` (not
-- zeroed) when `$rt = 0`.
#guard (match step (prog1Spec (.movn 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 1#32), (10, 99#32)]) with
        | .next s => readReg s 10 == 5#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.movn 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 0#32), (10, 99#32)]) with
        | .next s => readReg s 10 == 99#32
        | .halt _ => false) = true

-- `movz_taken_spec`/`movz_not_taken_unchanged`: the mirror image of `movn`.
#guard (match step (prog1Spec (.movz 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 0#32), (10, 99#32)]) with
        | .next s => readReg s 10 == 5#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.movz 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 1#32), (10, 99#32)]) with
        | .next s => readReg s 10 == 99#32
        | .halt _ => false) = true

/-! ## Group 5 — shift/rotate instruction family

`sll`/`srl`/`sra`/`sllv`/`srlv`/`srav`/`rotr`/`rotrv` (INSTRUCTION-REF "R-type
shifts"/"R-type variable shifts"/"R-type rotate" sections,
docs/spec/MIPS-COVERAGE-GAPS.md §3.4). All eight are straight-line
computations — no memory access, no branch scheduling, no inner `match`/`if`
on an abstract register value — so each follows `add_spec_raw`'s exact proof
recipe. -/

/-- **`sll` shifts `$rt` left by the fixed `shamt` field, zero-filling the
vacated low bits.** `shamt` comes straight from the instruction encoding
(INSTRUCTION-REF "sll"), not a register. -/
theorem sll_spec_raw (p : Program) (s : State) (w rd rt shamt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sll rd rt shamt))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< shamt.toNat)) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< shamt.toNat)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`srl` shifts `$rt` right by the fixed `shamt` field, zero-filling the
vacated high bits (logical shift).** Mirrors `sll_spec_raw`; see `sra_spec_raw`
for the sign-filling counterpart. -/
theorem srl_spec_raw (p : Program) (s : State) (w rd rt shamt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.srl rd rt shamt))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) >>> shamt.toNat)) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) >>> shamt.toNat)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`sra` shifts `$rt` right by the fixed `shamt` field, sign-filling the
vacated high bits (arithmetic shift).** Uses `BitVec.sshiftRight`, the same
helper `step` itself uses, so a negative `$rt` keeps its sign after the
shift (INSTRUCTION-REF "sra"). -/
theorem sra_spec_raw (p : Program) (s : State) (w rd rt shamt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sra rd rt shamt))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).sshiftRight shamt.toNat)) with
          pc := (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).sshiftRight shamt.toNat)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`sllv` shifts `$rt` left by `$rs`'s low 5 bits**, not a fixed `shamt`
field — so a shift-amount register holding e.g. `33` (`0b100001`) behaves
identically to one holding `1` (INSTRUCTION-REF "sllv",
docs/spec/MIPS-COVERAGE-GAPS.md §3.4). `extractLsb 4 0` is the exact masking
expression `step` itself uses. -/
theorem sllv_spec_raw (p : Program) (s : State) (w rd rt rs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sllv rd rt rs))
    (hpb : s.pendingBranch = none) :
    step p s =
      let amt := ((readReg s (regIdxSpec rs)).extractLsb 4 0).toNat
      StepResult.next
        { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< amt)) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< amt)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`srlv` shifts `$rt` right (zero-filling) by `$rs`'s low 5 bits.**
Mirrors `sllv_spec_raw`'s masking; logical (not arithmetic) shift, same as
`srl`. -/
theorem srlv_spec_raw (p : Program) (s : State) (w rd rt rs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.srlv rd rt rs))
    (hpb : s.pendingBranch = none) :
    step p s =
      let amt := ((readReg s (regIdxSpec rs)).extractLsb 4 0).toNat
      StepResult.next
        { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) >>> amt)) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) >>> amt)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`srav` shifts `$rt` right (sign-filling) by `$rs`'s low 5 bits.**
Mirrors `sllv_spec_raw`'s masking and `sra_spec_raw`'s sign-fill. -/
theorem srav_spec_raw (p : Program) (s : State) (w rd rt rs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.srav rd rt rs))
    (hpb : s.pendingBranch = none) :
    step p s =
      let amt := ((readReg s (regIdxSpec rs)).extractLsb 4 0).toNat
      StepResult.next
        { (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).sshiftRight amt)) with
          pc := (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).sshiftRight amt)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`rotr` rotates `$rt` right by the fixed `sa` field, wrapping bits
shifted off the bottom around to the top** (MIPS32r2; INSTRUCTION-REF "rotr",
docs/spec/MIPS-COVERAGE-GAPS.md §3.4) — unlike `srl`'s zero-fill on the same
input. `BitVec.rotateRight` is the exact operation `step` itself uses. -/
theorem rotr_spec_raw (p : Program) (s : State) (w rd rt sa : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.rotr rd rt sa))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).rotateRight sa.toNat)) with
          pc := (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).rotateRight sa.toNat)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`rotrv` rotates `$rt` right by `$rs`'s low 5 bits, wrapping around**
(MIPS32r2; INSTRUCTION-REF "rotrv"). Same masking as `sllv`/`srlv`/`srav`,
same wrap-around as `rotr`. -/
theorem rotrv_spec_raw (p : Program) (s : State) (w rd rt rs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.rotrv rd rt rs))
    (hpb : s.pendingBranch = none) :
    step p s =
      let amt := ((readReg s (regIdxSpec rs)).extractLsb 4 0).toNat
      StepResult.next
        { (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).rotateRight amt)) with
          pc := (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).rotateRight amt)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- Satisfiable examples: `sll`/`srl`/`sra` at shamt 0 and 31 (sign-fill vs.
-- zero-fill at the boundary), mirroring `Step.lean`'s own `#guard`s.
#guard (match step (prog1Spec (.sll 10#32 8#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)]) with
        | .next s => readReg s 10 == 0x12345678#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.sll 10#32 8#32 31#32))
          (setRegsSpec (initialState textBase) [(8, 1#32)]) with
        | .next s => readReg s 10 == 0x80000000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.srl 10#32 8#32 31#32))
          (setRegsSpec (initialState textBase) [(8, 0x80000000#32)]) with
        | .next s => readReg s 10 == 1#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.sra 10#32 8#32 31#32))
          (setRegsSpec (initialState textBase) [(8, 0x80000000#32)]) with
        | .next s => readReg s 10 == 0xffffffff#32
        | .halt _ => false) = true

-- Satisfiable examples: `sllv`/`srlv`/`srav` masking a shift amount of 33
-- down to 1 (`33 & 0x1f = 1`).
#guard (match step (prog1Spec (.sllv 10#32 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 1#32), (9, 33#32)]) with
        | .next s => readReg s 10 == 2#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.srlv 10#32 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0x80000000#32), (9, 33#32)]) with
        | .next s => readReg s 10 == 0x40000000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.srav 10#32 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0x80000000#32), (9, 33#32)]) with
        | .next s => readReg s 10 == 0xc0000000#32
        | .halt _ => false) = true

-- Satisfiable examples: `rotr`/`rotrv`, including the masked-amount case
-- (`36 & 0x1f = 4`).
#guard (match step (prog1Spec (.rotr 10#32 8#32 4#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)]) with
        | .next s => readReg s 10 == 0x81234567#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.rotrv 10#32 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32), (9, 36#32)]) with
        | .next s => readReg s 10 == 0x81234567#32
        | .halt _ => false) = true

/-! ### Bad-output rejection: `rotr` genuinely wraps, it is not `srl` in
disguise

A buggy `rotr` implementation might secretly reuse `srl`'s zero-fill (e.g.
by forgetting to reinsert the shifted-out bits). The two theorems below pin
down the exact register `rotr` and `srl` each write for the *same* `$rt`
value and shift amount (`0x12345678` shifted/rotated by `4`), and the
following `decide` shows those two outputs are provably different values —
so the spec captures genuine wrap-around, not just "a rightward shift of
some kind happened". -/

theorem rotr_wraps_not_zero_fill (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.rotr 10#32 8#32 4#32))
    (hpb : s.pendingBranch = none)
    (hrt : readReg s (regIdxSpec 8#32) = 0x12345678#32) :
    step p s = StepResult.next
      { (writeReg s (regIdxSpec 10#32) 0x81234567#32) with
        pc := (writeReg s (regIdxSpec 10#32) 0x81234567#32).pc + 4#32 } := by
  rw [rotr_spec_raw p s w 10#32 8#32 4#32 hfetch hdecode hpb]
  dsimp only
  rw [hrt]
  rfl

theorem srl_zero_fills_same_input (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.srl 10#32 8#32 4#32))
    (hpb : s.pendingBranch = none)
    (hrt : readReg s (regIdxSpec 8#32) = 0x12345678#32) :
    step p s = StepResult.next
      { (writeReg s (regIdxSpec 10#32) 0x01234567#32) with
        pc := (writeReg s (regIdxSpec 10#32) 0x01234567#32).pc + 4#32 } := by
  rw [srl_spec_raw p s w 10#32 8#32 4#32 hfetch hdecode hpb]
  dsimp only
  rw [hrt]
  rfl

/-- **`rotr`'s wrap-around is not optional.** From the same state — the
same `$8 = 0x12345678`, the same shift amount 4 — `rotr` and `srl` step to
states whose `$10` provably differ: `0x81234567` (the low nibble wrapped to
the top) versus `0x01234567` (the low nibble discarded). -/
theorem rotr_output_ne_srl_output (p p' : Program) (s : State) (w w' : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.rotr 10#32 8#32 4#32))
    (hfetch' : fetchWord p' s.pc = some w') (hdecode' : decode w' = some (.srl 10#32 8#32 4#32))
    (hpb : s.pendingBranch = none) (hsize32 : s.regs.size = 32)
    (hrt : readReg s (regIdxSpec 8#32) = 0x12345678#32) :
    ∃ s1 s2, step p s = StepResult.next s1 ∧ step p' s = StepResult.next s2 ∧
      readReg s1 10 = 0x81234567#32 ∧ readReg s2 10 = 0x01234567#32 ∧
      readReg s1 10 ≠ readReg s2 10 := by
  have h1 : readReg (writeReg s (regIdxSpec 10#32) 0x81234567#32) 10 = 0x81234567#32 :=
    writeReg_reads_back s 10 _ (by decide) hsize32
  have h2 : readReg (writeReg s (regIdxSpec 10#32) 0x01234567#32) 10 = 0x01234567#32 :=
    writeReg_reads_back s 10 _ (by decide) hsize32
  refine ⟨_, _, rotr_wraps_not_zero_fill p s w hfetch hdecode hpb hrt,
    srl_zero_fills_same_input p' s w' hfetch' hdecode' hpb hrt, h1, h2, ?_⟩
  show readReg (writeReg s (regIdxSpec 10#32) 0x81234567#32) 10
    ≠ readReg (writeReg s (regIdxSpec 10#32) 0x01234567#32) 10
  rw [h1, h2]
  decide

-- Concrete witness tying the two facts together: running `rotr` and `srl`
-- on the same register contents and shift amount produces different
-- results in `$rd`.
#guard (match step (prog1Spec (.rotr 10#32 8#32 4#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)]) with
        | .next s => readReg s 10
        | .halt _ => 0#32) !=
        (match step (prog1Spec (.srl 10#32 8#32 4#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)]) with
        | .next s => readReg s 10
        | .halt _ => 0#32)

/-! ## Group 5 — multiply/divide and HI/LO-register family

The `mult`/`multu`/`divu`/`mflo`/`mfhi`/`mthi`/`mtlo`/`madd`/`maddu`/`msub`/
`msubu` instructions (`docs/spec/INSTRUCTION-REF.md` "Multiply / divide"
and "mthi (R)"/"mtlo (R)" sections). `div`/`div_by_zero_spec`/
`div_negative_dividend_spec` above are the house style this section
follows: every theorem is `step` restated with public names, proved by the
same `obtain`/`subst`/`unfold step`/`rw [hfetch]`/`rw [hdecode]`/`rfl`
recipe as `add_spec_raw`. -/

/-- **`mult` forms the exact signed 64-bit product of `$rs` and `$rt`,
splitting it into `hi`/`lo`.** No GPR is written, and `mult` never halts
(INSTRUCTION-REF "mult" section: MARS never traps on multiply overflow —
the full 64-bit result always fits in `hi:lo`). -/
theorem mult_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mult rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
      StepResult.next
        { s with lo := prod64.extractLsb 31 0, hi := prod64.extractLsb 63 32, pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`multu` forms the exact unsigned 64-bit product of `$rs` and `$rt`,
splitting it into `hi`/`lo`.** Mirrors `mult_spec_raw`, except both
operands are read as unsigned `Nat`s first (INSTRUCTION-REF "multu"
section). Never halts. -/
theorem multu_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.multu rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := (readReg s (regIdxSpec rs)).toNat
      let b := (readReg s (regIdxSpec rt)).toNat
      let prod64 : BitVec 64 := BitVec.ofNat 64 (a * b)
      StepResult.next
        { s with lo := prod64.extractLsb 31 0, hi := prod64.extractLsb 63 32, pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `mult_spec_raw`: `5 * 7 = 35` fits entirely in `lo`, `hi = 0`.
#guard (match step (prog1Spec (.mult 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with
        | .next s => s.lo == 35#32 && s.hi == 0#32
        | .halt _ => false) = true

-- `mult_spec_raw`: a negative times a positive operand gives a negative
-- 64-bit product, so `hi` is all-ones (sign-extension of the product).
#guard (match step (prog1Spec (.mult 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffe#32), (9, 5#32)]) with
        | .next s => s.lo == 0xfffffff6#32 && s.hi == 0xffffffff#32
        | .halt _ => false) = true

-- `multu_spec_raw`: the same bit pattern `0xfffffffe` is unsigned, so
-- `0xfffffffe * 5` overflows into a nonzero `hi` without any sign-extension.
#guard (match step (prog1Spec (.multu 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffe#32), (9, 5#32)]) with
        | .next s => s.lo == 0xfffffff6#32 && s.hi == 4#32
        | .halt _ => false) = true

/-- **`divu` by a nonzero divisor is ordinary unsigned division/remainder;
`divu` by zero leaves `hi`/`lo` untouched and does not halt.** Unsigned
counterpart of `div_spec_raw` (INSTRUCTION-REF "divu" section — same
by-zero-is-a-silent-no-op MARS deviation documented for `div`). Always
advances the program counter by 4. -/
theorem divu_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.divu rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := (readReg s (regIdxSpec rs)).toNat
      let b := (readReg s (regIdxSpec rt)).toNat
      if b == 0 then
        StepResult.next { s with pc := s.pc + 4#32 }
      else
        StepResult.next { s with lo := BitVec.ofNat 32 (a / b), hi := BitVec.ofNat 32 (a % b), pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Corollary of `divu_spec_raw`: dividing by `0` leaves `hi`/`lo` exactly
as they were and does not halt — the unsigned counterpart of
`div_by_zero_spec` (INSTRUCTION-REF "divu" section). -/
theorem divu_by_zero_spec (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.divu rs rt))
    (hpb : s.pendingBranch = none)
    (hzero : readReg s (regIdxSpec rt) = 0#32) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [divu_spec_raw p s w rs rt hfetch hdecode hpb, hzero]
  rfl

-- `divu_spec_raw`: `17u / 5u = 3` remainder `2`, ordinary unsigned division.
#guard (match step (prog1Spec (.divu 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 17#32), (9, 5#32)]) with
        | .next s => s.lo == 3#32 && s.hi == 2#32
        | .halt _ => false) = true

-- `divu_by_zero_spec`: dividing by `0` leaves a pre-seeded `hi`/`lo` alone,
-- the unsigned counterpart of the `div_by_zero_spec` example above.
#guard (match step (prog1Spec (.divu 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 10#32), (9, 0#32)]) with
            hi := 0x11#32, lo := 0x22#32 } with
        | .next s => s.lo == 0x22#32 && s.hi == 0x11#32
        | .halt _ => false) = true

/-- **`mflo` copies `lo` into `$rd`.** Trivial register read
(INSTRUCTION-REF "mflo" section); never halts. -/
theorem mflo_spec_raw (p : Program) (s : State) (w rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mflo rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) s.lo) with
          pc := (writeReg s (regIdxSpec rd) s.lo).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`mfhi` copies `hi` into `$rd`.** Trivial register read
(INSTRUCTION-REF "mfhi" section); never halts. -/
theorem mfhi_spec_raw (p : Program) (s : State) (w rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mfhi rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) s.hi) with
          pc := (writeReg s (regIdxSpec rd) s.hi).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`mthi` copies `$rs` into `hi`; `lo` is left unchanged.** Write-direction
counterpart to `mfhi_spec_raw` (INSTRUCTION-REF "mthi (R)" section); no GPR
is written, never halts. -/
theorem mthi_spec_raw (p : Program) (s : State) (w rs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mthi rs))
    (hpb : s.pendingBranch = none) :
    step p s = StepResult.next { s with hi := readReg s (regIdxSpec rs), pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`mtlo` copies `$rs` into `lo`; `hi` is left unchanged.** Write-direction
counterpart to `mflo_spec_raw` (INSTRUCTION-REF "mtlo (R)" section); no GPR
is written, never halts. -/
theorem mtlo_spec_raw (p : Program) (s : State) (w rs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mtlo rs))
    (hpb : s.pendingBranch = none) :
    step p s = StepResult.next { s with lo := readReg s (regIdxSpec rs), pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **Round-trip check: `mthi` immediately followed by `mfhi` recovers
`$rs`'s original value through `hi`.** This is the "the half-pair actually
composes" check for `mthi`/`mfhi`: it is not enough for each instruction to
close on its own — writing `hi := $rs` and then reading `$rd := hi` two
steps later must produce exactly the value `$rs` held *before* either
instruction ran. Needs `regIdxSpec rd ≠ 0` (a write to `$zero` is a no-op,
INSTRUCTION-REF Global rule 2) and `s.regs.size = 32` (`writeReg_reads_back`'s
side condition, guaranteed by `initialState` — `State.lean`). -/
theorem mthi_mfhi_round_trip (p : Program) (s : State) (w w2 rs rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mthi rs))
    (hpb : s.pendingBranch = none)
    (hfetch2 : fetchWord p (s.pc + 4#32) = some w2) (hdecode2 : decode w2 = some (.mfhi rd))
    (hrd : regIdxSpec rd ≠ 0) (hsize32 : s.regs.size = 32) :
    ∃ s1 s2,
      step p s = StepResult.next s1 ∧
      step p s1 = StepResult.next s2 ∧
      readReg s2 (regIdxSpec rd) = readReg s (regIdxSpec rs) := by
  have h1 := mthi_spec_raw p s w rs hfetch hdecode hpb
  have h2 := mfhi_spec_raw p { s with hi := readReg s (regIdxSpec rs), pc := s.pc + 4#32 } w2 rd
    hfetch2 hdecode2 hpb
  refine ⟨_, _, h1, h2, ?_⟩
  exact writeReg_reads_back _ (regIdxSpec rd) _ hrd hsize32

-- `mthi_spec_raw`/`mfhi_spec_raw` concrete witness, standalone: `mthi` sets
-- `hi` from `$t0`, `mfhi` reads it back into `$t1`.
#guard (match step (prog1Spec (.mthi 8#32)) (setRegsSpec (initialState textBase) [(8, 0x2a#32)]) with
        | .next s => s.hi == 0x2a#32 && s.lo == 0#32
        | .halt _ => false) = true

-- `mtlo_spec_raw` concrete witness: `mtlo` sets `lo` from `$t0`, `hi`
-- untouched.
#guard (match step (prog1Spec (.mtlo 8#32)) (setRegsSpec (initialState textBase) [(8, 0x2a#32)]) with
        | .next s => s.lo == 0x2a#32 && s.hi == 0#32
        | .halt _ => false) = true

-- `mthi_mfhi_round_trip` concrete witness: `mthi $t0; mfhi $t1` leaves
-- `$t1` holding exactly `$t0`'s original value.
#guard (match step (buildProgSpec textBase [.mthi 8#32, .mfhi 9#32])
          (setRegsSpec (initialState textBase) [(8, 0x2a#32)]) with
        | .next s1 =>
          (match step (buildProgSpec textBase [.mthi 8#32, .mfhi 9#32]) s1 with
           | .next s2 => readReg s2 9 == 0x2a#32
           | .halt _ => false)
        | .halt _ => false) = true

/-- **`madd` adds the signed 64-bit product of `$rs`/`$rt` onto the
EXISTING `{hi,lo}` accumulator — it does not overwrite it.** The addend is
`s.hi ++ s.lo` (the 64-bit value already sitting in the accumulator
*before* this instruction runs), reassembled exactly as `Step.lean` does
and genuinely used as one operand of the `+` below, not discarded
(INSTRUCTION-REF "madd (R, SPECIAL2)" section). The 64-bit add wraps on
overflow, matching `mult`'s non-trapping precedent; never halts. -/
theorem madd_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.madd rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
      let acc64 : BitVec 64 := s.hi ++ s.lo
      let sum64 := acc64 + prod64
      StepResult.next
        { s with lo := sum64.extractLsb 31 0, hi := sum64.extractLsb 63 32, pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`maddu` adds the unsigned 64-bit product of `$rs`/`$rt` onto the
EXISTING `{hi,lo}` accumulator.** Unsigned counterpart of `madd_spec_raw`
(INSTRUCTION-REF "maddu (R, SPECIAL2)" section); same "accumulate, don't
overwrite" shape — `acc64` is built from `s.hi`/`s.lo` as they stood before
this instruction ran. Never halts. -/
theorem maddu_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.maddu rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := (readReg s (regIdxSpec rs)).toNat
      let b := (readReg s (regIdxSpec rt)).toNat
      let prod64 : BitVec 64 := BitVec.ofNat 64 (a * b)
      let acc64 : BitVec 64 := s.hi ++ s.lo
      let sum64 := acc64 + prod64
      StepResult.next
        { s with lo := sum64.extractLsb 31 0, hi := sum64.extractLsb 63 32, pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`msub` subtracts the signed 64-bit product of `$rs`/`$rt` from the
EXISTING `{hi,lo}` accumulator — it does not overwrite it.** Same
accumulator-reassembly shape as `madd_spec_raw`, but `acc64 - prod64`
instead of `acc64 + prod64` (INSTRUCTION-REF "msub (R, SPECIAL2)" section).
Wraps on underflow; never halts. -/
theorem msub_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.msub rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
      let acc64 : BitVec 64 := s.hi ++ s.lo
      let diff64 := acc64 - prod64
      StepResult.next
        { s with lo := diff64.extractLsb 31 0, hi := diff64.extractLsb 63 32, pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`msubu` subtracts the unsigned 64-bit product of `$rs`/`$rt` from the
EXISTING `{hi,lo}` accumulator.** Unsigned counterpart of `msub_spec_raw`
(INSTRUCTION-REF "msubu (R, SPECIAL2)" section); same accumulate-not-
overwrite shape. Never halts. -/
theorem msubu_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.msubu rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := (readReg s (regIdxSpec rs)).toNat
      let b := (readReg s (regIdxSpec rt)).toNat
      let prod64 : BitVec 64 := BitVec.ofNat 64 (a * b)
      let acc64 : BitVec 64 := s.hi ++ s.lo
      let diff64 := acc64 - prod64
      StepResult.next
        { s with lo := diff64.extractLsb 31 0, hi := diff64.extractLsb 63 32, pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `madd_spec_raw`: a pre-seeded accumulator of `{hi=0,lo=100}` plus
-- `5 * 7 = 35` gives `135`, i.e. the existing `lo` value is genuinely an
-- addend, not discarded.
#guard (match step (prog1Spec (.madd 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with hi := 0#32, lo := 100#32 } with
        | .next s => s.lo == 135#32 && s.hi == 0#32
        | .halt _ => false) = true

-- `maddu_spec_raw`: same pre-seeded accumulator, unsigned product.
#guard (match step (prog1Spec (.maddu 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with hi := 0#32, lo := 100#32 } with
        | .next s => s.lo == 135#32 && s.hi == 0#32
        | .halt _ => false) = true

-- `msub_spec_raw`: a pre-seeded accumulator of `{hi=0,lo=100}` minus
-- `5 * 7 = 35` gives `65`, i.e. the existing `lo` value is genuinely a
-- minuend, not discarded.
#guard (match step (prog1Spec (.msub 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with hi := 0#32, lo := 100#32 } with
        | .next s => s.lo == 65#32 && s.hi == 0#32
        | .halt _ => false) = true

-- `msubu_spec_raw`: same pre-seeded accumulator, unsigned product.
#guard (match step (prog1Spec (.msubu 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with hi := 0#32, lo := 100#32 } with
        | .next s => s.lo == 65#32 && s.hi == 0#32
        | .halt _ => false) = true

/-! ## Group 5 — remaining memory instructions (`sw`, `lh`, `lhu`, `sh`, `ll`, `sc`)

Same `lw`/`lb`/`lbu`-style raw specs (Group 2), for the rest of the memory
instruction set. Each one restates its `step` case with public names
(`readMemHalf`/`writeMemWord`/`writeMemHalf`, …), halting with
Address Error on a misaligned effective address exactly like `lw`/`lb` do,
and is backed by a concrete `#guard` witness in the same style as Group 3.

`lwl`/`lwr`/`swl`/`swr` (the unaligned-load/store family) are covered
separately, in the dedicated `## Group 7` section at the end of this file --
they need their own two mirrored helpers (`setByteSlotSpec`/`getByteSlotSpec`)
before their `step` cases can be restated, so they do not fit this group's
plain `readMemHalf`/`writeMemWord`/`writeMemHalf` vocabulary. -/

/-- **`sw` stores `$rt` as a big-endian word at `$rs + sext16(offset)` and
clears `llBit`** (any store invalidates a pending `ll`/`sc` pair, so a
subsequent `sc` correctly fails if memory changed underneath it), or raises
Address Error on a misaligned effective address (INSTRUCTION-REF "sw"
section). -/
theorem sw_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemWord s addr (readReg s (regIdxSpec rt)) with
      | none => takeAddressException s excCodeAdES addr
      | some s' =>
        StepResult.next
          { ({ s' with llBit := false }) with
            pc := ({ s' with llBit := false }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`sh` stores the low 16 bits of `$rt` as a big-endian halfword at
`$rs + sext16(offset)` and clears `llBit`**, or raises Address Error
on a halfword-misaligned effective address (INSTRUCTION-REF "sh" section).
-/
theorem sh_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sh rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemHalf s addr (readReg s (regIdxSpec rt)) with
      | none => takeAddressException s excCodeAdES addr
      | some s' =>
        StepResult.next
          { ({ s' with llBit := false }) with
            pc := ({ s' with llBit := false }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`sb` stores the low byte of `$rt` at `$rs + sext16(offset)` and
clears `llBit`** (MD00086 "SB": `StoreMemory(BYTE, GPR[rt] 7..0)`). There is
no alignment requirement, so `sb` never raises an Address Error; exactly
one memory byte changes. Clearing `llBit` is the model's pinned choice for
every store (see `State.llBit`). -/
theorem sb_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sb rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { s with
            mem := s.mem.insert (readReg s (regIdxSpec rs) + signExt16 imm)
              (readReg s (regIdxSpec rt) &&& 0xff#32).toNat.toUInt8
            llBit := false
            pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `sb_spec_raw`: `sb $9, 1($8)` writes exactly the low byte `0xab` at the
-- (odd) address, leaves its neighbours alone, and clears `llBit`.
#guard (match step (prog1Spec (.sb 8#32 9#32 1#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0x123456ab#32)]) with llBit := true } with
        | .next s => readMemByte s 0x10010001#32 == some 0xab && readMemByte s 0x10010000#32 == some 0
            && readMemByte s 0x10010002#32 == some 0 && s.llBit == false && s.pc == textBase + 4#32
        | .halt _ => false) = true
-- the assembled word `0xa1090001` is `sb $9, 1($8)`.
example : decode 0xa1090001#32 = some (.sb 8#32 9#32 1#32) := by decide

/-- **`ll` loads a word exactly like `lw`, and additionally sets `llBit`
and records its effective address in `llAddr`** — the link state that a
later `sc` checks (INSTRUCTION-REF "ll" section; MD00086 Vol II-A Rev 6.06,
LL, p.223-224). It raises Address Error on a word-misaligned effective
address, exactly like `lw`. -/
theorem ll_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ll rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v =>
        StepResult.next
          { ({ (writeReg s (regIdxSpec rt) v) with llBit := true, llAddr := addr }) with
            pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`sc` is conditional on `llBit` and on its address matching the
preceding `ll`'s, checked before `llBit` is cleared.** The effective address
is computed and alignment-checked unconditionally, just like `sw` (so a
misaligned `sc` raises Address Error regardless of `llBit`). Once the
address is valid: if `s.llBit` was `true` **and** the address equals
`s.llAddr` ("An SC will fail if the aligned address of the SC does not match
that of the preceding LL" — MD00086 Vol II-A Rev 6.06, SC, p.347), the store
commits (`$rt`'s old value is written to memory) and `$rt` is overwritten
with `1` (success); otherwise the store does **not** commit and `$rt` is
overwritten with `0` (failure). Either way `llBit`
ends up `false`. This single theorem states both outcomes together
(mirroring how `beq_spec_raw` states taken/not-taken as one `if`), because
the whole point of `ll`/`sc` is this exact atomic-primitive contract, not
just "some memory operation happened" (INSTRUCTION-REF "sc" section). -/
theorem sc_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sc rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemWord s addr (readReg s (regIdxSpec rt)) with
      | none => takeAddressException s excCodeAdES addr
      | some stored =>
        if s.llBit && s.llAddr == addr then
          StepResult.next
            { ({ (writeReg stored (regIdxSpec rt) 1#32) with llBit := false }) with
              pc := ({ (writeReg stored (regIdxSpec rt) 1#32) with llBit := false }).pc + 4#32 }
        else
          StepResult.next
            { ({ (writeReg s (regIdxSpec rt) 0#32) with llBit := false }) with
              pc := ({ (writeReg s (regIdxSpec rt) 0#32) with llBit := false }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `sw_spec_raw`: a stored word reads back exactly, and clears a
-- previously-set `llBit`.
#guard (match step (prog1Spec (.sw 8#32 9#32 0#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0x12345678#32)]) with
            llBit := true } with
        | .next s => readMemWord s 0x10010000#32 == some 0x12345678#32 && s.llBit == false
        | .halt _ => false) = true

-- `sw_spec_raw`: a misaligned `sw` raises Address Error, it never
-- rounds the address and stores anyway.
#guard (match step (prog1Spec (.sw 8#32 9#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0x10010000#32)]) with
        | .next s' => s'.cp0BadVAddr == 0x10010001#32 && s'.pc == exceptionVectorAddr
        | .halt _ => false) = true

-- `lh_spec_raw`/`lhu_spec_raw`: the same high-bit halfword sign-extends under `lh`
-- and zero-extends under `lhu`.
#guard (match (writeMemHalf (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
          0x10010000#32 0x8001#32).bind
          (fun s => some (step (prog1Spec (.lh 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0xffff8001#32
        | _ => false) = true
#guard (match (writeMemHalf (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
          0x10010000#32 0x8001#32).bind
          (fun s => some (step (prog1Spec (.lhu 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0x00008001#32
        | _ => false) = true

-- `sh_spec_raw`: only the low 16 bits of `$rt` are stored, and `llBit` is
-- cleared.
#guard (match step (prog1Spec (.sh 8#32 9#32 0#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0xffff1234#32)]) with
            llBit := true } with
        | .next s => readMemHalf s 0x10010000#32 == some 0x00001234#32 && s.llBit == false
        | .halt _ => false) = true

-- `ll_spec_raw`: loads like `lw` and sets `llBit`.
#guard (match (writeMemWord (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
          0x10010000#32 0x2a#32).bind
          (fun s => some (step (prog1Spec (.ll 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0x2a#32 && s.llBit == true
        | _ => false) = true

-- `sc_spec_raw`, success case: `llBit` set means the store commits and
-- `$rt` becomes `1`.
#guard (match step (prog1Spec (.sc 8#32 9#32 0#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0x99#32)]) with
            llBit := true, llAddr := 0x10010000#32 } with
        | .next s =>
          readReg s 9 == 1#32 && s.llBit == false && readMemWord s 0x10010000#32 == some 0x99#32
        | .halt _ => false) = true

-- `sc_spec_raw`, address mismatch: `llBit` is set but the preceding `ll` was
-- to another address, so the store does NOT commit and `$rt` becomes `0`.
#guard (match step (prog1Spec (.sc 8#32 9#32 0#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0x99#32)]) with
            llBit := true, llAddr := 0x10010004#32 } with
        | .next s =>
          readReg s 9 == 0#32 && s.llBit == false && readMemWord s 0x10010000#32 == some 0#32
        | .halt _ => false) = true

-- `sc_spec_raw`, failure case: `llBit` clear means the store does NOT
-- commit (memory stays `0`) and `$rt` becomes `0`.
#guard (match step (prog1Spec (.sc 8#32 9#32 0#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0x99#32)]) with
            llBit := false } with
        | .next s =>
          readReg s 9 == 0#32 && s.llBit == false && readMemWord s 0x10010000#32 == some 0#32
        | .halt _ => false) = true

-- `sc_spec_raw`: a misaligned `sc` raises Address Error regardless of
-- `llBit` (the alignment check is unconditional).
#guard (match step (prog1Spec (.sc 8#32 9#32 1#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32)]) with llBit := true } with
        | .next s' => s'.cp0BadVAddr == 0x10010001#32 && s'.pc == exceptionVectorAddr
        | .halt _ => false) = true

/-! ## Group 5 — remaining branch/jump instructions: `blez`/`bgtz`, `j`,
`jr`/`jalr`, and the REGIMM zero-comparison family `bltz`/`bgez`/`bltzal`/
`bgezal`

Same recipe as `beq_spec_raw`/`bne_spec_raw`/`jal_spec_raw` above: each
`_spec_raw` theorem restates one `step` case as a single equation (an
`if ... then ... else ...` for the conditional branches, a plain
`StepResult.next` for the unconditional jumps), proved by destructuring `s`,
`unfold step`, rewriting in the concrete `hfetch`/`hdecode` hypotheses, and
closing with `rfl`. Taken/not-taken corollaries then follow from the raw
spec by `ite_of_pos`/`ite_of_neg` in one line each, exactly like
`beq_taken_spec`/`beq_not_taken_spec`. -/

/-- **`blez` branch target and condition** — single-register comparison
against zero, otherwise identical delay-slot shape to `beq`/`bne`: if
`$rs ≤ 0` (signed, zero included), schedules `PC = PC_next + (offset << 2)`
via `pendingBranch` and itself falls through to `PC_next`; otherwise it is
an ordinary fallthrough with no scheduled transfer (INSTRUCTION-REF "blez"
section). -/
theorem blez_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.blez rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) ≤ 0 then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`blez`, taken**: when `$rs ≤ 0`, schedules `PC_next + (offset << 2)`
as the delay-slot transfer and falls through to `PC_next` first — same
one-delay-slot discipline as `beq` (INSTRUCTION-REF "blez" section). -/
theorem blez_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.blez rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : asSigned (readReg s (regIdxSpec rs)) ≤ 0) :
    step p s = StepResult.next
      { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [blez_spec_raw p s w rs imm hfetch hdecode hpb, ite_of_pos htaken]

/-- **`blez`, not taken**: when `$rs > 0`, falls through to `PC_next` with
no scheduled transfer. -/
theorem blez_not_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.blez rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : 0 < asSigned (readReg s (regIdxSpec rs))) :
    step p s = StepResult.next { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  rw [blez_spec_raw p s w rs imm hfetch hdecode hpb, ite_of_neg (by omega)]

/-- **`bgtz` branch target and condition** — the mirror image of `blez`:
if `$rs > 0` (signed, strictly positive), schedules
`PC = PC_next + (offset << 2)`, same one-delay-slot discipline
(INSTRUCTION-REF "bgtz" section). -/
theorem bgtz_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgtz rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if 0 < asSigned (readReg s (regIdxSpec rs)) then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bgtz`, taken**: when `$rs > 0`, schedules `PC_next + (offset << 2)`
as the delay-slot transfer. -/
theorem bgtz_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgtz rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : 0 < asSigned (readReg s (regIdxSpec rs))) :
    step p s = StepResult.next
      { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bgtz_spec_raw p s w rs imm hfetch hdecode hpb, ite_of_pos htaken]

/-- **`bgtz`, not taken**: when `$rs ≤ 0`, falls through to `PC_next` with
no scheduled transfer. -/
theorem bgtz_not_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgtz rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : asSigned (readReg s (regIdxSpec rs)) ≤ 0) :
    step p s = StepResult.next { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  rw [bgtz_spec_raw p s w rs imm hfetch hdecode hpb, ite_of_neg (by omega)]

/-- **`j` unconditionally schedules a jump whose top 4 bits come from
`PC_next`, not from `j`'s own address** — the same pseudo-direct target
composition as `jal`, minus the link-register write (INSTRUCTION-REF "j"
section). Like every other jump/branch here, `j` itself falls through to
`PC_next` and never jumps in the same step; the delay-slot instruction
always executes first. -/
theorem j_spec_raw (p : Program) (s : State) (w target : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.j target))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      StepResult.next
        { s with pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`jr` schedules a jump to the raw 32-bit value held in `$rs`** — not a
26-bit composed target like `j`, the full register value (INSTRUCTION-REF
"jr" section). A misaligned target is not special-cased here: it surfaces
as an Address Error (AdEL) exception the next time `step` tries to fetch from it.
Same one-delay-slot discipline as every other jump/branch: `jr` itself
falls through to `PC_next`. -/
theorem jr_spec_raw (p : Program) (s : State) (w rs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jr rs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { s with pc := s.pc + 4#32, pendingBranch := some (readReg s (regIdxSpec rs)) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`jalr` links `$rd` to `pc + 8` (the same `jal`/`jalr` link-value
convention — past the delay slot) and schedules a jump to the raw value
held in `$rs`, read *before* `$rd` is overwritten** — so `rd == rs`
aliasing is always safe (INSTRUCTION-REF "jalr" section). This is `step`'s
own code restated: the target expression reads `$rs` from the original `s`,
not from the just-written state, exactly matching the "If `rd == rs`..."
paragraph in the spec. -/
theorem jalr_spec_raw (p : Program) (s : State) (w rs rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jalr rs rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      StepResult.next
        { (writeReg s (regIdxSpec rd) (pcNext + 4#32)) with
          pc := pcNext, pendingBranch := some (readReg s (regIdxSpec rs)) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Corollary of `jalr_spec_raw`: `$rd` reads back exactly `pc + 8` — past
the delay slot, the same link-value convention as `jal`'s `$ra`. Requires
`$rd` to not itself be `$zero` (a write to `$zero` is always a no-op, see
`writeReg_preserves_zero_slot`). -/
theorem jalr_sets_rd (p : Program) (s : State) (w rs rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jalr rs rd))
    (hpb : s.pendingBranch = none) (hsize32 : s.regs.size = 32)
    (hrdnz : regIdxSpec rd ≠ (0 : Fin 32)) :
    ∃ s', step p s = StepResult.next s' ∧ readReg s' (regIdxSpec rd) = s.pc + 8#32 := by
  refine ⟨_, jalr_spec_raw p s w rs rd hfetch hdecode hpb, ?_⟩
  show readReg (writeReg s (regIdxSpec rd) ((s.pc + 4#32) + 4#32)) (regIdxSpec rd) = s.pc + 8#32
  rw [writeReg_reads_back s (regIdxSpec rd) ((s.pc + 4#32) + 4#32) hrdnz hsize32, BitVec.add_assoc]
  congr 1

/-- **`jalr $rs, $rs` (`rd == rs`) jumps to the *original* `$rs` value, not
the just-written link value** — the one subtlety specific to `jalr`
(INSTRUCTION-REF "jalr" section, "If `rd == rs`..." paragraph). Both halves
are named explicitly: the scheduled jump target is the pre-write `$rs`
value (`s`, not the post-write state), and the register itself afterward
holds the link value `pc + 8` — in general a different value, so aliasing
`rd`/`rs` (the common real-MIPS32 `jalr $t9` idiom with an implicit
`rd = $ra`, or an explicit `jalr $t9, $t9`) never loses the jump target. -/
theorem jalr_rd_eq_rs_targets_original_value (p : Program) (s : State) (w rs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jalr rs rs))
    (hpb : s.pendingBranch = none) (hsize32 : s.regs.size = 32)
    (hrsnz : regIdxSpec rs ≠ (0 : Fin 32)) :
    ∃ s', step p s = StepResult.next s' ∧
      s'.pendingBranch = some (readReg s (regIdxSpec rs)) ∧
      readReg s' (regIdxSpec rs) = s.pc + 8#32 := by
  refine ⟨_, jalr_spec_raw p s w rs rs hfetch hdecode hpb, rfl, ?_⟩
  show readReg (writeReg s (regIdxSpec rs) ((s.pc + 4#32) + 4#32)) (regIdxSpec rs) = s.pc + 8#32
  rw [writeReg_reads_back s (regIdxSpec rs) ((s.pc + 4#32) + 4#32) hrsnz hsize32, BitVec.add_assoc]
  congr 1

/-- **`bltz` branch target and condition** (REGIMM, opcode `0x01`,
`rt = 0x00`): if `$rs < 0` (signed), schedules
`PC = PC_next + (offset << 2)`, same one-delay-slot discipline as
`blez`/`bgtz` (INSTRUCTION-REF "bltz" section). -/
theorem bltz_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltz rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) < 0 then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bltz`, taken**: when `$rs < 0`, schedules `PC_next + (offset << 2)`. -/
theorem bltz_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltz rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : asSigned (readReg s (regIdxSpec rs)) < 0) :
    step p s = StepResult.next
      { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bltz_spec_raw p s w rs imm hfetch hdecode hpb, ite_of_pos htaken]

/-- **`bltz`, not taken**: when `$rs ≥ 0`, falls through to `PC_next`. -/
theorem bltz_not_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltz rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : 0 ≤ asSigned (readReg s (regIdxSpec rs))) :
    step p s = StepResult.next { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  rw [bltz_spec_raw p s w rs imm hfetch hdecode hpb, ite_of_neg (by omega)]

/-- **`bgez` branch target and condition** (REGIMM, `rt = 0x01`) — the
mirror image of `bltz`: if `$rs ≥ 0` (signed, zero included), schedules
`PC = PC_next + (offset << 2)` (INSTRUCTION-REF "bgez" section). -/
theorem bgez_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgez rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if 0 ≤ asSigned (readReg s (regIdxSpec rs)) then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bgez`, taken**: when `$rs ≥ 0`, schedules `PC_next + (offset << 2)`. -/
theorem bgez_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgez rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : 0 ≤ asSigned (readReg s (regIdxSpec rs))) :
    step p s = StepResult.next
      { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bgez_spec_raw p s w rs imm hfetch hdecode hpb, ite_of_pos htaken]

/-- **`bgez`, not taken**: when `$rs < 0`, falls through to `PC_next`. -/
theorem bgez_not_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgez rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : asSigned (readReg s (regIdxSpec rs)) < 0) :
    step p s = StepResult.next { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  rw [bgez_spec_raw p s w rs imm hfetch hdecode hpb, ite_of_neg (by omega)]

/-- **`bltzal` links `$ra` to `pc + 8` unconditionally, then — independent
of the link — branches on `$rs < 0` exactly like `bltz`.** This two-part
structure (unconditional link, conditional branch) is the real MIPS32
architectural definition, not a simplification: every execution of
`bltzal` writes `$ra`, whether or not the branch itself is taken
(INSTRUCTION-REF "bltzal" section — `GPR[31] <- PC + 8` happens in the
instruction's own cycle regardless of the branch condition tested one cycle
later). The branch condition reads `$rs` from the state *before* the link
write, matching this simulator's documented resolution of the `rs = $ra`
UNPREDICTABLE case. -/
theorem bltzal_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltzal rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      let s' := writeReg s 31 (pcNext + 4#32)
      if asSigned (readReg s (regIdxSpec rs)) < 0 then
        StepResult.next { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s' with pc := pcNext, pendingBranch := some (s.pc + 8#32) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bltzal`, taken**: `$ra` links to `pc + 8` (as always) and the branch
also schedules `PC_next + (offset << 2)`. -/
theorem bltzal_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltzal rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : asSigned (readReg s (regIdxSpec rs)) < 0) :
    step p s = StepResult.next
      { (writeReg s 31 ((s.pc + 4#32) + 4#32)) with
        pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bltzal_spec_raw p s w rs imm hfetch hdecode hpb, ite_of_pos htaken]

/-- **`bltzal`, not taken**: `$ra` still links to `pc + 8` (the link is
unconditional), but no transfer is scheduled — control simply falls
through to `PC_next`. -/
theorem bltzal_not_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltzal rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : 0 ≤ asSigned (readReg s (regIdxSpec rs))) :
    step p s = StepResult.next
      { (writeReg s 31 ((s.pc + 4#32) + 4#32)) with
        pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  rw [bltzal_spec_raw p s w rs imm hfetch hdecode hpb, ite_of_neg (by omega)]

/-- Corollary of `bltzal_taken_spec`/`bltzal_not_taken_spec`: `$ra` reads
back exactly `pc + 8` regardless of whether the branch is taken — the
unconditional-link half of `bltzal` stated on its own. -/
theorem bltzal_sets_ra (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltzal rs imm))
    (hpb : s.pendingBranch = none) (hsize32 : s.regs.size = 32) :
    ∃ s', step p s = StepResult.next s' ∧ readReg s' (regIdxSpec 31#32) = s.pc + 8#32 := by
  have h31 : regIdxSpec 31#32 = (31 : Fin 32) := by decide
  have hreads : readReg (writeReg s 31 ((s.pc + 4#32) + 4#32)) (regIdxSpec 31#32) = s.pc + 8#32 := by
    rw [h31, writeReg_reads_back s 31 ((s.pc + 4#32) + 4#32) (by decide) hsize32, BitVec.add_assoc]
    congr 1
  by_cases htaken : asSigned (readReg s (regIdxSpec rs)) < 0
  · exact ⟨_, bltzal_taken_spec p s w rs imm hfetch hdecode hpb htaken, hreads⟩
  · exact ⟨_, bltzal_not_taken_spec p s w rs imm hfetch hdecode hpb (by omega), hreads⟩

/-- **`bgezal` links `$ra` to `pc + 8` unconditionally, then branches on
`$rs ≥ 0` exactly like `bgez`** — same unconditional-link/conditional-
branch structure as `bltzal` (INSTRUCTION-REF "bgezal" section). -/
theorem bgezal_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgezal rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      let s' := writeReg s 31 (pcNext + 4#32)
      if 0 ≤ asSigned (readReg s (regIdxSpec rs)) then
        StepResult.next { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s' with pc := pcNext, pendingBranch := some (s.pc + 8#32) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bgezal`, taken**: `$ra` links to `pc + 8` (as always) and the branch
also schedules `PC_next + (offset << 2)`. -/
theorem bgezal_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgezal rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : 0 ≤ asSigned (readReg s (regIdxSpec rs))) :
    step p s = StepResult.next
      { (writeReg s 31 ((s.pc + 4#32) + 4#32)) with
        pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bgezal_spec_raw p s w rs imm hfetch hdecode hpb, ite_of_pos htaken]

/-- **`bgezal`, not taken**: `$ra` still links to `pc + 8` (the link is
unconditional), but no transfer is scheduled. -/
theorem bgezal_not_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgezal rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : asSigned (readReg s (regIdxSpec rs)) < 0) :
    step p s = StepResult.next
      { (writeReg s 31 ((s.pc + 4#32) + 4#32)) with
        pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  rw [bgezal_spec_raw p s w rs imm hfetch hdecode hpb, ite_of_neg (by omega)]

/-- Corollary of `bgezal_taken_spec`/`bgezal_not_taken_spec`: `$ra` reads
back exactly `pc + 8` regardless of whether the branch is taken. -/
theorem bgezal_sets_ra (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgezal rs imm))
    (hpb : s.pendingBranch = none) (hsize32 : s.regs.size = 32) :
    ∃ s', step p s = StepResult.next s' ∧ readReg s' (regIdxSpec 31#32) = s.pc + 8#32 := by
  have h31 : regIdxSpec 31#32 = (31 : Fin 32) := by decide
  have hreads : readReg (writeReg s 31 ((s.pc + 4#32) + 4#32)) (regIdxSpec 31#32) = s.pc + 8#32 := by
    rw [h31, writeReg_reads_back s 31 ((s.pc + 4#32) + 4#32) (by decide) hsize32, BitVec.add_assoc]
    congr 1
  by_cases htaken : 0 ≤ asSigned (readReg s (regIdxSpec rs))
  · exact ⟨_, bgezal_taken_spec p s w rs imm hfetch hdecode hpb htaken, hreads⟩
  · exact ⟨_, bgezal_not_taken_spec p s w rs imm hfetch hdecode hpb (by omega), hreads⟩

/-! ### Satisfiable examples for Group 5

Same discipline as Group 3: every theorem above is instantiated on a
concrete program/state with every hypothesis discharged, via `#guard`
(compiled evaluation, since `Program`/`State.mem` are `cbv_opaque`
`Std.HashMap`s that `decide`/`rfl` get stuck on). -/

-- `blez_taken_spec`/`blez_not_taken_spec`: `-5 ≤ 0` schedules the target;
-- `5 ≤ 0` is false and falls through.
#guard (match step (prog1Spec (.blez 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.blez 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 8#32)
        | .halt _ => false) = true

-- `bgtz_taken_spec`/`bgtz_not_taken_spec`: the mirror image of `blez`.
#guard (match step (prog1Spec (.bgtz 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgtz 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 8#32)
        | .halt _ => false) = true

-- `j_spec_raw`: an unconditional jump schedules the composed target and
-- falls through to the delay slot first, same target-composition formula
-- as `jal`'s own example above.
#guard (match step (prog1Spec (.j 0x1000#32)) (initialState textBase) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some 0x4000#32
        | .halt _ => false) = true

-- `jr_spec_raw`: schedules the raw register value, not a composed target.
#guard (match step (prog1Spec (.jr 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x80020000#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some 0x80020000#32
        | .halt _ => false) = true

-- `jalr_sets_rd`: `$t1` ends up exactly `pc + 8`, and the jump target is
-- the raw value read out of `$t0`.
#guard (match step (prog1Spec (.jalr 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0x80020000#32)]) with
        | .next s =>
          readReg s 9 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some 0x80020000#32
        | .halt _ => false) = true

-- `jalr_rd_eq_rs_targets_original_value`: `jalr $t1, $t1` still schedules
-- the *original* `$t1` value as the jump target, even though `$t1` itself
-- is overwritten with the link value `pc + 8` in the same step.
#guard (match step (prog1Spec (.jalr 9#32 9#32))
          (setRegsSpec (initialState textBase) [(9, 0x80020000#32)]) with
        | .next s =>
          s.pendingBranch == some 0x80020000#32 && readReg s 9 == textBase + 8#32 &&
            s.pendingBranch ≠ some (readReg s 9)
        | .halt _ => false) = true

-- `bltz_taken_spec`/`bltz_not_taken_spec`: `-5 < 0` taken, `5 < 0` false.
#guard (match step (prog1Spec (.bltz 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bltz 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 8#32)
        | .halt _ => false) = true

-- `bgez_taken_spec`/`bgez_not_taken_spec`: the mirror image of `bltz`.
#guard (match step (prog1Spec (.bgez 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgez 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 8#32)
        | .halt _ => false) = true

-- `bltzal_sets_ra`/`bltzal_taken_spec`: `$ra` links unconditionally even
-- though the branch itself is taken here.
#guard (match step (prog1Spec (.bltzal 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s =>
          readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true

-- `bltzal_not_taken_spec`: `$ra` *still* links even though `5 < 0` is
-- false and no transfer is scheduled — the unconditional-link half fires
-- regardless of the branch outcome.
#guard (match step (prog1Spec (.bltzal 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s => readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 8#32)
        | .halt _ => false) = true

-- `bgezal_sets_ra`/`bgezal_not_taken_spec`: same unconditional-link
-- convention as `bltzal`, mirrored branch condition.
#guard (match step (prog1Spec (.bgezal 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s => readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 8#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgezal 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0#32)]) with
        | .next s =>
          readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true

/-! ## Group 5 — I-type immediate instructions (`addiu`, `slti`, `sltiu`,
`andi`, `ori`, `xori`, `lui`)

All seven are the remaining non-`addi` I-type arith/logic instructions
(`docs/spec/INSTRUCTION-REF.md` "I-type immediate arithmetic / logic"
section, right after `addi`). Every one of them is a straight-line
`execInstr` case (no inner `match`/`if` on an abstract register value, no
memory access, no branch scheduling), so each theorem below follows
`addi_spec_raw`'s exact tactic recipe verbatim. -/

/-- **`addiu` computes `$rs + sext16(imm)` with plain 32-bit wraparound and
never traps** — unlike `addi`, there is no overflow check at all (same
sign-extended immediate, but the "u" suffix removes the overflow test
entirely; INSTRUCTION-REF "addiu" section, confirmed against `Step.lean`'s
`.addiu` case, which has no `addOverflows`/halt branch whatsoever). -/
theorem addiu_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.addiu rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) + signExt16 imm)) with
          pc := (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) + signExt16 imm)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`slti` writes `1` iff `$rs < sext16(imm)` under a signed comparison,
else `0`** (INSTRUCTION-REF "slti" section). -/
theorem slti_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.slti rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := if asSigned (readReg s (regIdxSpec rs)) < asSigned (signExt16 imm)
               then 1#32 else 0#32
      StepResult.next
        { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`sltiu` sign-extends the 16-bit immediate first, exactly like `slti`,
then compares the resulting 32-bit values as unsigned** — the "u" affects
only the comparison, not the immediate's extension (INSTRUCTION-REF
"sltiu" section, same convention as this project's `sltu`; confirmed
against `Step.lean`'s `.sltiu` case, which calls `signExt16 imm` and then
compares `.toNat` values). -/
theorem sltiu_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sltiu rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := if (readReg s (regIdxSpec rs)).toNat < (signExt16 imm).toNat
               then 1#32 else 0#32
      StepResult.next
        { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`andi` zero-extends the 16-bit immediate, then bitwise-ANDs it with
`$rs`** — unlike `addi`/`slti`, the immediate is zero-extended, not
sign-extended (INSTRUCTION-REF "andi" section: "immediate is
zero-extended... not sign-extended"). -/
theorem andi_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.andi rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) &&& zeroExt16 imm)) with
          pc := (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) &&& zeroExt16 imm)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`ori` zero-extends the 16-bit immediate, then bitwise-ORs it with
`$rs`** (INSTRUCTION-REF "ori" section — same zero-extension convention as
`andi`). -/
theorem ori_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ori rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) ||| zeroExt16 imm)) with
          pc := (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) ||| zeroExt16 imm)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`xori` zero-extends the 16-bit immediate, then bitwise-XORs it with
`$rs`** (INSTRUCTION-REF "xori" section — same zero-extension convention as
`andi`). -/
theorem xori_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.xori rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) ^^^ zeroExt16 imm)) with
          pc := (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) ^^^ zeroExt16 imm)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`lui` writes `imm << 16` into `$rt`, ignoring `$rs` entirely** — `$rs`
is a fixed/unused field in the real encoding, and `Instruction.lui` itself
has no `rs` operand at all (INSTRUCTION-REF "lui" section: "$rt = imm <<
16", no sign extension needed since the low 16 bits are always discarded by
the shift). -/
theorem lui_spec_raw (p : Program) (s : State) (w rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lui rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rt) (zeroExt16 imm <<< 16)) with
          pc := (writeReg s (regIdxSpec rt) (zeroExt16 imm <<< 16)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `addiu_spec_raw`: `0x7fffffff + 1` wraps to `0x80000000` instead of
-- trapping (the one observable difference from `addi`).
#guard (match step (prog1Spec (.addiu 8#32 9#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0x7fffffff#32)]) with
        | .next s => readReg s 9 == 0x80000000#32
        | .halt _ => false) = true

-- `slti_spec_raw`/`sltiu_spec_raw`: the same bit pattern (`-1` signed,
-- `0xffffffff` unsigned) compares differently against `0` depending on
-- signedness.
#guard (match step (prog1Spec (.slti 8#32 9#32 0x0000#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => readReg s 9 == 1#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.sltiu 8#32 9#32 0x0000#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => readReg s 9 == 0#32
        | .halt _ => false) = true

-- `andi_spec_raw`/`ori_spec_raw`/`xori_spec_raw`: the immediate is
-- zero-extended, not sign-extended — the high 16 bits of `$rs` are never
-- pulled from the immediate's sign.
#guard (match step (prog1Spec (.andi 8#32 9#32 0x8001#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => readReg s 9 == 0x00008001#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.ori 8#32 9#32 0x8001#32))
          (setRegsSpec (initialState textBase) [(8, 0#32)]) with
        | .next s => readReg s 9 == 0x00008001#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.xori 8#32 9#32 0x8001#32))
          (setRegsSpec (initialState textBase) [(8, 0#32)]) with
        | .next s => readReg s 9 == 0x00008001#32
        | .halt _ => false) = true

-- `lui_spec_raw`: the immediate lands in the high half-word, low half-word
-- stays zero, and `$rs` (here nonzero garbage) is ignored since `lui` has
-- no `rs` operand at all.
#guard (match step (prog1Spec (.lui 9#32 0x8001#32)) (initialState textBase) with
        | .next s => readReg s 9 == 0x80010000#32
        | .halt _ => false) = true

/-! ## Group 6 — register-register trap family (`teq`, `tne`, `tlt`, `tge`,
`tltu`, `tgeu`, `break`)

Ground truth: `docs/spec/INSTRUCTION-REF.md` "Coprocessor 0 / traps and
exceptions" section (the shared exception mechanism) and its "teq / tne /
tlt / tge / tltu / tgeu" / "break" subsections. When the trap fires the right-hand side is `takeException s code`; Group 0
(`exceptionEntry_*`) states what that does to `EPC`/`Cause`/`Status`/`pc`
(all public `def`s in `Types.lean`) — a genuinely
different right-hand-side shape from every Group 2/5 theorem above
(`cp0Epc`/`cp0Cause`/`cp0Status`/`pc` all change together, no `writeReg`
involved at all). Every theorem below needs `hpb : s.pendingBranch = none`,
even `break` (whose own semantics never consult `pendingBranch` at all):
`Step.lean`'s `execInstr` opens with an unconditional `if
s.pendingBranch.isSome && isBranchLike instr then halt else ...` check
*before* dispatching to any instruction's own case, so `rfl` cannot reduce
past that `if` without `s.pendingBranch` pinned to a concrete value, no
matter which instruction follows. The six comparison-based theorems need
`hpb` a second time, for their *non-trapping* branch, which still falls
through via the ordinary `mkNext`/`advance` path (so its exact shape —
plain `pc + 4#32`, no `pendingBranch` left dangling — depends on `s` not
already being mid-delay-slot, exactly as for `beq_spec_raw`). -/

/-- **`break` unconditionally raises the Breakpoint exception** (ExcCode
9) — in any state, in or out of a delay slot. What `takeException` does to
`EPC`/`Cause`/`Status`/`pc`/`pendingBranch` is stated once, in Group 0
(`exceptionEntry_*`) (INSTRUCTION-REF "break" section). -/
theorem break_spec_raw (p : Program) (s : State) (w code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.break code)) :
    step p s = takeException s excCodeBp := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  rfl

-- `break_spec_raw`: a concrete `break` lands exactly on the exception
-- vector with the `Bp` exception code packed into `Cause`.
#guard (match step (prog1Spec (.break 0#32)) (initialState textBase) with
        | .next s =>
          s.cp0Epc == textBase && s.cp0Cause == (excCodeBp <<< 2) &&
            s.cp0Status == (statusCu1Mask ||| statusExlMask) && s.pc == exceptionVectorAddr
        | .halt _ => false) = true

/-- **`teq` traps iff `$rs == $rt`**, taking the shared coprocessor-0
exception with `excCode = excCodeTr`; otherwise it is a complete no-op
beyond the ordinary fallthrough to `pc + 4#32` — no CP0 state touched at
all (INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu" section). -/
theorem teq_spec_raw (p : Program) (s : State) (w rs rt code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.teq rs rt code))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tne` traps iff `$rs ≠ $rt`** — the mirror image of `teq`
(INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu" section). -/
theorem tne_spec_raw (p : Program) (s : State) (w rs rt code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tne rs rt code))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt) then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tlt` traps iff `$rs <s $rt`**, a *signed* comparison
(INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu" section: "`tlt`:
`$rs <s $rt` (signed)"). -/
theorem tlt_spec_raw (p : Program) (s : State) (w rs rt code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tlt rs rt code))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) < asSigned (readReg s (regIdxSpec rt)) then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tge` traps iff `$rs ≥s $rt`**, a *signed* comparison — the mirror
image of `tlt` (INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu"
section). -/
theorem tge_spec_raw (p : Program) (s : State) (w rs rt code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tge rs rt code))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) ≥ asSigned (readReg s (regIdxSpec rt)) then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tltu` traps iff `$rs <u $rt`**, an *unsigned* comparison on the raw
bit patterns (INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu"
section: "`tltu`: `$rs <u $rt` (unsigned)"). -/
theorem tltu_spec_raw (p : Program) (s : State) (w rs rt code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tltu rs rt code))
    (hpb : s.pendingBranch = none) :
    step p s =
      if (readReg s (regIdxSpec rs)).toNat < (readReg s (regIdxSpec rt)).toNat then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tgeu` traps iff `$rs ≥u $rt`**, an *unsigned* comparison — the
mirror image of `tltu` (INSTRUCTION-REF "teq / tne / tlt / tge / tltu /
tgeu" section). -/
theorem tgeu_spec_raw (p : Program) (s : State) (w rs rt code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tgeu rs rt code))
    (hpb : s.pendingBranch = none) :
    step p s =
      if (readReg s (regIdxSpec rs)).toNat ≥ (readReg s (regIdxSpec rt)).toNat then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `teq_spec_raw`/`tne_spec_raw`: equal registers trap under `teq` (and are
-- a no-op under `tne`); unequal registers are the mirror image. One
-- `#guard` per instruction per branch, matching the house style used for
-- `beq`/`bne` above.
#guard (match step (prog1Spec (.teq 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)]) with
        | .next s =>
          s.cp0Epc == textBase && s.cp0Cause == (excCodeTr <<< 2) &&
            s.cp0Status == (statusCu1Mask ||| statusExlMask) && s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.teq 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.cp0Status == statusCu1Mask
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tne 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s =>
          s.cp0Epc == textBase && s.cp0Cause == (excCodeTr <<< 2) &&
            s.cp0Status == (statusCu1Mask ||| statusExlMask) && s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tne 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.cp0Status == statusCu1Mask
        | .halt _ => false) = true

-- `tlt_spec_raw`/`tge_spec_raw`: `-1` (as `0xffffffff`) is signed-less-than
-- `1`, so `tlt` traps and `tge` does not; swapping the operands flips both.
#guard (match step (prog1Spec (.tlt 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tge 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true

-- `tltu_spec_raw`/`tgeu_spec_raw`: the same bit pattern `0xffffffff` is the
-- *largest* unsigned value, so it is never `<u 1` but always `≥u 1`.
#guard (match step (prog1Spec (.tltu 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tgeu 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true

/-! ## Group 7 — Coprocessor 0: register moves, `di`/`ei`, `eret`, `wait`, `pref`

The floating-point (coprocessor 1) specifications live in
`Semantics/Specs/FpSpec.lean`.

`writeFpReg_reads_back` below is the `fpRegs` counterpart of
`writeReg_reads_back` above: unlike `writeReg`, `writeFpReg` has no
hardwired-zero register to special-case, so it needs only the array-size
hypothesis. -/

/-- Writing `v` to FP register `i` and immediately reading `i` back gives
exactly `v` (`writeFpReg` has no hardwired-zero slot, unlike `writeReg`). -/
theorem writeFpReg_reads_back (s : State) (i : Fin 32) (v : W32)
    (hsize : s.fpRegs.size = 32) : readFpReg (writeFpReg s i v) i = v := by
  unfold writeFpReg readFpReg
  simp [Array.set!, Array.getD_eq_getD_getElem?, hsize, i.isLt]

/-- **`mfc0` reads a modeled CP0 register `(rd, sel)` into GPR `$rt`**:
`(8,0)` BadVAddr, `(12,0)` Status, `(13,0)` Cause, `(14,0)` EPC, `(15,0)`
PRId, `(15,1)` EBase, `(16,0)` Config, `(16,1)` Config1, `(30,0)` ErrorEPC.
`decode` produces `mfc0` only for these; for any other pair (reachable only
through a hand-built `Instruction`) the step raises Reserved Instruction,
which is also what the undecodable word does. User mode is not modeled, so
Coprocessor Unusable is never raised. -/
theorem mfc0_spec_raw (p : Program) (s : State) (w rt rd sel : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mfc0 rt rd sel))
    (hpb : s.pendingBranch = none) :
    step p s =
      let read (v : W32) : StepResult :=
        StepResult.next
          { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }
      match rd.toNat, sel.toNat with
      | 8, 0 => read s.cp0BadVAddr
      | 12, 0 => read s.cp0Status
      | 13, 0 => read s.cp0Cause
      | 14, 0 => read s.cp0Epc
      | 15, 0 => read 0x00010000#32
      | 15, 1 => read ((s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32)
      | 16, 0 => read 0x80008402#32
      | 16, 1 => read 0x00000001#32
      | 30, 0 => read s.cp0ErrorEpc
      | _, _ => takeException s excCodeRI := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`mtc0` writes GPR `$rt` into a modeled CP0 register, through that
register's write mask.** `Status` (12,0) keeps only `statusWriteMask` (IE,
EXL, ERL, IM7..0, BEV, CU1; every other bit reads as zero). `Cause` (13,0)
changes only `causeWriteMask` (DC, IV, IP1..0) and keeps `BD`, `CE`,
`ExcCode` and everything else. `EPC` (14,0) and `ErrorEPC` (30,0) are fully
writable. `EBase` (15,1) takes bits 29..12 of the written value under the
fixed bits 31..30 = `10`. `BadVAddr` (8,0), `PRId` (15,0), `Config` (16,0)
and `Config1` (16,1) are read-only: the write is ignored. Any other pair
raises Reserved Instruction, as for `mfc0_spec_raw`. -/
theorem mtc0_spec_raw (p : Program) (s : State) (w rt rd sel : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mtc0 rt rd sel))
    (hpb : s.pendingBranch = none) :
    step p s =
      match rd.toNat, sel.toNat with
      | 8, 0 => StepResult.next { s with pc := s.pc + 4#32 }
      | 12, 0 =>
        StepResult.next
          { s with cp0Status := readReg s (regIdxSpec rt) &&& statusWriteMask, pc := s.pc + 4#32 }
      | 13, 0 =>
        StepResult.next
          { s with
              cp0Cause := (s.cp0Cause &&& ~~~causeWriteMask) |||
                (readReg s (regIdxSpec rt) &&& causeWriteMask)
              pc := s.pc + 4#32 }
      | 14, 0 => StepResult.next { s with cp0Epc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | 15, 0 => StepResult.next { s with pc := s.pc + 4#32 }
      | 15, 1 =>
        StepResult.next
          { s with
              cp0EBase := (readReg s (regIdxSpec rt) &&& 0x3ffff000#32) ||| 0x80000000#32
              pc := s.pc + 4#32 }
      | 16, 0 => StepResult.next { s with pc := s.pc + 4#32 }
      | 16, 1 => StepResult.next { s with pc := s.pc + 4#32 }
      | 30, 0 =>
        StepResult.next { s with cp0ErrorEpc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | _, _ => takeException s excCodeRI := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- The write mask of `Cause` is `DC` (27), `IV` (23), `IP1..IP0` (9..8)
(MD00090 Vol III Rev 6.02 §9.36, p.209-210). -/
theorem causeWriteMask_eq : causeWriteMask = 0x08800300#32 := rfl

/-- **`di`: `$rt ← Status`, then `Status.IE ← 0`** (MD00086 Vol II-A
Rev 6.06, DI, p.164). The value written to `$rt` is the `Status` before the
change; no other `Status` bit changes. -/
theorem di_spec_raw (p : Program) (s : State) (w rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.di rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg { s with cp0Status := s.cp0Status &&& ~~~statusIeMask } (regIdxSpec rt)
            s.cp0Status) with
          pc := (writeReg { s with cp0Status := s.cp0Status &&& ~~~statusIeMask } (regIdxSpec rt)
            s.cp0Status).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  rfl

/-- **`ei`: `$rt ← Status`, then `Status.IE ← 1`** (MD00086 Vol II-A
Rev 6.06, EI, p.176). -/
theorem ei_spec_raw (p : Program) (s : State) (w rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ei rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg { s with cp0Status := s.cp0Status ||| statusIeMask } (regIdxSpec rt)
            s.cp0Status) with
          pc := (writeReg { s with cp0Status := s.cp0Status ||| statusIeMask } (regIdxSpec rt)
            s.cp0Status).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  rfl

/-- **`pref` is a no-op**: "Any action, including doing nothing, is
permitted … PREF does not cause addressing-related exceptions" (MD00086
Vol II-A Rev 6.06, PREF, p.321). Only `pc` changes; it never raises, whatever
the address and hint. -/
theorem pref_spec_raw (p : Program) (s : State) (w rs hint imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.pref rs hint imm))
    (hpb : s.pendingBranch = none) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  rfl

/-- **`eret`** (MD00086 "ERET"), executed outside a delay slot:
`if Status.ERL = 1 then PC ← ErrorEPC, ERL ← 0 else PC ← EPC, EXL ← 0`,
and **always `LLbit ← 0`**. It has no delay slot of its own: `pc` is set in
this very step. -/
theorem eret_spec_raw (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none) :
    step p s =
      if s.cp0Status &&& statusErlMask != 0#32 then
        StepResult.next
          { s with pc := s.cp0ErrorEpc, cp0Status := s.cp0Status &&& ~~~statusErlMask, llBit := false }
      else
        StepResult.next
          { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask, llBit := false } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`eret` clears `LLbit`**, whichever return address it uses — so an
`sc` after an exception return fails (see `sc_spec_raw`). -/
theorem eret_clears_llBit (p : Program) (s s' : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none) (hstep : step p s = StepResult.next s') :
    s'.llBit = false := by
  rw [eret_spec_raw p s w hfetch hdecode hpb] at hstep
  split at hstep <;> (injection hstep with h; rw [← h])

/-- **`eret` in a branch delay slot halts** (`branchInDelaySlot`), like a
branch or jump there: the architecture makes it UNPREDICTABLE. (This
replaces the former `eret_bypasses_delay_slot`, which stated that `eret`
ignored a pending branch and left it live — a behavior the architecture
does not define.) -/
theorem eret_in_delay_slot_halts (p : Program) (s : State) (w t : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = some t) :
    step p s = StepResult.halt .branchInDelaySlot :=
  branch_in_delay_slot_halts p s w .eret hfetch hdecode (by rw [hpb]; rfl) rfl

/-- **`wait` is a documented no-op**: this simulator has no
interrupt/timer model, so `wait` just falls through to `pc + 4` like any
ordinary non-control-flow instruction, touching no other state
(`Step.lean`'s `wait` docstring: `mkNext s s`). -/
theorem wait_spec_raw (p : Program) (s : State) (w code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.wait code))
    (hpb : s.pendingBranch = none) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Corollary of `wait_spec_raw`: every piece of state besides `pc` is
left untouched — the "no-op" claim made precise, not just "produces some
next state". -/
theorem wait_preserves_state (p : Program) (s : State) (w code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.wait code))
    (hpb : s.pendingBranch = none) :
    ∃ s', step p s = StepResult.next s' ∧ s'.regs = s.regs ∧ s'.fpRegs = s.fpRegs ∧
      s'.hi = s.hi ∧ s'.lo = s.lo ∧ s'.mem = s.mem ∧ s'.out = s.out ∧
      s'.cp0Status = s.cp0Status ∧ s'.cp0Cause = s.cp0Cause ∧ s'.cp0Epc = s.cp0Epc ∧
      s'.pc = s.pc + 4#32 := by
  refine ⟨_, wait_spec_raw p s w code hfetch hdecode hpb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- `mfc0` reads back Status/Cause/EPC, selected by `rd`;
-- an out-of-scope `rd` raises Reserved Instruction.
#guard (match step (prog1Spec (.mfc0 8#32 12#32 0#32)) { (initialState textBase) with cp0Status := 0x2#32 } with
        | .next s => readReg s 8 == 0x2#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mfc0 8#32 13#32 0#32)) { (initialState textBase) with cp0Cause := 0x34#32 } with
        | .next s => readReg s 8 == 0x34#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mfc0 8#32 14#32 0#32)) { (initialState textBase) with cp0Epc := 0x3000#32 } with
        | .next s => readReg s 8 == 0x3000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mfc0 8#32 0#32 0#32)) (initialState textBase) with
        | .next s' => causeExcCode s' == excCodeRI && s'.pc == exceptionVectorAddr
        | .halt _ => false) = true

-- `mtc0` writes Status/Cause (through its mask)/EPC from a GPR; an
-- out-of-scope `rd` raises Reserved Instruction.
#guard (match step (prog1Spec (.mtc0 8#32 12#32 0#32)) (setRegsSpec (initialState textBase) [(8, 0x2#32)]) with
        | .next s => s.cp0Status == 0x2#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mtc0 8#32 13#32 0#32)) (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => s.cp0Cause == causeWriteMask
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mtc0 8#32 14#32 0#32)) (setRegsSpec (initialState textBase) [(8, 0x3000#32)]) with
        | .next s => s.cp0Epc == 0x3000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mtc0 8#32 0#32 0#32)) (setRegsSpec (initialState textBase) [(8, 1#32)]) with
        | .next s' => causeExcCode s' == excCodeRI && s'.pc == exceptionVectorAddr
        | .halt _ => false) = true

-- `eret` restores `pc` from `cp0Epc` and clears `Status.EXL`.
#guard (match step (prog1Spec .eret)
          { (initialState textBase) with cp0Epc := 0x3000#32, cp0Status := statusExlMask } with
        | .next s => s.pc == 0x3000#32 && s.cp0Status == 0#32
        | .halt _ => false) = true
-- `eret_clears_llBit`; `Status.ERL = 1` returns to `ErrorEPC` and clears `ERL`.
#guard (match step (prog1Spec .eret)
          { (initialState textBase) with cp0Epc := 0x3000#32, cp0Status := statusExlMask, llBit := true } with
        | .next s => s.llBit == false
        | .halt _ => false) = true
#guard (match step (prog1Spec .eret)
          { (initialState textBase) with cp0Epc := 0x3000#32, cp0ErrorEpc := 0x4000#32,
                                         cp0Status := statusErlMask ||| statusExlMask } with
        | .next s => s.pc == 0x4000#32 && s.cp0Status == statusExlMask
        | .halt _ => false) = true
-- `eret_in_delay_slot_halts`.
#guard (match step (prog1Spec .eret)
          { (initialState textBase) with
            cp0Epc := 0x3000#32, cp0Status := statusExlMask,
            pendingBranch := some 0x99999999#32 } with
        | .halt .branchInDelaySlot => true
        | _ => false) = true

-- `wait` falls through to `pc + 4`, touching no other state.
#guard (match step (prog1Spec (.wait 0#32)) (initialState textBase) with
        | .next s => s.pc == textBase + 4#32 && s.cp0Status == (initialState textBase).cp0Status &&
            s.regs == (initialState textBase).regs
        | .halt _ => false) = true

/-! ## Group 7 — `lwl`/`lwr`/`swl`/`swr`: classic MIPS32 unaligned load/store pair

Real MIPS32 classic (pre-r6) unaligned-memory-access family (MD00086 Rev
2.50 §3.2, Table 3-4; `docs/spec/INSTRUCTION-REF.md`'s dedicated section).
Unlike `lw`/`sw`, the effective address has no alignment requirement at
all: `readMemByte`/`writeMemByte` are already total, so none of these four
`step` cases can ever halt — `lwl_spec_raw`/`lwr_spec_raw` have no
Address Error branch at all (contrast `lw_spec_raw`), and
`swl_spec_raw`/`swr_spec_raw`, like `sw_spec_raw`, only ever clear `llBit`.
Each RHS below reconstructs `Step.lean`'s own four-way
`off := addr.toNat % 4` match verbatim, using the `setByteSlotSpec`/
`getByteSlotSpec` mirrors declared at the top of this file plus the public
`readMemByte`/`writeMemByte` — the same technique `sc_spec_raw`/
`div_spec_raw` already use for a symbolic `if`/`match` scrutinee that does
not need to resolve for the closing `rfl` to go through. -/

/-- **`lwl` ("load word left") merges 1–4 most-significant bytes starting at
`$rs + sext16(offset)` into the most-significant end of `$rt`, leaving
`$rt`'s existing least-significant bytes untouched** — exactly how many
bytes merge depends on `addr.toNat % 4` (4 at `off = 0`, behaving exactly
like a plain `lw`; down to 1 at `off = 3`). Never halts on a misaligned
address, unlike `lw` (INSTRUCTION-REF `lwl` section). -/
theorem lwl_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lwl rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      let off := addr.toNat % 4
      let old := readReg s (regIdxSpec rt)
      let b0 := (readMemByte s addr).getD 0
      let v :=
        match off with
        | 0 =>
          let b1 := (readMemByte s (addr + 1#32)).getD 0
          let b2 := (readMemByte s (addr + 2#32)).getD 0
          let b3 := (readMemByte s (addr + 3#32)).getD 0
          setByteSlotSpec (setByteSlotSpec (setByteSlotSpec (setByteSlotSpec old 0 b0) 1 b1) 2 b2) 3 b3
        | 1 =>
          let b1 := (readMemByte s (addr + 1#32)).getD 0
          let b2 := (readMemByte s (addr + 2#32)).getD 0
          setByteSlotSpec (setByteSlotSpec (setByteSlotSpec old 0 b0) 1 b1) 2 b2
        | 2 =>
          let b1 := (readMemByte s (addr + 1#32)).getD 0
          setByteSlotSpec (setByteSlotSpec old 0 b0) 1 b1
        | _ =>  -- off = 3 (Nat match needs a default; addr.toNat % 4 is always < 4)
          setByteSlotSpec old 0 b0
      StepResult.next
        { (writeReg s (regIdxSpec rt) v) with
          pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`lwr` ("load word right") merges 1–4 least-significant bytes ending
at `$rs + sext16(offset)` into the least-significant end of `$rt`, leaving
`$rt`'s existing most-significant bytes untouched** — the mirror image of
`lwl_spec_raw`: exactly how many bytes merge depends on `addr.toNat % 4`
(1 at `off = 0`, up to 4 at `off = 3`, behaving exactly like a plain `lw`).
Never halts on a misaligned address, unlike `lw` (INSTRUCTION-REF `lwr`
section). -/
theorem lwr_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lwr rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      let off := addr.toNat % 4
      let old := readReg s (regIdxSpec rt)
      let v :=
        match off with
        | 0 =>
          let b3 := (readMemByte s addr).getD 0
          setByteSlotSpec old 3 b3
        | 1 =>
          let b2 := (readMemByte s (addr - 1#32)).getD 0
          let b3 := (readMemByte s addr).getD 0
          setByteSlotSpec (setByteSlotSpec old 2 b2) 3 b3
        | 2 =>
          let b1 := (readMemByte s (addr - 2#32)).getD 0
          let b2 := (readMemByte s (addr - 1#32)).getD 0
          let b3 := (readMemByte s addr).getD 0
          setByteSlotSpec (setByteSlotSpec (setByteSlotSpec old 1 b1) 2 b2) 3 b3
        | _ =>  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
          let b0 := (readMemByte s (addr - 3#32)).getD 0
          let b1 := (readMemByte s (addr - 2#32)).getD 0
          let b2 := (readMemByte s (addr - 1#32)).getD 0
          let b3 := (readMemByte s addr).getD 0
          setByteSlotSpec (setByteSlotSpec (setByteSlotSpec (setByteSlotSpec old 0 b0) 1 b1) 2 b2) 3 b3
      StepResult.next
        { (writeReg s (regIdxSpec rt) v) with
          pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`swl` ("store word left") stores `$rt`'s most-significant 1–4 bytes
starting at `$rs + sext16(offset)`, and clears `llBit`** (store-class, like
`sw`/`sh`) — exactly how many bytes are stored depends on
`addr.toNat % 4` (4 at `off = 0`, behaving exactly like a plain `sw`; down
to 1 at `off = 3`). Never halts on a misaligned address, unlike `sw`
(INSTRUCTION-REF `swl` section). -/
theorem swl_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.swl rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      let off := addr.toNat % 4
      let v := readReg s (regIdxSpec rt)
      let s1 := (writeMemByte s addr (getByteSlotSpec v 0)).getD s
      let s' :=
        match off with
        | 0 =>
          let s2 := (writeMemByte s1 (addr + 1#32) (getByteSlotSpec v 1)).getD s1
          let s3 := (writeMemByte s2 (addr + 2#32) (getByteSlotSpec v 2)).getD s2
          (writeMemByte s3 (addr + 3#32) (getByteSlotSpec v 3)).getD s3
        | 1 =>
          let s2 := (writeMemByte s1 (addr + 1#32) (getByteSlotSpec v 1)).getD s1
          (writeMemByte s2 (addr + 2#32) (getByteSlotSpec v 2)).getD s2
        | 2 => (writeMemByte s1 (addr + 1#32) (getByteSlotSpec v 1)).getD s1
        | _ => s1  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
      StepResult.next
        { ({ s' with llBit := false }) with
          pc := ({ s' with llBit := false }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`swr` ("store word right") stores `$rt`'s least-significant 1–4
bytes ending at `$rs + sext16(offset)`, and clears `llBit`** (store-class,
like `sw`/`sh`) — the mirror image of `swl_spec_raw`: exactly how many
bytes are stored depends on `addr.toNat % 4` (1 at `off = 0`, up to 4 at
`off = 3`, behaving exactly like a plain `sw`). Never halts on a misaligned
address, unlike `sw` (INSTRUCTION-REF `swr` section). -/
theorem swr_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.swr rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      let off := addr.toNat % 4
      let v := readReg s (regIdxSpec rt)
      let s' :=
        match off with
        | 0 => (writeMemByte s addr (getByteSlotSpec v 3)).getD s
        | 1 =>
          let s1 := (writeMemByte s (addr - 1#32) (getByteSlotSpec v 2)).getD s
          (writeMemByte s1 addr (getByteSlotSpec v 3)).getD s1
        | 2 =>
          let s1 := (writeMemByte s (addr - 2#32) (getByteSlotSpec v 1)).getD s
          let s2 := (writeMemByte s1 (addr - 1#32) (getByteSlotSpec v 2)).getD s1
          (writeMemByte s2 addr (getByteSlotSpec v 3)).getD s2
        | _ =>  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
          let s1 := (writeMemByte s (addr - 3#32) (getByteSlotSpec v 0)).getD s
          let s2 := (writeMemByte s1 (addr - 2#32) (getByteSlotSpec v 1)).getD s1
          let s3 := (writeMemByte s2 (addr - 1#32) (getByteSlotSpec v 2)).getD s2
          (writeMemByte s3 addr (getByteSlotSpec v 3)).getD s3
      StepResult.next
        { ({ s' with llBit := false }) with
          pc := ({ s' with llBit := false }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Base address for the concrete `lwl`/`lwr`/`swl`/`swr` examples below
(mirrors `Step.lean`'s test-only `unalignedBase`). -/
def unalignedBaseSpec : W32 := 0x10010000#32

/-- Write a list of `(address, byte)` pairs into `s.mem`, for building the
concrete unaligned-memory examples below (mirrors `setRegsSpec`'s `foldl`
shape; `writeMemByte` always succeeds — see its docstring — so the `.getD
acc` fallback is never actually exercised, same as every `.getD` in
`swl_spec_raw`/`swr_spec_raw` above). -/
def setMemBytesSpec (s : State) (kvs : List (W32 × UInt8)) : State :=
  kvs.foldl (fun acc kv => (writeMemByte acc kv.1 kv.2).getD acc) s

/-- Concrete state with `$t0` (register 8) pointing at `unalignedBaseSpec`
and bytes `0x11,0x22,...,0x88` at `unalignedBaseSpec + 0..7`, so every
byte-position merge `lwl`/`lwr` perform is individually visible in the
resulting word (mirrors `Step.lean`'s test-only `unalignedTestState`). -/
def unalignedTestStateSpec : State :=
  setMemBytesSpec (setRegsSpec (initialState textBase) [(8, unalignedBaseSpec)])
    [(unalignedBaseSpec + 0#32, 0x11), (unalignedBaseSpec + 1#32, 0x22),
     (unalignedBaseSpec + 2#32, 0x33), (unalignedBaseSpec + 3#32, 0x44),
     (unalignedBaseSpec + 4#32, 0x55), (unalignedBaseSpec + 5#32, 0x66),
     (unalignedBaseSpec + 6#32, 0x77), (unalignedBaseSpec + 7#32, 0x88)]

/-- Concrete state with `$t0` pointing at `unalignedBaseSpec` and `$t1`
holding `0xaabbccdd`, for the `swl`/`swr` examples below (mirrors
`Step.lean`'s test-only `swTestState`). -/
def swTestStateSpec : State :=
  setRegsSpec (initialState textBase) [(8, unalignedBaseSpec), (9, 0xaabbccdd#32)]

-- `lwl_spec_raw`: `off = 0` loads the full word, exactly matching plain `lw`.
#guard (match step (prog1Spec (.lwl 8#32 9#32 0#32)) unalignedTestStateSpec with
        | .next s => readReg s 9 == 0x11223344#32
        | .halt _ => false) = true

-- `lwl_spec_raw`: the three misaligned offsets, `$rt`'s untouched low
-- bytes coming from its prior value.
#guard (match step (prog1Spec (.lwl 8#32 9#32 1#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0x000000ff#32)]) with
        | .next s => readReg s 9 == 0x223344ff#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.lwl 8#32 9#32 2#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0x0000abcd#32)]) with
        | .next s => readReg s 9 == 0x3344abcd#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.lwl 8#32 9#32 3#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0x00112233#32)]) with
        | .next s => readReg s 9 == 0x44112233#32
        | .halt _ => false) = true

-- `lwr_spec_raw`: `off = 3` loads the full word, exactly matching plain `lw`.
#guard (match step (prog1Spec (.lwr 8#32 9#32 3#32)) unalignedTestStateSpec with
        | .next s => readReg s 9 == 0x11223344#32
        | .halt _ => false) = true

-- `lwr_spec_raw`: the three misaligned offsets, `$rt`'s untouched high
-- bytes coming from its prior value.
#guard (match step (prog1Spec (.lwr 8#32 9#32 0#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0xaabbcc00#32)]) with
        | .next s => readReg s 9 == 0xaabbcc11#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.lwr 8#32 9#32 1#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0xaabb0000#32)]) with
        | .next s => readReg s 9 == 0xaabb1122#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.lwr 8#32 9#32 2#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0xaa000000#32)]) with
        | .next s => readReg s 9 == 0xaa112233#32
        | .halt _ => false) = true

-- Complementary-pair idiom: `lwl $rt, 1($rs)` then `lwr $rt, 4($rs)`
-- (addresses `A+1` and `A+4`, both unaligned/aligned-boundary-straddling)
-- together reconstruct the unaligned word spanning bytes `A+1..A+4`
-- (`0x22334455`), each byte supplied by exactly one of the two instructions.
-- Both instructions must come from the same two-instruction program (run
-- sequentially via its own advancing `pc`), not two independent
-- single-instruction programs both starting at `textBase`.
#guard (match step (buildProgSpec textBase [.lwl 8#32 9#32 1#32, .lwr 8#32 9#32 4#32])
          unalignedTestStateSpec with
        | .next s1 =>
          (match step (buildProgSpec textBase [.lwl 8#32 9#32 1#32, .lwr 8#32 9#32 4#32]) s1 with
            | .next s2 => readReg s2 9 == 0x22334455#32
            | .halt _ => false)
        | .halt _ => false) = true

-- `swl_spec_raw`: `off = 0` stores the full word, exactly matching plain
-- `sw`, and clears a previously-set `llBit`.
#guard (match step (prog1Spec (.swl 8#32 9#32 0#32)) { swTestStateSpec with llBit := true } with
        | .next s => readMemWord s unalignedBaseSpec == some 0xaabbccdd#32 && s.llBit == false
        | .halt _ => false) = true

-- `swl_spec_raw`: the three misaligned offsets store only the top
-- `4 - off` bytes, starting at `addr`; bytes before `addr` (and after the
-- stored run) are untouched (read back as the zero-fill default).
#guard (match step (prog1Spec (.swl 8#32 9#32 1#32)) swTestStateSpec with
        | .next s =>
          readMemByte s (unalignedBaseSpec + 1#32) == some 0xaa &&
            readMemByte s (unalignedBaseSpec + 2#32) == some 0xbb &&
            readMemByte s (unalignedBaseSpec + 3#32) == some 0xcc &&
            readMemByte s (unalignedBaseSpec + 4#32) == some 0
        | .halt _ => false) = true
#guard (match step (prog1Spec (.swl 8#32 9#32 2#32)) swTestStateSpec with
        | .next s =>
          readMemByte s (unalignedBaseSpec + 2#32) == some 0xaa &&
            readMemByte s (unalignedBaseSpec + 3#32) == some 0xbb
        | .halt _ => false) = true
#guard (match step (prog1Spec (.swl 8#32 9#32 3#32)) swTestStateSpec with
        | .next s => readMemByte s (unalignedBaseSpec + 3#32) == some 0xaa
        | .halt _ => false) = true

-- `swr_spec_raw`: `off = 3` stores the full word, exactly matching plain
-- `sw`, and clears a previously-set `llBit`.
#guard (match step (prog1Spec (.swr 8#32 9#32 3#32)) { swTestStateSpec with llBit := true } with
        | .next s => readMemWord s unalignedBaseSpec == some 0xaabbccdd#32 && s.llBit == false
        | .halt _ => false) = true

-- `swr_spec_raw`: the three misaligned offsets store only the bottom
-- `off + 1` bytes, ending at `addr`.
#guard (match step (prog1Spec (.swr 8#32 9#32 0#32)) swTestStateSpec with
        | .next s => readMemByte s unalignedBaseSpec == some 0xdd
        | .halt _ => false) = true
#guard (match step (prog1Spec (.swr 8#32 9#32 1#32)) swTestStateSpec with
        | .next s =>
          readMemByte s unalignedBaseSpec == some 0xcc &&
            readMemByte s (unalignedBaseSpec + 1#32) == some 0xdd
        | .halt _ => false) = true
#guard (match step (prog1Spec (.swr 8#32 9#32 2#32)) swTestStateSpec with
        | .next s =>
          readMemByte s unalignedBaseSpec == some 0xbb &&
            readMemByte s (unalignedBaseSpec + 1#32) == some 0xcc &&
            readMemByte s (unalignedBaseSpec + 2#32) == some 0xdd
        | .halt _ => false) = true

-- Complementary-pair idiom: `swl $rt, 1($rs)` then `swr $rt, 4($rs)`
-- together store every byte of `$rt` into the unaligned word spanning
-- `A+1..A+4`, exactly once each. Same two-instruction-program caveat as
-- the `lwl`/`lwr` idiom example above.
#guard (match step (buildProgSpec textBase [.swl 8#32 9#32 1#32, .swr 8#32 9#32 4#32])
          swTestStateSpec with
        | .next s1 =>
          (match step (buildProgSpec textBase [.swl 8#32 9#32 1#32, .swr 8#32 9#32 4#32]) s1 with
            | .next s2 =>
              readMemByte s2 (unalignedBaseSpec + 1#32) == some 0xaa &&
                readMemByte s2 (unalignedBaseSpec + 2#32) == some 0xbb &&
                readMemByte s2 (unalignedBaseSpec + 3#32) == some 0xcc &&
                readMemByte s2 (unalignedBaseSpec + 4#32) == some 0xdd
            | .halt _ => false)
        | .halt _ => false) = true


/-! ## Group 8 — SPECIAL2/SPECIAL3 bit-manipulation specs (`clo`, `clz`,
`mul`, `seb`, `seh`, `wsbh`, `ext`, `ins`)

These eight instructions (MIPS32/MIPS32r2 additions, `docs/spec/
MIPS-COVERAGE-GAPS.md` §3.4/§3.5) had an `execInstr` case in `Step.lean` and
`#guard` coverage there, but no `_spec_raw` theorem in this file. This
closes that gap, following the same "restate `step`, close by `rfl`" recipe as every other
group above. The abbreviations they use (`countLeadingZerosFromSpec`/`countLeadingZerosSpec`/
`countLeadingOnesSpec`/`signExtLowByteSpec`/`lowBitsMaskSpec`) live next to
`regIdxSpec` near the top of the file, per this file's existing convention. -/

/-- **`clo` counts `$rs`'s leading one bits (from the MSB) into `$rd`**;
`32` if `$rs` is all-ones (SPECIAL2 opcode 0x1c, funct 0x21; INSTRUCTION-REF
"clo"). -/
theorem clo_spec_raw (p : Program) (s : State) (w rs rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.clo rs rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd)
            (BitVec.ofNat 32 (countLeadingOnesSpec (readReg s (regIdxSpec rs))))) with
          pc := (writeReg s (regIdxSpec rd)
            (BitVec.ofNat 32 (countLeadingOnesSpec (readReg s (regIdxSpec rs))))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`clz` counts `$rs`'s leading zero bits (from the MSB) into `$rd`**;
`32` if `$rs` is all-zero (SPECIAL2 opcode 0x1c, funct 0x20; INSTRUCTION-REF
"clz"). -/
theorem clz_spec_raw (p : Program) (s : State) (w rs rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.clz rs rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd)
            (BitVec.ofNat 32 (countLeadingZerosSpec (readReg s (regIdxSpec rs))))) with
          pc := (writeReg s (regIdxSpec rd)
            (BitVec.ofNat 32 (countLeadingZerosSpec (readReg s (regIdxSpec rs))))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `clo`/`clz` satisfiable examples, matching `Step.lean`'s own `#guard`s:
-- all-ones -> 32 leading ones, all-zero -> 0; all-zero -> 32 leading zeros.
#guard (match step (prog1Spec (.clo 8#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => readReg s 10 == 32#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.clo 8#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xfff0ffff#32)]) with
        | .next s => readReg s 10 == 12#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.clz 8#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x00000000#32)]) with
        | .next s => readReg s 10 == 32#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.clz 8#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x0000ffff#32)]) with
        | .next s => readReg s 10 == 16#32
        | .halt _ => false) = true

/-- **`mul` writes the low 32 bits of the signed product `$rs * $rt` to
`$rd`; `hi`/`lo` are left completely unchanged** (SPECIAL2 opcode 0x1c,
funct 0x02; INSTRUCTION-REF "mul"). Unlike `mult`, this never touches the
`hi`/`lo` accumulator at all — see `mul_leaves_hi_lo_unchanged` below for
that half of the claim isolated. -/
theorem mul_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mul rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs) * readReg s (regIdxSpec rt))) with
          pc := (writeReg s (regIdxSpec rd)
            (readReg s (regIdxSpec rs) * readReg s (regIdxSpec rt))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **"Bad output rejection" for `mul`**: the resulting state's `hi`/`lo`
read back *exactly* their pre-step values — a buggy implementation that
routed `mul` through the same `hi`/`lo`-writing path as `mult` could never
satisfy this. -/
theorem mul_leaves_hi_lo_unchanged (p : Program) (s s' : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mul rs rt rd))
    (hpb : s.pendingBranch = none)
    (hstep : step p s = StepResult.next s') :
    s'.hi = s.hi ∧ s'.lo = s.lo := by
  rw [mul_spec_raw p s w rs rt rd hfetch hdecode hpb] at hstep
  injection hstep with hs
  rw [← hs]
  exact ⟨writeReg_hi s _ _, writeReg_lo s _ _⟩

-- `mul` satisfiable examples, matching `Step.lean`'s own `#guard`s: the
-- regular product case, and signed wraparound ((-1) * 2 = -2).
#guard (match step (prog1Spec (.mul 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 6#32), (9, 7#32)]) with
        | .next s => readReg s 10 == 42#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mul 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 2#32)]) with
        | .next s => readReg s 10 == 0xfffffffe#32
        | .halt _ => false) = true

/-- **`seb` sign-extends `$rt`'s low byte into `$rd`**, ignoring `$rt`'s
higher bits entirely (SPECIAL3 BSHFL opcode 0x1f, funct 0x20, sub-field
0x10; INSTRUCTION-REF "seb"). -/
theorem seb_spec_raw (p : Program) (s : State) (w rd rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.seb rd rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) (signExtLowByteSpec (readReg s (regIdxSpec rt)))) with
          pc := (writeReg s (regIdxSpec rd)
            (signExtLowByteSpec (readReg s (regIdxSpec rt)))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`seh` sign-extends `$rt`'s low halfword into `$rd`**, ignoring `$rt`'s
upper 16 bits entirely (SPECIAL3 BSHFL opcode 0x1f, funct 0x20, sub-field
0x18; INSTRUCTION-REF "seh"). Reuses the already-public `signExt16` directly
— no new mirror needed (same helper `addi`/`lw`/etc. already use for
immediates). -/
theorem seh_spec_raw (p : Program) (s : State) (w rd rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.seh rd rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) (signExt16 (readReg s (regIdxSpec rt)))) with
          pc := (writeReg s (regIdxSpec rd) (signExt16 (readReg s (regIdxSpec rt)))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `seb`/`seh` satisfiable examples, matching `Step.lean`'s own `#guard`s.
#guard (match step (prog1Spec (.seb 10#32 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345680#32)]) with
        | .next s => readReg s 10 == 0xffffff80#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.seb 10#32 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x1234567f#32)]) with
        | .next s => readReg s 10 == 0x0000007f#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.seh 10#32 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x1234ffff#32)]) with
        | .next s => readReg s 10 == 0xffffffff#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.seh 10#32 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x12347fff#32)]) with
        | .next s => readReg s 10 == 0x00007fff#32
        | .halt _ => false) = true

/-- **`wsbh` swaps the two bytes within each 16-bit half of `$rt`
independently, leaving the halfwords themselves in place** — not a full
32-bit byte-reverse (SPECIAL3 BSHFL opcode 0x1f, funct 0x20, sub-field 0x02;
INSTRUCTION-REF "wsbh"). The formula is small enough that `Step.lean` writes
it out inline with no helper, so this restates it directly. -/
theorem wsbh_spec_raw (p : Program) (s : State) (w rd rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.wsbh rd rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := readReg s (regIdxSpec rt)
      let b0 := v &&& 0xff#32
      let b1 := (v >>> 8) &&& 0xff#32
      let b2 := (v >>> 16) &&& 0xff#32
      let b3 := (v >>> 24) &&& 0xff#32
      let result := (b2 <<< 24) ||| (b3 <<< 16) ||| (b0 <<< 8) ||| b1
      StepResult.next
        { (writeReg s (regIdxSpec rd) result) with
          pc := (writeReg s (regIdxSpec rd) result).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `wsbh` satisfiable example, matching `Step.lean`'s own `#guard`: halfword0
-- `0x5678` swaps to `0x7856`, halfword1 `0x1234` swaps to `0x3412`, halfwords
-- stay in place -> `0x34127856`.
#guard (match step (prog1Spec (.wsbh 10#32 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)]) with
        | .next s => readReg s 10 == 0x34127856#32
        | .halt _ => false) = true

/-- **`ext` extracts a `size`-bit field of `$rs` starting at bit `pos`,
zero-extended, into `$rt`** (SPECIAL3 opcode 0x1f, funct 0x00;
INSTRUCTION-REF "ext"). `pos`/`size` are already the semantic values here —
`decode` did the raw-field +-1 arithmetic — so this is pure bit masking,
with no special case for the real `pos + size <= 32` hardware constraint
(matching `Step.lean`'s own documented choice). -/
theorem ext_spec_raw (p : Program) (s : State) (w rt rs pos size : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ext rt rs pos size))
    (hpb : s.pendingBranch = none) :
    step p s =
      let field := (readReg s (regIdxSpec rs) >>> pos.toNat) &&& lowBitsMaskSpec size.toNat
      StepResult.next
        { (writeReg s (regIdxSpec rt) field) with
          pc := (writeReg s (regIdxSpec rt) field).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`ins` inserts the low `size` bits of `$rs`, shifted up to bit `pos`,
into `$rt`, leaving every other bit of `$rt` untouched** (SPECIAL3 opcode
0x1f, funct 0x04; INSTRUCTION-REF "ins"). See `ins_outside_field_unchanged`
below for the "every other bit" half of this claim isolated and proved on
its own, the same way `movn`/`movz`'s "genuinely unchanged" properties are
proved elsewhere in this file. -/
theorem ins_spec_raw (p : Program) (s : State) (w rt rs pos size : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ins rt rs pos size))
    (hpb : s.pendingBranch = none) :
    step p s =
      let mask := lowBitsMaskSpec size.toNat
      let srcField := (readReg s (regIdxSpec rs) &&& mask) <<< pos.toNat
      let clearMask := ~~~(mask <<< pos.toNat)
      let newVal := (readReg s (regIdxSpec rt) &&& clearMask) ||| srcField
      StepResult.next
        { (writeReg s (regIdxSpec rt) newVal) with
          pc := (writeReg s (regIdxSpec rt) newVal).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Bitvector identity behind `ins_outside_field_unchanged`: ORing in a
field that lies entirely inside `l <<< k` cannot change the bits outside
`l <<< k`. Proved bit by bit (no SAT solver / native evaluation, so it
depends only on the three standard axioms). -/
theorem ins_mask_absorb (a b l : W32) (k : Nat) :
    ((a &&& ~~~(l <<< k)) ||| ((b &&& l) <<< k)) &&& ~~~(l <<< k) = a &&& ~~~(l <<< k) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_shiftLeft]
  by_cases hk : i < k
  · simp [hk]
  · simp only [hk, decide_false, Bool.not_false, Bool.true_and]
    cases a[i] <;> cases b[i - k] <;> cases l[i - k] <;> rfl

/-- **"Bad output rejection" for `ins`**: after `ins` runs, `$rt`'s bits
*outside* the `[pos, pos+size)` target field read back *exactly* their
pre-step values — a buggy implementation that e.g. zeroed the rest of `$rt`
instead of preserving it could never satisfy this. The field-boundary mask
`clearMask` is exactly `ins_spec_raw`'s own `clearMask`, so this is a direct
algebraic consequence of that equation (`ins_mask_absorb` just above is the
bitvector identity: ORing in a field that `clearMask` already zeroes out cannot change
what survives when `clearMask` is applied again). Needs `regIdxSpec rt ≠ 0`
(a write to `$zero` is a no-op, INSTRUCTION-REF Global rule 2) and
`s.regs.size = 32` (`writeReg_reads_back`'s side condition, guaranteed by
`initialState` — `State.lean`). -/
theorem ins_outside_field_unchanged (p : Program) (s s' : State) (w rt rs pos size : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ins rt rs pos size))
    (hpb : s.pendingBranch = none)
    (hrt : regIdxSpec rt ≠ 0) (hsize32 : s.regs.size = 32)
    (hstep : step p s = StepResult.next s') :
    let clearMask := ~~~(lowBitsMaskSpec size.toNat <<< pos.toNat)
    readReg s' (regIdxSpec rt) &&& clearMask = readReg s (regIdxSpec rt) &&& clearMask := by
  rw [ins_spec_raw p s w rt rs pos size hfetch hdecode hpb] at hstep
  injection hstep with hs
  have hr : readReg s' (regIdxSpec rt) =
      (readReg s (regIdxSpec rt) &&& ~~~(lowBitsMaskSpec size.toNat <<< pos.toNat)) |||
        ((readReg s (regIdxSpec rs) &&& lowBitsMaskSpec size.toNat) <<< pos.toNat) := by
    rw [← hs]
    exact writeReg_reads_back s (regIdxSpec rt) _ hrt hsize32
  dsimp only
  rw [hr]
  exact ins_mask_absorb _ _ _ _

-- `ext`/`ins` satisfiable examples, matching `Step.lean`'s own `#guard`s.
#guard (match step (prog1Spec (.ext 10#32 8#32 6#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)]) with
        | .next s => readReg s 10 == ((0x12345678#32 >>> 6) &&& 0x3ff#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.ext 10#32 8#32 0#32 32#32))
          (setRegsSpec (initialState textBase) [(8, 0x89abcdef#32)]) with
        | .next s => readReg s 10 == 0x89abcdef#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.ins 10#32 8#32 6#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x159#32), (10, 0x12345678#32)]) with
        | .next s => readReg s 10 == ((0x12345678#32 &&& ~~~(0x3ff#32 <<< 6)) ||| ((0x159#32 &&& 0x3ff#32) <<< 6))
        | .halt _ => false) = true
-- `ins_outside_field_unchanged` concrete witness: bits outside `[6, 16)` of
-- `$t2` survive the `ins` untouched.
#guard (match step (prog1Spec (.ins 10#32 8#32 6#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x159#32), (10, 0x12345678#32)]) with
        | .next s => (readReg s 10 &&& ~~~(0x3ff#32 <<< 6)) == (0x12345678#32 &&& ~~~(0x3ff#32 <<< 6))
        | .halt _ => false) = true


/-! ## Group 8 — immediate-operand trap family (`teqi`, `tnei`, `tgei`,
`tgeiu`, `tlti`, `tltiu`)

Ground truth: `docs/spec/INSTRUCTION-REF.md`'s REGIMM trap-immediate
subsection and `docs/spec/MIPS-COVERAGE-GAPS.md` §3.8, mirrored directly
from `Step.lean`'s `.teqi`/`.tnei`/`.tgei`/`.tgeiu`/`.tlti`/`.tltiu` cases.
These six are the sign-extended-16-bit-immediate counterparts of Group 6's
`teq`/`tne`/`tlt`/`tge`/`tltu`/`tgeu`: same coprocessor-0 `takeException`
shape (`cp0Epc`/`cp0Cause`/`cp0Status`/`pc` all change together on the
trapping branch, plain fallthrough to `pc + 4#32` otherwise), comparing
`$rs` against `signExt16 imm` instead of against a second register.
`tgeiu`/`tltiu` sign-extend the immediate to a full 32-bit value *first*,
exactly like `sltiu` does for its immediate, and only then compare the
resulting bit pattern as unsigned (confirmed against `Step.lean`'s actual
`.tgeiu`/`.tltiu` cases, which call `signExt16 imm` and then compare
`.toNat` values — not zero-extension, and not a signed comparison). As in
Group 6, every theorem below needs `hpb : s.pendingBranch = none` because
`execInstr` opens with an unconditional `pendingBranch`/`isBranchLike`
guard before dispatching to any instruction's own case. -/

/-- **`teqi` traps iff `$rs == sext16(imm)`**, taking the shared
coprocessor-0 exception with `excCode = excCodeTr`; otherwise it is a
complete no-op beyond the ordinary fallthrough to `pc + 4#32` (REGIMM
trap-immediate subsection; mirrors `teq_spec_raw` with `sext16 imm` in
place of `$rt`). -/
theorem teqi_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.teqi rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == signExt16 imm then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tnei` traps iff `$rs ≠ sext16(imm)`** — the mirror image of `teqi`
(REGIMM trap-immediate subsection). -/
theorem tnei_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tnei rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) ≠ signExt16 imm then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tgei` traps iff `$rs ≥s sext16(imm)`**, a *signed* comparison
(REGIMM trap-immediate subsection; mirrors `tge_spec_raw`). -/
theorem tgei_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tgei rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) ≥ asSigned (signExt16 imm) then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tgeiu` sign-extends the 16-bit immediate to a full 32-bit value
first, exactly like `tgei`, then compares the resulting bit patterns as
*unsigned*** — the "u" affects only the comparison, not the immediate's
extension (same convention as `sltiu`; confirmed against `Step.lean`'s
`.tgeiu` case, which calls `signExt16 imm` and then compares `.toNat`
values). -/
theorem tgeiu_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tgeiu rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if (readReg s (regIdxSpec rs)).toNat ≥ (signExt16 imm).toNat then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tlti` traps iff `$rs <s sext16(imm)`**, a *signed* comparison
(REGIMM trap-immediate subsection; mirrors `tlt_spec_raw`). -/
theorem tlti_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tlti rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) < asSigned (signExt16 imm) then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tltiu` sign-extends the 16-bit immediate to a full 32-bit value
first, exactly like `tlti`, then compares the resulting bit patterns as
*unsigned*** — the mirror image of `tgeiu` (same convention as `sltiu`;
confirmed against `Step.lean`'s `.tltiu` case, which calls `signExt16 imm`
and then compares `.toNat` values). -/
theorem tltiu_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tltiu rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if (readReg s (regIdxSpec rs)).toNat < (signExt16 imm).toNat then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `teqi_spec_raw`/`tnei_spec_raw`: `$rs == sext16(imm)` traps under `teqi`
-- (and is a no-op under `tnei`); a mismatch is the mirror image. One
-- `#guard` per instruction per branch, matching the house style used for
-- `teq`/`tne` above.
#guard (match step (prog1Spec (.teqi 8#32 5#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s =>
          s.cp0Epc == textBase && s.cp0Cause == (excCodeTr <<< 2) &&
            s.cp0Status == (statusCu1Mask ||| statusExlMask) && s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.teqi 8#32 5#32))
          (setRegsSpec (initialState textBase) [(8, 6#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.cp0Status == statusCu1Mask
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tnei 8#32 5#32))
          (setRegsSpec (initialState textBase) [(8, 6#32)]) with
        | .next s =>
          s.cp0Epc == textBase && s.cp0Cause == (excCodeTr <<< 2) &&
            s.cp0Status == (statusCu1Mask ||| statusExlMask) && s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tnei 8#32 5#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.cp0Status == statusCu1Mask
        | .halt _ => false) = true

-- `tgei_spec_raw`/`tlti_spec_raw`: `sext16 0xffff = -1`, so `-1` (as
-- `0xffffffff`) is signed-greater-or-equal to `-1` under `tgei` (traps) but
-- not signed-less-than `-1` under `tlti` (no trap); `1 < 1` is false so
-- `tlti 1` also does not trap on `$rs = 1`.
#guard (match step (prog1Spec (.tgei 8#32 0xffff#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tgei 8#32 0xffff#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffe#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tlti 8#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tlti 8#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 1#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true

-- `tgeiu_spec_raw`/`tltiu_spec_raw`: `sext16 1 = 1`, and `0xffffffff` is the
-- *largest* unsigned value, so `$rs = 0xffffffff` is never `<u 1` under
-- `tltiu` but always `≥u 1` under `tgeiu` — the same edge case
-- `sltiu`/`tltu`/`tgeu` above use. A second pair with `sext16 0xffff =
-- 0xffffffff` and `$rs = 1` confirms `tgeiu` really compares unsigned
-- (`1 ≥u 0xffffffff` is false), not signed like `tgei` (where the same
-- inputs trap, since `1 ≥s -1`).
#guard (match step (prog1Spec (.tgeiu 8#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tltiu 8#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tltiu 8#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tgeiu 8#32 0xffff#32))
          (setRegsSpec (initialState textBase) [(8, 1#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tgei 8#32 0xffff#32))
          (setRegsSpec (initialState textBase) [(8, 1#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true


/-! ## Group 6 — single-instruction restatements and the historical
`step_preserves_zero_register_nontrivial`

`step_preserves_zero_register` is now proved structurally in Group 1, for
every instruction at once. This section keeps the single-instruction
`_spec_raw'` restatements that the earlier per-instruction proof of that
invariant used (they are still true, closed theorems about `step`), and
`step_preserves_zero_register_nontrivial` itself, now a one-line corollary. -/

/-- **`lb` sign-extends the loaded byte** (INSTRUCTION-REF "lb" section).
`readMemByte` never fails, so the `none` arm is unreachable; it is kept so
the equation matches `step`'s code. -/
theorem lb_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lb rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemByte s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some b =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) ((BitVec.ofNat 8 b.toNat).signExtend 32)) with
            pc := (writeReg s (regIdxSpec rt) ((BitVec.ofNat 8 b.toNat).signExtend 32)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`lbu` zero-extends the loaded byte** — same address and byte as `lb`, different widening (INSTRUCTION-REF "lbu" section). -/
theorem lbu_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lbu rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemByte s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some b =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) (BitVec.ofNat 32 b.toNat)) with
            pc := (writeReg s (regIdxSpec rt) (BitVec.ofNat 32 b.toNat)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`lh` sign-extends the loaded big-endian halfword**, or raises Address Error (AdEL) on an odd address (INSTRUCTION-REF "lh" section). -/
theorem lh_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lh rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemHalf s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some h =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) (signExt16 h)) with
            pc := (writeReg s (regIdxSpec rt) (signExt16 h)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`lhu` zero-extends the loaded big-endian halfword**, or raises Address Error (AdEL) on an odd address (INSTRUCTION-REF "lhu" section). -/
theorem lhu_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lhu rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemHalf s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some h =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) h) with
            pc := (writeReg s (regIdxSpec rt) h).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **Hypothesis-carrying form of `step_preserves_zero_register`**, kept
under its historical name. It used to be proved by a per-instruction
dispatch over the `_spec_raw` theorems (and was incomplete: 39 instructions
had no case); it is now simply a corollary of the structural theorem
`step_preserves_zero_register` (Group 1), which needs none of the
`hfetch`/`hdecode`/`hpb` hypotheses. -/
theorem step_preserves_zero_register_nontrivial (p : Program) (s s' : State) (w : W32)
    (instr : Instruction)
    (_hfetch : fetchWord p s.pc = some w) (_hdecode : decode w = some instr)
    (_hpb : s.pendingBranch = none)
    (hstep : step p s = StepResult.next s') :
    readReg s' 0 = readReg s 0 :=
  step_preserves_zero_register p s s' hstep

/-! ## Group N+1 — `sync`/`synci` no-ops

`sync` and `synci` are no-ops in this model (`Step.lean`), proved by the same
recipe as `wait_spec_raw` above. -/

/-- **`sync` is a documented no-op**: this single-hart simulator models no
concurrency or out-of-order execution for a memory-ordering barrier to
order anything against, so `sync` just falls through to `pc + 4` like any
ordinary non-control-flow instruction, touching no other state
(`Step.lean`'s `sync` docstring: `mkNext s s`). -/
theorem sync_spec_raw (p : Program) (s : State) (w stype : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sync stype))
    (hpb : s.pendingBranch = none) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`synci` is a documented no-op**: it computes the same effective
address as `lw`/`sw` (`readReg s rs + signExt16 offset`) for architectural
fidelity, but this simulator has no instruction-cache model to flush, so
the address is immediately discarded and `synci` falls through to `pc + 4`
touching no other state at all, not even a memory read (`Step.lean`'s
`synci` docstring). -/
theorem synci_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.synci rs imm))
    (hpb : s.pendingBranch = none) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-! ## Group N — "branch likely" family (`beql bnel blezl bgtzl bltzl bgezl
bltzall bgezall`)

`docs/spec/INSTRUCTION-REF.md` "branch likely" section; `Semantics/
Step.lean`'s module docstring and its `.beql`..`.bgezall` `execInstr` cases.
These eight are architecturally different from every other branch/jump
documented above: a **taken** branch-likely schedules `pendingBranch`
exactly like its non-likely counterpart (the delay slot executes
normally), but a **not-taken** branch-likely does *not* fall through the
ordinary way — its delay-slot instruction is nullified: this same step
moves `pc` straight to `pc + 8` and leaves `pendingBranch = none`, so the
instruction at `pc + 4` is never fetched, decoded or executed. The
nullification is therefore a property of `step` itself (see also
`beql_not_taken_squashes_delay_slot` below). -/

/-- **`beql`/`bnel` step-level shape**: identical field layout and taken
condition to `beq` (`$rs == $rt`), but the not-taken case skips the delay
slot (`pc := pc + 8`, no pending branch) instead of executing it
(INSTRUCTION-REF "beql / bnel" section). -/
theorem beql_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beql rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 8#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bnel`**: the mirror image of `beql` — taken on `$rs ≠ $rt`, squashes
(skips the delay slot (`pc := pc + 8`)) when `$rs == $rt` instead. -/
theorem bnel_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bnel rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        StepResult.next { s with pc := s.pc + 8#32 }
      else
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`blezl`**: same condition as `blez` (`$rs ≤ 0`, signed), not-taken
skips the delay slot (`pc := pc + 8`) instead of falling through plainly. -/
theorem blezl_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.blezl rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) ≤ 0 then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 8#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bgtzl`**: same condition as `bgtz` (`$rs > 0`, signed), not-taken
skips the delay slot (`pc := pc + 8`). -/
theorem bgtzl_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgtzl rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if 0 < asSigned (readReg s (regIdxSpec rs)) then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 8#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bltzl`** (REGIMM `rt = 0x02`): same condition as `bltz` (`$rs < 0`,
signed), not-taken skips the delay slot (`pc := pc + 8`). -/
theorem bltzl_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltzl rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) < 0 then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 8#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bgezl`** (REGIMM `rt = 0x03`): same condition as `bgez` (`$rs ≥ 0`,
signed), not-taken skips the delay slot (`pc := pc + 8`). -/
theorem bgezl_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgezl rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if 0 ≤ asSigned (readReg s (regIdxSpec rs)) then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 8#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bltzall`** (REGIMM `rt = 0x12`): same unconditional-`$ra`-link
convention as `bltzal` (`$ra := PC_next + 4`, written before the
taken/not-taken test, independent of the branch outcome), then the same
`$rs < 0` condition as `bltzl` — not-taken skips the delay slot (`pc := pc + 8`)
instead of plainly falling through, exactly like every other branch-likely
instruction above; the link still happens on the squashed path, matching
INSTRUCTION-REF's explicit note that the link "survives the squash case". -/
theorem bltzall_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltzall rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      let s' := writeReg s 31 (pcNext + 4#32)
      if asSigned (readReg s (regIdxSpec rs)) < 0 then
        StepResult.next { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s' with pc := s.pc + 8#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bgezall`** (REGIMM `rt = 0x13`): same unconditional link as
`bltzall`, mirrored branch condition (`$rs ≥ 0`, same as `bgezl`/`bgezal`).
Not-taken skips the delay slot (`pc := pc + 8`); the link still happens either
way. -/
theorem bgezall_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgezall rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      let s' := writeReg s 31 (pcNext + 4#32)
      if 0 ≤ asSigned (readReg s (regIdxSpec rs)) then
        StepResult.next { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s' with pc := s.pc + 8#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-! ### Satisfiable examples for the branch-likely `_spec_raw` theorems

Same discipline as every other group above: each theorem is instantiated
on a concrete program/state with every hypothesis discharged, via `#guard`
(compiled evaluation). Each pair below exercises both the taken branch
(ordinary `pendingBranch` scheduling) and the not-taken branch (`pc + 8`,
`pendingBranch` left `none`). -/

-- `beql`: `5 == 5` schedules the target with no squash; `5 == 6` is false
-- and squashes instead of plainly falling through (contrast `beq`'s
-- not-taken example above, where the delay slot still executes).
#guard (match step (prog1Spec (.beql 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)]) with
        | .next s =>
          s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.beql 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false) = true

-- `bnel`: opposite polarity to `beql`, same squash mechanism.
#guard (match step (prog1Spec (.bnel 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s =>
          s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bnel 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)]) with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false) = true

-- `blezl`/`bgtzl`: same conditions as `blez`/`bgtz`, squash instead of
-- plain fall-through on not-taken.
#guard (match step (prog1Spec (.blezl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s =>
          s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.blezl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgtzl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s =>
          s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgtzl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false) = true

-- `bltzl`/`bgezl` (REGIMM): same conditions as `bltz`/`bgez`.
#guard (match step (prog1Spec (.bltzl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s =>
          s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bltzl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgezl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s =>
          s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgezl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false) = true

-- `bltzall`/`bgezall` (REGIMM): `$ra` links to `pc + 8` unconditionally in
-- both the taken and squashed cases, mirroring `bltzal`/`bgezal`'s own
-- examples above; the not-taken side lands on `pc + 8` directly.
#guard (match step (prog1Spec (.bltzall 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s =>
          readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bltzall 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s =>
          readReg s 31 == textBase + 8#32 && s.pc == textBase + 8#32 &&
            s.pendingBranch == none
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgezall 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s =>
          readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgezall 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s =>
          readReg s 31 == textBase + 8#32 && s.pc == textBase + 8#32 &&
            s.pendingBranch == none
        | .halt _ => false) = true

/-! ## Branch-likely nullification is a property of `step`

A not-taken branch-likely nullifies its delay-slot instruction. That is
part of the branch-likely's own `step` (it moves `pc` to `pc + 8` and
leaves no pending branch), so the theorem below needs **no hypothesis about
what `p` holds at `s.pc + 4`**: a real instruction, undecodable garbage, or
nothing at all — it is never fetched. `run`, being `step` iterated, agrees. -/

/-- **A not-taken `beql` skips its delay slot in one `step`**, whatever the
program holds there; `run` for one step lands in the same state. -/
theorem beql_not_taken_squashes_delay_slot (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beql rs rt imm))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt)) :
    step p s = StepResult.next { s with pc := s.pc + 8#32 } ∧
      run p s 1 = RunResult.limitReached { s with pc := s.pc + 8#32 } 1 := by
  have hstep : step p s = StepResult.next { s with pc := s.pc + 8#32 } := by
    rw [beql_spec_raw p s w rs rt imm hfetch hdecode hpb]
    simp [hnot]
  refine ⟨hstep, ?_⟩
  show run.go p 1 s 0 = _
  rw [show (1 : Nat) = Nat.succ 0 from rfl, run.go.eq_2, hstep]
  rfl

-- Concrete instance: `prog1Spec` maps *only* `textBase` (the `beql`); there
-- is no instruction at `textBase + 4`. One bare `step` reaches
-- `textBase + 8` with no pending branch and no exception.
#guard (match step (prog1Spec (.beql 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none && s.cp0Status == statusCu1Mask
        | .halt _ => false) = true

/-! ## Floating point (coprocessor 1)

Specifications of every coprocessor-1 instruction, in terms of the bit-level
functions of `Semantics/FpOps.lean` (`Mips.Fp`). Every theorem takes
`hcu : cu1Enabled s = true` (`Status.CU1 = 1`); `fp_coprocessor_unusable`
covers `CU1 = 0` for all of them at once.

How an FP computational instruction completes is stated once, by
`fpCompletesS` / `fpCompletesD` / `fpCompletesCmp` (written here with
`fpeEnabled` / `raiseFlags`, independently of `Step.lean`'s `fpFinish*`,
which go through `fpUpdate`); the per-instruction theorems then only name
the `Mips.Fp` function applied to the operands. -/

/-- Outside a delay slot, completing normally means `pc ← pc + 4`. -/
theorem mkNext_of_none (s x : State) (h : s.pendingBranch = none) :
    mkNext s x = StepResult.next { x with pc := x.pc + 4#32 } := by
  unfold mkNext advance; rw [h]

/-- `execInstr` is `execBody` once its two guards are passed: the instruction
is not a control transfer in a delay slot, and it does not need an unusable
coprocessor 1. -/
theorem execInstr_eq_body (s : State) (instr : Instruction)
    (hnb : isBranchLike instr = false ∨ s.pendingBranch = none)
    (hcu : usesCop1 instr = false ∨ cu1Enabled s = true) :
    execInstr s instr = execBody s instr := by
  have h1 : (isBranchLike instr && s.pendingBranch.isSome) = false := by
    rcases hnb with h | h <;> simp [h]
  have h2 : (usesCop1 instr && !cu1Enabled s) = false := by
    rcases hcu with h | h <;> simp [h]
  unfold execInstr
  rw [h1, h2]
  rfl

/-- FCSR after an FP instruction that traps: `Cause` (bits 17..12) becomes
exactly the exceptions `f` of this operation (`E` clear); nothing else
changes — in particular `Flags` are **not** updated. -/
def fcsrTrapped (fcsr : W32) (f : Mips.Fp.Flags) : W32 :=
  (fcsr &&& ~~~Mips.Fp.fcsrCauseMask) ||| ((f.toBits.zeroExtend 32 : BitVec 32) <<< 12)

/-- **How an FP instruction with a 32-bit result completes** (`r.1` the
result bits for `FPR[fd]`, `r.2` the IEEE exceptions it raised), outside a
delay slot. If one of the exceptions is enabled in FCSR, the Floating Point
exception is taken (ExcCode 15) from a state in which only FCSR.Cause has
changed — **the destination is not written**. Otherwise the result is
written, FCSR.Cause is set to `r.2` and `r.2` is ORed into FCSR.Flags
(`Mips.Fp.raiseFlags`), and `pc` advances
(MD00082 Vol I-A Rev 6.01 §6.7.1, p.98-99; Table 6.8, p.94). -/
def fpCompletesS (s : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags) : StepResult :=
  if Mips.Fp.fpeEnabled s.fcsr r.2 then
    takeException { s with fcsr := fcsrTrapped s.fcsr r.2 } excCodeFPE
  else
    StepResult.next
      { s with fpRegs := s.fpRegs.set! (regIdx fd).val r.1, fcsr := Mips.Fp.raiseFlags s.fcsr r.2,
               pc := s.pc + 4#32 }

/-- As `fpCompletesS`, for a 64-bit result: the low word goes to `FPR[fd]`,
the high word to `FPR[fd+1]` (the `Status.FR = 0` register pair). -/
def fpCompletesD (s : State) (fd : W32) (r : BitVec 64 × Mips.Fp.Flags) : StepResult :=
  if Mips.Fp.fpeEnabled s.fcsr r.2 then
    takeException { s with fcsr := fcsrTrapped s.fcsr r.2 } excCodeFPE
  else
    StepResult.next
      { s with
          fpRegs := (s.fpRegs.set! (regIdx fd).val (r.1.extractLsb' 0 32)).set!
            (regIdx (fd + 1#32)).val (r.1.extractLsb' 32 32)
          fcsr := Mips.Fp.raiseFlags s.fcsr r.2
          pc := s.pc + 4#32 }

/-- As `fpCompletesS`, for a compare: the "result" is the Boolean `r.1`
written to condition code `cc`; no FP register changes. -/
def fpCompletesCmp (s : State) (cc : W32) (r : Bool × Mips.Fp.Flags) : StepResult :=
  if Mips.Fp.fpeEnabled s.fcsr r.2 then
    takeException { s with fcsr := fcsrTrapped s.fcsr r.2 } excCodeFPE
  else
    StepResult.next
      { s with fcsr := Mips.Fp.setCC (Mips.Fp.raiseFlags s.fcsr r.2) (ccIdx cc) r.1,
               pc := s.pc + 4#32 }

theorem fpFinishS_eq (s : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags)
    (hpb : s.pendingBranch = none) : fpFinishS s fd r = fpCompletesS s fd r := by
  unfold fpFinishS fpCompletesS
  dsimp only
  rw [Mips.Fp.fpUpdate_snd]
  by_cases h : Mips.Fp.fpeEnabled s.fcsr r.2 = true
  · rw [ite_of_pos h, ite_of_pos h, Mips.Fp.fpUpdate_fst_of_enabled _ _ h]; rfl
  · have h' : Mips.Fp.fpeEnabled s.fcsr r.2 = false := by simpa using h
    rw [ite_of_neg h, ite_of_neg h, Mips.Fp.fpUpdate_fst_of_not_enabled _ _ h',
      mkNext_of_none _ _ hpb]
    rfl

theorem fpFinishD_eq (s : State) (fd : W32) (r : BitVec 64 × Mips.Fp.Flags)
    (hpb : s.pendingBranch = none) : fpFinishD s fd r = fpCompletesD s fd r := by
  unfold fpFinishD fpCompletesD
  dsimp only
  rw [Mips.Fp.fpUpdate_snd]
  by_cases h : Mips.Fp.fpeEnabled s.fcsr r.2 = true
  · rw [ite_of_pos h, ite_of_pos h, Mips.Fp.fpUpdate_fst_of_enabled _ _ h]; rfl
  · have h' : Mips.Fp.fpeEnabled s.fcsr r.2 = false := by simpa using h
    rw [ite_of_neg h, ite_of_neg h, Mips.Fp.fpUpdate_fst_of_not_enabled _ _ h',
      mkNext_of_none _ _ hpb]
    rfl

theorem fpFinishCmp_eq (s : State) (cc : W32) (r : Bool × Mips.Fp.Flags)
    (hpb : s.pendingBranch = none) : fpFinishCmp s cc r = fpCompletesCmp s cc r := by
  unfold fpFinishCmp fpCompletesCmp
  dsimp only
  rw [Mips.Fp.fpUpdate_snd]
  by_cases h : Mips.Fp.fpeEnabled s.fcsr r.2 = true
  · rw [ite_of_pos h, ite_of_pos h, Mips.Fp.fpUpdate_fst_of_enabled _ _ h]; rfl
  · have h' : Mips.Fp.fpeEnabled s.fcsr r.2 = false := by simpa using h
    rw [ite_of_neg h, ite_of_neg h, Mips.Fp.fpUpdate_fst_of_not_enabled _ _ h',
      mkNext_of_none _ _ hpb]

/-! ### General theorems -/

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

/-! ### Arithmetic -/

/-- **`add.s`: `fd ← fs + ft`**, single precision: the result bits and exceptions are
`Mips.Fp.f32Add` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, ADD.fmt, p.34) -/
theorem addS_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.addS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd
        (Mips.Fp.f32Add (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`sub.s`: `fd ← fs − ft`**, single precision: the result bits and exceptions are
`Mips.Fp.f32Sub` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, SUB.fmt, p.389) -/
theorem subS_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.subS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd
        (Mips.Fp.f32Sub (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`mul.s`: `fd ← fs × ft`**, single precision: the result bits and exceptions are
`Mips.Fp.f32Mul` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, MUL.fmt, p.302) -/
theorem mulS_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mulS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd
        (Mips.Fp.f32Mul (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`div.s`: `fd ← fs / ft`**, single precision: the result bits and exceptions are
`Mips.Fp.f32Div` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, DIV.fmt, p.170) -/
theorem divS_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.divS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd
        (Mips.Fp.f32Div (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`sqrt.s`**: `Mips.Fp.f32Sqrt` of the operand, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, SQRT.fmt, p.382). -/
theorem sqrtS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sqrtS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f32Sqrt (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`recip.s`**: `Mips.Fp.f32Recip` of the operand, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, RECIP.fmt, p.336). -/
theorem recipS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.recipS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f32Recip (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`rsqrt.s`**: `Mips.Fp.f32Rsqrt` of the operand, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, RSQRT.fmt, p.343). -/
theorem rsqrtS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.rsqrtS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f32Rsqrt (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`abs.s`**: `Mips.Fp.f32Abs` of the operand, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, ABS.fmt, p.32). Arithmetic (`FIR.Has2008 = 0`): any NaN operand signals Invalid Operation. -/
theorem absS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.absS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f32Abs (readFpReg s (regIdx fs))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`neg.s`**: `Mips.Fp.f32Neg` of the operand, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, NEG.fmt, p.307). Arithmetic (`FIR.Has2008 = 0`): any NaN operand signals Invalid Operation. -/
theorem negS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.negS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f32Neg (readFpReg s (regIdx fs))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`madd.s`** (unfused: multiply, round, add/subtract, round):
`Mips.Fp.f32Madd` of `fr`, `fs`, `ft`, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310) -/
theorem maddS_spec_raw (p : Program) (s : State) (w fd fr fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.maddS fd fr fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd
        (Mips.Fp.f32Madd (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fr)) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`msub.s`** (unfused: multiply, round, add/subtract, round):
`Mips.Fp.f32Msub` of `fr`, `fs`, `ft`, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310) -/
theorem msubS_spec_raw (p : Program) (s : State) (w fd fr fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.msubS fd fr fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd
        (Mips.Fp.f32Msub (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fr)) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`nmadd.s`** (unfused: multiply, round, add/subtract, round, negate):
`Mips.Fp.f32Nmadd` of `fr`, `fs`, `ft`, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310) -/
theorem nmaddS_spec_raw (p : Program) (s : State) (w fd fr fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.nmaddS fd fr fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd
        (Mips.Fp.f32Nmadd (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fr)) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`nmsub.s`** (unfused: multiply, round, add/subtract, round, negate):
`Mips.Fp.f32Nmsub` of `fr`, `fs`, `ft`, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310) -/
theorem nmsubS_spec_raw (p : Program) (s : State) (w fd fr fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.nmsubS fd fr fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd
        (Mips.Fp.f32Nmsub (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fr)) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`add.d`: `fd ← fs + ft`**, double precision: the result bits and exceptions are
`Mips.Fp.f64Add` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, ADD.fmt, p.34) -/
theorem addD_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.addD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesD s fd
        (Mips.Fp.f64Add (Mips.Fp.envOf s.fcsr) (readFpD s fs) (readFpD s ft)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishD_eq s fd _ hpb

/-- **`sub.d`: `fd ← fs − ft`**, double precision: the result bits and exceptions are
`Mips.Fp.f64Sub` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, SUB.fmt, p.389) -/
theorem subD_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.subD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesD s fd
        (Mips.Fp.f64Sub (Mips.Fp.envOf s.fcsr) (readFpD s fs) (readFpD s ft)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishD_eq s fd _ hpb

/-- **`mul.d`: `fd ← fs × ft`**, double precision: the result bits and exceptions are
`Mips.Fp.f64Mul` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, MUL.fmt, p.302) -/
theorem mulD_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mulD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesD s fd
        (Mips.Fp.f64Mul (Mips.Fp.envOf s.fcsr) (readFpD s fs) (readFpD s ft)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishD_eq s fd _ hpb

/-- **`div.d`: `fd ← fs / ft`**, double precision: the result bits and exceptions are
`Mips.Fp.f64Div` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, DIV.fmt, p.170) -/
theorem divD_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.divD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesD s fd
        (Mips.Fp.f64Div (Mips.Fp.envOf s.fcsr) (readFpD s fs) (readFpD s ft)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishD_eq s fd _ hpb

/-- **`sqrt.d`**: `Mips.Fp.f64Sqrt` of the operand, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, SQRT.fmt, p.382). -/
theorem sqrtD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sqrtD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesD s fd (Mips.Fp.f64Sqrt (Mips.Fp.envOf s.fcsr) (readFpD s fs)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishD_eq s fd _ hpb

/-- **`recip.d`**: `Mips.Fp.f64Recip` of the operand, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, RECIP.fmt, p.336). -/
theorem recipD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.recipD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesD s fd (Mips.Fp.f64Recip (Mips.Fp.envOf s.fcsr) (readFpD s fs)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishD_eq s fd _ hpb

/-- **`rsqrt.d`**: `Mips.Fp.f64Rsqrt` of the operand, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, RSQRT.fmt, p.343). -/
theorem rsqrtD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.rsqrtD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesD s fd (Mips.Fp.f64Rsqrt (Mips.Fp.envOf s.fcsr) (readFpD s fs)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishD_eq s fd _ hpb

/-- **`abs.d`**: `Mips.Fp.f64Abs` of the operand, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, ABS.fmt, p.32). Arithmetic (`FIR.Has2008 = 0`): any NaN operand signals Invalid Operation. -/
theorem absD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.absD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesD s fd (Mips.Fp.f64Abs (readFpD s fs)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishD_eq s fd _ hpb

/-- **`neg.d`**: `Mips.Fp.f64Neg` of the operand, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, NEG.fmt, p.307). Arithmetic (`FIR.Has2008 = 0`): any NaN operand signals Invalid Operation. -/
theorem negD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.negD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesD s fd (Mips.Fp.f64Neg (readFpD s fs)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishD_eq s fd _ hpb

/-- **`madd.d`** (unfused: multiply, round, add/subtract, round):
`Mips.Fp.f64Madd` of `fr`, `fs`, `ft`, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310) -/
theorem maddD_spec_raw (p : Program) (s : State) (w fd fr fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.maddD fd fr fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesD s fd
        (Mips.Fp.f64Madd (Mips.Fp.envOf s.fcsr) (readFpD s fr) (readFpD s fs) (readFpD s ft)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishD_eq s fd _ hpb

/-- **`msub.d`** (unfused: multiply, round, add/subtract, round):
`Mips.Fp.f64Msub` of `fr`, `fs`, `ft`, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310) -/
theorem msubD_spec_raw (p : Program) (s : State) (w fd fr fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.msubD fd fr fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesD s fd
        (Mips.Fp.f64Msub (Mips.Fp.envOf s.fcsr) (readFpD s fr) (readFpD s fs) (readFpD s ft)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishD_eq s fd _ hpb

/-- **`nmadd.d`** (unfused: multiply, round, add/subtract, round, negate):
`Mips.Fp.f64Nmadd` of `fr`, `fs`, `ft`, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310) -/
theorem nmaddD_spec_raw (p : Program) (s : State) (w fd fr fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.nmaddD fd fr fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesD s fd
        (Mips.Fp.f64Nmadd (Mips.Fp.envOf s.fcsr) (readFpD s fr) (readFpD s fs) (readFpD s ft)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishD_eq s fd _ hpb

/-- **`nmsub.d`** (unfused: multiply, round, add/subtract, round, negate):
`Mips.Fp.f64Nmsub` of `fr`, `fs`, `ft`, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310) -/
theorem nmsubD_spec_raw (p : Program) (s : State) (w fd fr fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.nmsubD fd fr fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesD s fd
        (Mips.Fp.f64Nmsub (Mips.Fp.envOf s.fcsr) (readFpD s fr) (readFpD s fs) (readFpD s ft)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishD_eq s fd _ hpb

/-! ### Conversions -/

/-- **`round.w.s`** converts to a 32-bit word rounding to nearest even, whatever FCSR.RM is:
`Mips.Fp.f32ToW32 .RN`. NaN, ±∞ and out-of-range values give `0x7FFFFFFF` with
Invalid Operation (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem roundWS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.roundWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f32ToW32 .RN (readFpReg s (regIdx fs))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`trunc.w.s`** converts to a 32-bit word rounding toward zero, whatever FCSR.RM is:
`Mips.Fp.f32ToW32 .RZ`. NaN, ±∞ and out-of-range values give `0x7FFFFFFF` with
Invalid Operation (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem truncWS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.truncWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f32ToW32 .RZ (readFpReg s (regIdx fs))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`ceil.w.s`** converts to a 32-bit word rounding toward +∞, whatever FCSR.RM is:
`Mips.Fp.f32ToW32 .RP`. NaN, ±∞ and out-of-range values give `0x7FFFFFFF` with
Invalid Operation (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem ceilWS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ceilWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f32ToW32 .RP (readFpReg s (regIdx fs))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`floor.w.s`** converts to a 32-bit word rounding toward −∞, whatever FCSR.RM is:
`Mips.Fp.f32ToW32 .RM`. NaN, ±∞ and out-of-range values give `0x7FFFFFFF` with
Invalid Operation (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem floorWS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.floorWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f32ToW32 .RM (readFpReg s (regIdx fs))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`cvt.w.s`** converts to a 32-bit word rounding **per FCSR.RM**
(MD00086 Vol II-A Rev 6.06, CVT.W.fmt, p.160): `Mips.Fp.f32ToW32 (getRM fcsr)` -/
theorem cvtWS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cvtWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f32ToW32 (Mips.Fp.getRM s.fcsr) (readFpReg s (regIdx fs))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`round.w.d`** converts to a 32-bit word rounding to nearest even, whatever FCSR.RM is:
`Mips.Fp.f64ToW32 .RN`. NaN, ±∞ and out-of-range values give `0x7FFFFFFF` with
Invalid Operation (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem roundWD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.roundWD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f64ToW32 .RN (readFpD s fs)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`trunc.w.d`** converts to a 32-bit word rounding toward zero, whatever FCSR.RM is:
`Mips.Fp.f64ToW32 .RZ`. NaN, ±∞ and out-of-range values give `0x7FFFFFFF` with
Invalid Operation (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem truncWD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.truncWD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f64ToW32 .RZ (readFpD s fs)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`ceil.w.d`** converts to a 32-bit word rounding toward +∞, whatever FCSR.RM is:
`Mips.Fp.f64ToW32 .RP`. NaN, ±∞ and out-of-range values give `0x7FFFFFFF` with
Invalid Operation (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem ceilWD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ceilWD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f64ToW32 .RP (readFpD s fs)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`floor.w.d`** converts to a 32-bit word rounding toward −∞, whatever FCSR.RM is:
`Mips.Fp.f64ToW32 .RM`. NaN, ±∞ and out-of-range values give `0x7FFFFFFF` with
Invalid Operation (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem floorWD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.floorWD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f64ToW32 .RM (readFpD s fs)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`cvt.w.d`** converts to a 32-bit word rounding **per FCSR.RM**
(MD00086 Vol II-A Rev 6.06, CVT.W.fmt, p.160): `Mips.Fp.f64ToW32 (getRM fcsr)` -/
theorem cvtWD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cvtWD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f64ToW32 (Mips.Fp.getRM s.fcsr) (readFpD s fs)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`cvt.s.w`**: word → single, correctly rounded under FCSR (`Mips.Fp.w32ToF32`) -/
theorem cvtSW_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cvtSW fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.w32ToF32 (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-- **`cvt.d.w`**: word → double, always exact (`Mips.Fp.w32ToF64`); raises nothing -/
theorem cvtDW_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cvtDW fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesD s fd (Mips.Fp.w32ToF64 (readFpReg s (regIdx fs)), Mips.Fp.Flags.none) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishD_eq s fd _ hpb

/-- **`cvt.d.s`**: single → double (`Mips.Fp.f32ToF64`): exact; a quiet NaN keeps its sign and
payload, a signaling NaN signals Invalid -/
theorem cvtDS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cvtDS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesD s fd (Mips.Fp.f32ToF64 (readFpReg s (regIdx fs))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishD_eq s fd _ hpb

/-- **`cvt.s.d`**: double → single, correctly rounded under FCSR (`Mips.Fp.f64ToF32`) -/
theorem cvtSD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cvtSD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f64ToF32 (Mips.Fp.envOf s.fcsr) (readFpD s fs)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishS_eq s fd _ hpb

/-! ### Compare -/

/-- **`c.cond.s`** writes `FCC[cc]` with predicate `cond` (its low four bits) of the two singles:
`Mips.Fp.f32Compare`, completing per `fpCompletesCmp` (MD00086 Vol II-A Rev 6.06,
C.cond.fmt, p.110-113). `fpCompletesCmp_ok` says only `FCC[cc]` changes -/
theorem cCondS_spec_raw (p : Program) (s : State) (w cond cc fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cCondS cond cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesCmp s cc
        (Mips.Fp.f32Compare (cond.setWidth 4) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishCmp_eq s cc _ hpb

/-- **`c.cond.d`**: as `cCondS_spec_raw`, on doubles (`Mips.Fp.f64Compare`) -/
theorem cCondD_spec_raw (p : Program) (s : State) (w cond cc fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cCondD cond cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesCmp s cc (Mips.Fp.f64Compare (cond.setWidth 4) (readFpD s fs) (readFpD s ft)) := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  exact fpFinishCmp_eq s cc _ hpb

/-! ### Moves (non-arithmetic: FCSR untouched) -/

/-- **`mfc1`**: `$rt ← FPR[fs]`, raw bits -/
theorem mfc1_spec_raw (p : Program) (s : State) (w rt fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mfc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      StepResult.next { (writeReg s (regIdx rt) (readFpReg s (regIdx fs))) with pc := (writeReg s (regIdx rt) (readFpReg s (regIdx fs))).pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`mtc1`**: `FPR[fs] ← $rt`, raw bits -/
theorem mtc1_spec_raw (p : Program) (s : State) (w rt fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mtc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      StepResult.next { (writeFpReg s (regIdx fs) (readReg s (regIdx rt))) with pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`mfhc1`**: `$rt ←` the high word of the double in `fs`, i.e. `FPR[fs+1]`
(MD00086 Vol II-A Rev 6.06, MFHC1, p.271) -/
theorem mfhc1_spec_raw (p : Program) (s : State) (w rt fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mfhc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      StepResult.next { (writeReg s (regIdx rt) (readFpReg s (regIdx (fs + 1#32)))) with pc := (writeReg s (regIdx rt) (readFpReg s (regIdx (fs + 1#32)))).pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`mthc1`**: the high word of the double in `fs` (`FPR[fs+1]`) `← $rt`; `FPR[fs]` is kept
(MD00086 Vol II-A Rev 6.06, MTHC1, p.295) -/
theorem mthc1_spec_raw (p : Program) (s : State) (w rt fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mthc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      StepResult.next { (writeFpReg s (regIdx (fs + 1#32)) (readReg s (regIdx rt))) with pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`mov.s`**: raw copy; an SNaN is copied without signaling -/
theorem movS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      StepResult.next { (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))) with pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`mov.d`**: raw copy of the register pair -/
theorem movD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      StepResult.next { (writeFpD s fd (readFpD s fs)) with pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`movf.s`**: `if FCC[cc] = 0 then fd ← fs`; otherwise nothing changes but `pc`
(MD00086 Vol II-A Rev 6.06, MOVF.fmt, p.277) -/
theorem movfS_spec_raw (p : Program) (s : State) (w fd fs cc : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movfS fd fs cc))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      if readFcc s cc then StepResult.next { s with pc := s.pc + 4#32 }
      else StepResult.next { (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))) with pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`movt.s`**: `if FCC[cc] = 1 then fd ← fs` -/
theorem movtS_spec_raw (p : Program) (s : State) (w fd fs cc : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movtS fd fs cc))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      if readFcc s cc then StepResult.next { (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))) with pc := s.pc + 4#32 }
      else StepResult.next { s with pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`movn.s`**: `if $rt ≠ 0 then fd ← fs` -/
theorem movnS_spec_raw (p : Program) (s : State) (w fd fs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movnS fd fs rt))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      if readReg s (regIdx rt) != 0#32 then StepResult.next { (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))) with pc := s.pc + 4#32 }
      else StepResult.next { s with pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`movz.s`**: `if $rt = 0 then fd ← fs` -/
theorem movzS_spec_raw (p : Program) (s : State) (w fd fs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movzS fd fs rt))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      if readReg s (regIdx rt) == 0#32 then StepResult.next { (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))) with pc := s.pc + 4#32 }
      else StepResult.next { s with pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`movf.d`**: `if FCC[cc] = 0 then fd ← fs`; otherwise nothing changes but `pc`
(MD00086 Vol II-A Rev 6.06, MOVF.fmt, p.277) -/
theorem movfD_spec_raw (p : Program) (s : State) (w fd fs cc : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movfD fd fs cc))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      if readFcc s cc then StepResult.next { s with pc := s.pc + 4#32 }
      else StepResult.next { (writeFpD s fd (readFpD s fs)) with pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`movt.d`**: `if FCC[cc] = 1 then fd ← fs` -/
theorem movtD_spec_raw (p : Program) (s : State) (w fd fs cc : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movtD fd fs cc))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      if readFcc s cc then StepResult.next { (writeFpD s fd (readFpD s fs)) with pc := s.pc + 4#32 }
      else StepResult.next { s with pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`movn.d`**: `if $rt ≠ 0 then fd ← fs` -/
theorem movnD_spec_raw (p : Program) (s : State) (w fd fs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movnD fd fs rt))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      if readReg s (regIdx rt) != 0#32 then StepResult.next { (writeFpD s fd (readFpD s fs)) with pc := s.pc + 4#32 }
      else StepResult.next { s with pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`movz.d`**: `if $rt = 0 then fd ← fs` -/
theorem movzD_spec_raw (p : Program) (s : State) (w fd fs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movzD fd fs rt))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      if readReg s (regIdx rt) == 0#32 then StepResult.next { (writeFpD s fd (readFpD s fs)) with pc := s.pc + 4#32 }
      else StepResult.next { s with pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`movf`** (GPR): `if FCC[cc] = 0 then $rd ← $rs` (MD00086 Vol II-A Rev 6.06, MOVF, p.276) -/
theorem movf_spec_raw (p : Program) (s : State) (w rs cc rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movf rs cc rd))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      if readFcc s cc then StepResult.next { s with pc := s.pc + 4#32 }
      else
        StepResult.next
          { (writeReg s (regIdx rd) (readReg s (regIdx rs))) with
            pc := (writeReg s (regIdx rd) (readReg s (regIdx rs))).pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`movt`** (GPR): `if FCC[cc] = 1 then $rd ← $rs` (MD00086 Vol II-A Rev 6.06, MOVT, p.281) -/
theorem movt_spec_raw (p : Program) (s : State) (w rs cc rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movt rs cc rd))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      if readFcc s cc then
        StepResult.next
          { (writeReg s (regIdx rd) (readReg s (regIdx rs))) with
            pc := (writeReg s (regIdx rd) (readReg s (regIdx rs))).pc + 4#32 }
      else StepResult.next { s with pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-! ### Control registers -/

/-- **`cfc1`**: `$rt ←` FP control register `fs` — `Mips.Fp.readControl`: FIR (0), FCCR (25),
FEXR (26), FENR (28), FCSR (31); any other number reads 0 (pin for UNPREDICTABLE)
(MD00086 Vol II-A Rev 6.06, CFC1, p.129-130) -/
theorem cfc1_spec_raw (p : Program) (s : State) (w rt fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cfc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      StepResult.next { (writeReg s (regIdx rt) ((Mips.Fp.readControl s.fcsr fs.toNat).getD 0#32)) with pc := (writeReg s (regIdx rt) ((Mips.Fp.readControl s.fcsr fs.toNat).getD 0#32)).pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`ctc1`**: FP control register `fs ← $rt` through `Mips.Fp.writeControl`, then
`CheckFPException`: if the new FCSR has a Cause bit whose Enable is set, or Cause.E, the
Floating Point exception is taken **with the register already written**. A register
number the manual leaves UNPREDICTABLE is a no-op (pin)
(MD00086 Vol II-A Rev 6.06, CTC1, p.149-151) -/
theorem ctc1_spec_raw (p : Program) (s : State) (w rt fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ctc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      match Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt)) with
      | none => StepResult.next { s with pc := s.pc + 4#32 }
      | some f =>
        if Mips.Fp.fcsrTrapPending f then takeException { s with fcsr := f } excCodeFPE
        else StepResult.next { s with fcsr := f, pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **FCSR round trip through `ctc1 $rt, $31` / `cfc1 $rt, $31`.** Writing `v`
to control register 31 makes FCSR `v` with the reserved bits 22..18 cleared
(`Mips.Fp.fcsrWritableMask`), and reading register 31 of that FCSR returns
exactly that value. -/
theorem fcsr_ctc1_cfc1_roundtrip (fcsr v : W32) :
    ∃ f, Mips.Fp.writeControl fcsr 31 v = some f ∧ f = v &&& Mips.Fp.fcsrWritableMask ∧
      Mips.Fp.readControl f 31 = some (v &&& Mips.Fp.fcsrWritableMask) := by
  refine ⟨v &&& Mips.Fp.fcsrWritableMask, rfl, rfl, ?_⟩
  have h := Mips.Fp.readControl_writeControl_fcsr fcsr v
  simpa [Mips.Fp.writeControl, Mips.Fp.writeFCSR] using h

/-- The round trip at the level of `step`: after `ctc1 $rt, $31` completes
without a pending FP exception, the state's FCSR is `$rt` masked to the
writable bits. -/
theorem ctc1_fcsr_spec (p : Program) (s : State) (w rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ctc1 rt 31#32))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hnt : Mips.Fp.fcsrTrapPending (readReg s (regIdx rt) &&& Mips.Fp.fcsrWritableMask) = false) :
    step p s =
      StepResult.next
        { s with fcsr := readReg s (regIdx rt) &&& Mips.Fp.fcsrWritableMask, pc := s.pc + 4#32 } := by
  rw [ctc1_spec_raw p s w rt 31#32 hfetch hdecode hpb hcu]
  show (if Mips.Fp.fcsrTrapPending (readReg s (regIdx rt) &&& Mips.Fp.fcsrWritableMask) = true
    then _ else _) = _
  rw [ite_of_neg (by simp [hnt])]
  rfl

/-- … and `cfc1 $rt, $31` reads the FCSR back (its reserved bits as zero). -/
theorem cfc1_fcsr_spec (p : Program) (s : State) (w rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cfc1 rt 31#32))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      StepResult.next
        { (writeReg s (regIdx rt) (s.fcsr &&& Mips.Fp.fcsrWritableMask)) with
          pc := (writeReg s (regIdx rt) (s.fcsr &&& Mips.Fp.fcsrWritableMask)).pc + 4#32 } :=
  cfc1_spec_raw p s w rt 31#32 hfetch hdecode hpb hcu

/-! ### Loads, stores, prefetch -/

/-- **`lwc1`**: `FPR[ft] ← MEM32[$rs + sext(imm)]`; Address Error (AdEL) if not word-aligned -/
theorem lwc1_spec_raw (p : Program) (s : State) (w rs ft imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lwc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      let addr := readReg s (regIdx rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v => StepResult.next { (writeFpReg s (regIdx ft) v) with pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`swc1`**: `MEM32[$rs + sext(imm)] ← FPR[ft]`; Address Error (AdES) if not word-aligned;
clears `LLbit` like every store -/
theorem swc1_spec_raw (p : Program) (s : State) (w rs ft imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.swc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      let addr := readReg s (regIdx rs) + signExt16 imm
      match writeMemWord s addr (readFpReg s (regIdx ft)) with
      | none => takeAddressException s excCodeAdES addr
      | some s' => StepResult.next { s' with llBit := false, pc := s'.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`ldc1`**: loads a big-endian doubleword into the pair (`FPR[ft+1]` ← the word at `addr`,
`FPR[ft]` ← the word at `addr + 4`). **Address Error if `addr` is not a multiple of 8**
(MD00086 Vol II-A Rev 6.06, LDC1, p.215) -/
theorem ldc1_spec_raw (p : Program) (s : State) (w rs ft imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ldc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      let addr := readReg s (regIdx rs) + signExt16 imm
      if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdEL addr
      else
        match readMemWord s addr, readMemWord s (addr + 4#32) with
        | some hi, some lo =>
          StepResult.next { (writeFpReg (writeFpReg s (regIdx ft) lo) (regIdx (ft + 1#32)) hi) with pc := s.pc + 4#32 }
        | _, _ => takeAddressException s excCodeAdEL addr := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`sdc1`**: stores the pair as a big-endian doubleword. **Address Error if `addr` is not a
multiple of 8** (MD00086 Vol II-A Rev 6.06, SDC1, p.362) -/
theorem sdc1_spec_raw (p : Program) (s : State) (w rs ft imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sdc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      let addr := readReg s (regIdx rs) + signExt16 imm
      if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdES addr
      else
        match writeMemWord s addr (readFpReg s (regIdx (ft + 1#32))) with
        | none => takeAddressException s excCodeAdES addr
        | some s' =>
          match writeMemWord s' (addr + 4#32) (readFpReg s (regIdx ft)) with
          | none => takeAddressException s excCodeAdES addr
          | some s'' => StepResult.next { s'' with llBit := false, pc := s''.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`lwxc1`**: as `lwc1` with the address `$base + $index` (MD00086 Vol II-A Rev 6.06, LWXC1, p.254) -/
theorem lwxc1_spec_raw (p : Program) (s : State) (w fd index base : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lwxc1 fd index base))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      let addr := readReg s (regIdx base) + readReg s (regIdx index)
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v => StepResult.next { (writeFpReg s (regIdx fd) v) with pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`ldxc1`**: as `ldc1` with the address `$base + $index` (MD00086 Vol II-A Rev 6.06, LDXC1, p.218) -/
theorem ldxc1_spec_raw (p : Program) (s : State) (w fd index base : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ldxc1 fd index base))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      let addr := readReg s (regIdx base) + readReg s (regIdx index)
      if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdEL addr
      else
        match readMemWord s addr, readMemWord s (addr + 4#32) with
        | some hi, some lo =>
          StepResult.next { (writeFpReg (writeFpReg s (regIdx fd) lo) (regIdx (fd + 1#32)) hi) with pc := s.pc + 4#32 }
        | _, _ => takeAddressException s excCodeAdEL addr := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`swxc1`**: as `swc1` with the address `$base + $index` (MD00086 Vol II-A Rev 6.06, SWXC1, p.406) -/
theorem swxc1_spec_raw (p : Program) (s : State) (w fs index base : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.swxc1 fs index base))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      let addr := readReg s (regIdx base) + readReg s (regIdx index)
      match writeMemWord s addr (readFpReg s (regIdx fs)) with
      | none => takeAddressException s excCodeAdES addr
      | some s' => StepResult.next { s' with llBit := false, pc := s'.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`sdxc1`**: as `sdc1` with the address `$base + $index` (MD00086 Vol II-A Rev 6.06, SDXC1, p.364) -/
theorem sdxc1_spec_raw (p : Program) (s : State) (w fs index base : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sdxc1 fs index base))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      let addr := readReg s (regIdx base) + readReg s (regIdx index)
      if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdES addr
      else
        match writeMemWord s addr (readFpReg s (regIdx (fs + 1#32))) with
        | none => takeAddressException s excCodeAdES addr
        | some s' =>
          match writeMemWord s' (addr + 4#32) (readFpReg s (regIdx fs)) with
          | none => takeAddressException s excCodeAdES addr
          | some s'' => StepResult.next { s'' with llBit := false, pc := s''.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`prefx`** is a no-op (but, being a COP1X instruction, it needs `Status.CU1`)
(MD00086 Vol II-A Rev 6.06, PREFX, p.329) -/
theorem prefx_spec_raw (p : Program) (s : State) (w hint index base : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.prefx hint index base))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      StepResult.next { s with pc := s.pc + 4#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-! ### Branches on a condition code -/

/-- **`bc1f`**: branch if `FCC[cc] = 0`, with the ordinary delay slot (MD00086 Vol II-A Rev 6.06,
BC1F, p.56) -/
theorem bc1f_spec_raw (p : Program) (s : State) (w cc imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bc1f cc imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      if readFcc s cc then StepResult.next { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }
      else
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 imm <<< 2)) } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`bc1t`**: branch if `FCC[cc] = 1`, with the ordinary delay slot (MD00086 Vol II-A Rev 6.06,
BC1T, p.60) -/
theorem bc1t_spec_raw (p : Program) (s : State) (w cc imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bc1t cc imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      if readFcc s cc then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 imm <<< 2)) }
      else StepResult.next { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`bc1fl`**: branch-likely if `FCC[cc] = 0`; **when not taken the delay slot is nullified**
(`pc ← pc + 8`, nothing pending) (MD00086 Vol II-A Rev 6.06, BC1FL, p.58) -/
theorem bc1fl_spec_raw (p : Program) (s : State) (w cc imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bc1fl cc imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      if readFcc s cc then StepResult.next { s with pc := s.pc + 8#32 }
      else
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 imm <<< 2)) } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl

/-- **`bc1tl`**: branch-likely if `FCC[cc] = 1`; when not taken the delay slot is nullified
(MD00086 Vol II-A Rev 6.06, BC1TL, p.62) -/
theorem bc1tl_spec_raw (p : Program) (s : State) (w cc imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bc1tl cc imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      if readFcc s cc then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 imm <<< 2)) }
      else StepResult.next { s with pc := s.pc + 8#32 } := by
  unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  rfl
