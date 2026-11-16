import Semantics.Specs.Lemmas

/-!
# Exception — exception entry

What `exceptionEntry` / `takeException` / `takeAddressException` do, in each of the cases
`Status.EXL` = 0/1, in a delay slot or not, `Status.BEV` (MD00090 "General Exception Processing",
as cited in the theorems' docstrings). No theorem here assumes `s.pendingBranch = none`.

## Theorems in this file (12)

  `exceptionEntry_always` `exceptionVector_reset` `exception_keeps_llBit`
  `exceptionEntry_exl0_not_in_delay_slot` `exceptionEntry_exl0_in_delay_slot` `exceptionEntry_exl1`
  `exceptionEntry_excCode` `exceptionEntry_ce` `exceptionEntry_cause_other_bits`
  `exceptionEntry_badInstr` `exceptionEntry_badInstr_fetched` `takeInterrupt_badInstr_unchanged`
-/

set_option maxRecDepth 4000

/-! ## Exception entry (MD00090 "General Exception Processing")

`takeException s code` is `(exceptionEntry s code)`;
`takeAddressException s code addr` additionally sets `BadVAddr := addr`
first. The theorems below say what `exceptionEntry` does in each of the
cases `Status.EXL = 0/1` × in a delay slot / not, and with `Status.BEV`. -/

/-- **What exception entry always does**, whatever `EXL`, the delay-slot
status and the coprocessor number `ce`: `PC ←` the general vector (`EBase`'s
base with offset `0x180` — `0x80000180` at reset — or `0xBFC00380` when
`Status.BEV = 1`); `Status.EXL ← 1` (no other `Status` bit changes); **the
pending branch is abandoned**; and nothing else outside `EPC`/`Cause` (and
`BadInstr`/`BadInstrP`, `exceptionEntry_badInstr`) is touched — no general register,
memory, FP register, `FCSR`, `LLbit`, `BadVAddr`, `ErrorEPC`, `EBase` or the LL address.
**`LLbit` is unchanged**: exception entry does not clear it; the SC failure conditions list
"An ERET instruction is executed. (Release 5 includes ERETNC, which will not cause the SC to
fail.)" (MD00086 Vol II-A Rev 6.06, SC, p.347), so a handler that returns with `eret` makes the
`sc` fail (`eret_clears_llBit`) and one that returns with `eretnc` does not (`eretnc_keeps_llBit`;
ERETNC "will never cause the SC to fail", ERETNC, p.179). -/
theorem exceptionEntry_always (s : State) (code ce : W32) :
    (exceptionEntry s code ce).pc =
        (if s.cp0Status &&& statusBevMask == 0#32 then
          ((s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32) ||| 0x180#32
         else 0xBFC00380#32) ∧
      (exceptionEntry s code ce).cp0Status = s.cp0Status ||| statusExlMask ∧
      (exceptionEntry s code ce).pendingBranch = none ∧
      (exceptionEntry s code ce).regs = s.regs ∧
      (exceptionEntry s code ce).physMem = s.physMem ∧
      (exceptionEntry s code ce).fpRegs = s.fpRegs ∧
      (exceptionEntry s code ce).fcsr = s.fcsr ∧
      (exceptionEntry s code ce).llBit = s.llBit ∧
      (exceptionEntry s code ce).cp0BadVAddr = s.cp0BadVAddr ∧
      (exceptionEntry s code ce).cp0ErrorEpc = s.cp0ErrorEpc ∧
      (exceptionEntry s code ce).cp0EBase = s.cp0EBase ∧
      (exceptionEntry s code ce).llAddr = s.llAddr :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- With `EBase` at its reset value the general vector is the classic
`0x80000180`. -/
theorem exceptionVector_reset (s : State) (hbev : s.cp0Status &&& statusBevMask = 0#32)
    (heb : s.cp0EBase = 0x80000000#32) : exceptionVector s = 0x80000180#32 := by
  simp [exceptionVector, ebaseValue, hbev, heb]; decide

/-- **No exception changes `LLbit`** (MD00086 Vol II-A Rev 6.06, SC, p.347: the events that make
an SC fail include "An ERET instruction is executed", not the exception itself; the return from the
handler decides: `eret_clears_llBit`, `eretnc_keeps_llBit`). Stated for both exception forms `step`
uses. -/
theorem exception_keeps_llBit (s s' : State) (code addr : W32)
    (h : takeException s code = s' ∨
      takeAddressException s code addr = s') :
    s'.llBit = s.llBit := by
  rcases h with h | h <;> (have h := h; rw [← h]; rfl)

/-- **A synchronous exception records the faulting instruction in `BadInstr` and, in a delay slot,
the branch in `BadInstrP`** (MD00090 Vol III Rev 6.02 §9.25, p.179: BadInstr is "Faulting
instruction word", "only set by exceptions which are synchronous to an instruction"; §9.26, p.181:
BadInstrP "contains the prior branch instruction, when the faulting instruction is in a branch delay
slot"). `exceptionEntry` with its default `sync := true` is every exception the model raises but the
Interrupt (`takeInterrupt_badInstr_unchanged`): `BadInstr ← faultingInstr s` (the word fetched at
`pc`; 0 when that fetch fails, where "the value stored in BadInstr is UNPREDICTABLE", p.179, pin);
`BadInstrP ←` the word at `pc - 4` (`instrWordAt`, the branch) in a delay slot, else 0 ("When a
synchronous exception occurs and the faulting instruction is not in a branch delay slot, then the
value stored in BadInstrP is UNPREDICTABLE", p.181, pin). -/
theorem exceptionEntry_badInstr (s : State) (code ce : W32) :
    (exceptionEntry s code ce).cp0BadInstr = faultingInstr s ∧
      (exceptionEntry s code ce).cp0BadInstrP =
        (if s.pendingBranch.isSome then instrWordAt s (s.pc - 4#32) else 0#32) :=
  ⟨rfl, rfl⟩

/-- Corollary of `exceptionEntry_badInstr`: when the instruction at `pc` was fetched (`readMemWord s
s.pc = some w`, e.g. for every exception the instruction itself raises), `BadInstr` is that word. -/
theorem exceptionEntry_badInstr_fetched (s : State) (code ce w : W32)
    (hfetch : readMemWord s s.pc = some w) :
    (exceptionEntry s code ce).cp0BadInstr = w := by
  show (readMemWord s s.pc).getD 0#32 = w
  rw [hfetch]; rfl

/-- **An interrupt leaves `BadInstr` and `BadInstrP` unchanged** (MD00090 Vol III Rev 6.02 §9.25,
p.179: "The BadInstr register is not set by Interrupts"; §9.26, p.181, the same for BadInstrP). -/
theorem takeInterrupt_badInstr_unchanged (s : State) :
    (takeInterrupt s).cp0BadInstr = s.cp0BadInstr ∧
      (takeInterrupt s).cp0BadInstrP = s.cp0BadInstrP :=
  ⟨rfl, rfl⟩

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
