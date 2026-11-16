import Semantics.Refine.DecodeDiagram
import Semantics.Refine.Cycle

/-!
# Refine.DecodeBridge — `Manual.Decode` against the model's `decode` (wave 12b)

* `decode_diagram_sound` / `decode_diagram_complete`: `Manual.Decode w = .instr i` gives a
  diagram of `w`, and every word that is a diagram is decoded to an instruction.
* `decode_agrees`: a word `decode` accepts is decoded to the same instruction by `Manual.Decode`.
* `decode_none_rejected`: a word `decode` rejects but `Manual.Decode` decodes is `Rejected`:
  `MFC0`/`MTC0` of a register CP0 does not contain, `EXT` with `lsb + msbd > 31`, `INS` with
  `lsb > msb`. Their Operation always reaches an oracle choice (`rejected_consults`), which
  `modelOracle` resolves as Reserved Instruction.
* `fetchExecute_diagram`, `instructionTime_diagram`: under the model's choices the instruction time
  with the spec's decoder `Manual.decodeDiagram` is the one with `decode`.
-/

namespace Refine

open Manual DecodeSpec

/-! ## `Manual.Decode` and the diagrams -/

theorem decode_instr_mem {w : W32} {j : Instruction} (h : Decode w = .instr j) :
    j ∈ candidates w ∧ enc j = some w := by
  unfold Decode at h
  split at h
  · rename_i i hi
    cases h
    exact ⟨List.mem_of_find?_eq_some hi, by simpa using List.find?_some hi⟩
  · split at h <;> cases h

/-- **Soundness**: the instruction `Manual.Decode` returns for `w` has the diagram `w`. -/
theorem decode_diagram_sound (w : W32) (i : Instruction) (h : Decode w = .instr i) :
    enc i = some w := (decode_instr_mem h).2

theorem enc_mfc0_sel (rt rd sel : W32) : enc (.mfc0 rt rd sel) = enc (.mfc0 rt rd (sel &&& 7#32)) := by
  simp only [enc, fld, BitVec.and_assoc, mask3, BitVec.and_self]

theorem enc_mtc0_sel (rt rd sel : W32) : enc (.mtc0 rt rd sel) = enc (.mtc0 rt rd (sel &&& 7#32)) := by
  simp only [enc, fld, BitVec.and_assoc, mask3, BitVec.and_self]

theorem enc_rdhwr_sel (rt rd sel : W32) :
    enc (.rdhwr rt rd sel) = enc (.rdhwr rt rd (sel &&& 7#32)) := by
  simp only [enc, fld, BitVec.and_assoc, mask3, BitVec.and_self]

theorem and7_lt (x : W32) : (x &&& 7#32).toNat < 8 := by
  rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- Every diagram word has a candidate with that diagram. -/
theorem exists_candidate (i : Instruction) (w : W32) (h : enc i = some w) :
    ∃ j ∈ candidates w, enc j = some w := by
  have key : ∀ i', enc i' = some w → SelOK i' → ∃ j ∈ candidates w, enc j = some w := by
    intro i' h' hs
    rw [enc_eq_encode_gen i' hs] at h'
    cases Option.some.inj h'
    exact enc_candidate i' hs
  cases i
  case mfc0 rt rd sel => exact key (.mfc0 rt rd (sel &&& 7#32)) (by rw [← enc_mfc0_sel]; exact h) (and7_lt sel)
  case mtc0 rt rd sel => exact key (.mtc0 rt rd (sel &&& 7#32)) (by rw [← enc_mtc0_sel]; exact h) (and7_lt sel)
  case rdhwr rt rd sel =>
    exact key (.rdhwr rt rd (sel &&& 7#32)) (by rw [← enc_rdhwr_sel]; exact h) (and7_lt sel)
  all_goals exact key _ h trivial

/-- **Completeness**: a word that is the diagram of an instruction is decoded to an instruction with
that diagram. -/
theorem decode_diagram_complete (i : Instruction) (w : W32) (h : enc i = some w) :
    ∃ j, Decode w = .instr j ∧ enc j = some w := by
  obtain ⟨j, hj, he⟩ := exists_candidate i w h
  unfold Decode
  cases hf : (candidates w).find? (fun i => enc i == some w) with
  | none =>
    have := List.find?_eq_none.mp hf j hj
    simp [he] at this
  | some k => exact ⟨k, rfl, by simpa using List.find?_some hf⟩

/-! ## The candidates the model rejects -/

/-- **A diagram word the model's `decode` rejects** (fields in range). -/
def Rejected : Instruction → Prop
  | .mfc0 rt rd sel | .mtc0 rt rd sel =>
    rt.toNat < 32 ∧ rd.toNat < 32 ∧ sel.toNat < 8 ∧ isModeledCp0Reg rd sel = false
  | .ext rt rs pos size =>
    rt.toNat < 32 ∧ rs.toNat < 32 ∧ pos.toNat < 32 ∧ 1 ≤ size.toNat ∧ size.toNat ≤ 32 ∧
      32 < pos.toNat + size.toNat
  | .ins rt rs pos size =>
    rt.toNat < 32 ∧ rs.toNat < 32 ∧ pos.toNat < 32 ∧
      ∃ msb : W32, msb.toNat < pos.toNat ∧ size = msb - pos + 1#32
  | _ => False

/-- **The PAUSE word is never decoded as `SLL r0, r0, 5`**: `PAUSE` is the first candidate, and its
diagram is that word (PAUSE p.317). -/
theorem decode_ne_sll_pause (w : W32) : Decode w ≠ .instr (.sll 0#32 0#32 5#32) := by
  intro h
  have he := decode_diagram_sound w _ h
  have hp : enc .pause = some w := by rw [← he]; rfl
  unfold Decode at h
  simp only [candidates, List.find?_cons, hp, beq_self_eq_true] at h
  cases h

theorem rejected_selOK (j : Instruction) (h : Rejected j) : SelOK j := by
  cases j <;> simp only [Rejected] at h <;> first | exact h.2.2.1 | trivial

attribute [local simp] fieldAt_rs fieldAt_rt fieldAt_rd fieldAt_sa fieldAt_imm fieldAt_target
  fieldAt_off9 fieldAt_code20 fieldAt_code10 fieldAt_code19
  rsOf_lt rtOf_lt rdOf_lt shamtOf_lt immOf_lt targetOf_lt off9Of_lt code20Of_lt
  code10Of_lt code19Of_lt fieldAt_sel_lt fieldAt_sel86_lt
  opcodeOf_or_mkRT rsOf_or_mkRT rtOf_or_mkRT rdOf_or_mkRT shamtOf_or_mkRT
  functOf_or_mkRT opcodeOf_mkRT rsOf_mkRT rtOf_mkRT rdOf_mkRT shamtOf_mkRT functOf_mkRT
  coOf_or_mkRT and_31 and_7 and_63

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
/-- **Every candidate is well-formed or `Rejected`**, or it is `SLL r0, r0, 5`, whose word is the
diagram of `PAUSE` (`decode_ne_sll_pause`). -/
theorem candidate_cases (w : W32) : ∀ j ∈ candidates w,
    j.WellFormed ∨ Rejected j ∨ j = .sll 0#32 0#32 5#32 := by
  simp only [candidates, List.forall_mem_cons]
  have hrd := rdOf_lt w; have hsa := shamtOf_lt w; have hrs := rsOf_lt w; have hrt := rtOf_lt w
  have hsel := fieldAt_sel_lt w; have hsel86 := fieldAt_sel86_lt w
  have himm := immOf_lt w; have htg := targetOf_lt w; have hoff := off9Of_lt w
  have hc20 := code20Of_lt w; have hc10 := code10Of_lt w; have hc19 := code19Of_lt w
  repeat' apply And.intro
  all_goals first
    | (left; simp only [Instruction.WellFormed, fieldAt_rs, fieldAt_rt, fieldAt_rd, fieldAt_sa,
        fieldAt_imm, fieldAt_target, fieldAt_off9, fieldAt_code20, fieldAt_code10, fieldAt_code19];
        omega)
    | (left; exact trivial)
    | (intro x hx; cases hx)
    | skip
  -- sll (the PAUSE word is `SLL r0, r0, 5`)
  all_goals first
    | (by_cases hp : fieldAt w 15 11 = 0#32 ∧ fieldAt w 20 16 = 0#32 ∧ fieldAt w 10 6 = 5#32
       · right; right; obtain ⟨h1, h2, h3⟩ := hp; rw [h1, h2, h3]
       · left; exact ⟨hrd, hrt, hsa, hp⟩)
    | skip
  -- mfc0 / mtc0
  all_goals first
    | (cases hm : isModeledCp0Reg (rdOf w) (fieldAt w 2 0)
       · right; left; exact ⟨hrt, hrd, hsel, hm⟩
       · left; exact ⟨hrt, hm⟩)
    | skip
  -- ext
  all_goals first
    | (by_cases hc : (shamtOf w).toNat + ((rdOf w + 1#32).toNat) ≤ 32
       · left; simp only [Instruction.WellFormed, fieldAt_rt, fieldAt_rs, fieldAt_sa, fieldAt_rd]
         refine ⟨hrt, hrs, hsa, ?_, hc⟩
         rw [BitVec.toNat_add]; simp; omega
       · right; left; simp only [Rejected, fieldAt_rt, fieldAt_rs, fieldAt_sa, fieldAt_rd]
         refine ⟨hrt, hrs, hsa, ?_, ?_, by omega⟩ <;> (rw [BitVec.toNat_add]; simp; omega))
    | skip
  -- ins
  all_goals
    have hrd' : (fieldAt w 15 11).toNat < 32 := hrd
    have hsa' : (fieldAt w 10 6).toNat < 32 := hsa
    by_cases hc : (fieldAt w 10 6).toNat ≤ (fieldAt w 15 11).toNat
    · left; simp only [Instruction.WellFormed]
      refine ⟨hrt, hrs, hsa, ?_, ?_⟩ <;> bv_omega
    · right; left; exact ⟨hrt, hrs, hsa, fieldAt w 15 11, by omega, rfl⟩

/-- **The model's `decode` rejects the `Rejected` diagram words.** -/
theorem decode_rejected (j : Instruction) (h : Rejected j) : decode (encode j) = none := by
  cases j <;> simp only [Rejected] at h
  case mfc0 rt rd sel =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    have h5 : sel.toNat < 64 := by omega
    simp [encode, decode, decodeFor, decodePrimary, decodeCop0, decodeIf, h2, h3, h4, h5]
  case mtc0 rt rd sel =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    have h5 : sel.toNat < 64 := by omega
    simp [encode, decode, decodeFor, decodePrimary, decodeCop0, decodeIf, h2, h3, h4, h5]
  case ext rt rs pos size =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    have e1 : (size - 1#32) &&& 31#32 = size - 1#32 := and_31 _ (by bv_omega)
    simp [encode, decode, decodeFor, decodePrimary, decodeSpecial3, decodeIf, h1, h2, h3, e1]
    bv_omega
  case ins rt rs pos size =>
    obtain ⟨h1, h2, h3, msb, h4, rfl⟩ := h
    have e0 : pos + (msb - pos + 1#32) - 1#32 = msb := by bv_omega
    have e1 : msb &&& 31#32 = msb := and_31 _ (by omega)
    simp [encode, decode, decodeFor, decodePrimary, decodeSpecial3, decodeIf, h1, h2, h3, e0, e1]
    omega

/-! ## The bridge -/

/-- **A word the model's `decode` accepts is decoded by `Manual.Decode` to the same instruction.** -/
theorem decode_agrees (w : W32) (i : Instruction) (h : decode w = some i) : Decode w = .instr i := by
  obtain ⟨j, hj, he⟩ := decode_diagram_complete i w (decode_enc w i h)
  have hm := (decode_instr_mem hj).1
  rcases candidate_cases w j hm with hwf | hr | hp
  · rw [decode_of_enc j w hwf he] at h
    cases h; exact hj
  · rw [enc_eq_encode_gen j (rejected_selOK j hr)] at he
    cases Option.some.inj he
    rw [decode_rejected j hr] at h
    cases h
  · subst hp; exact absurd hj (decode_ne_sll_pause w)

/-- **A word the model's `decode` rejects but `Manual.Decode` decodes is `Rejected`.** -/
theorem decode_none_rejected (w : W32) (h : decode w = none) (j : Instruction)
    (hj : Decode w = .instr j) : Rejected j := by
  obtain ⟨hm, he⟩ := decode_instr_mem hj
  rcases candidate_cases w j hm with hwf | hr | hp
  · rw [decode_of_enc j w hwf he] at h; cases h
  · exact hr
  · subst hp; exact absurd hj (decode_ne_sll_pause w)

/-! ## The rejected words reach an oracle choice -/

/-- The model's CP0 register set is the spec's `IsCoprocessorRegisterImplemented` (fields in range). -/
theorem isModeled_iff_nat : ∀ n, n < 32 → ∀ m, m < 8 →
    isModeledCp0Reg (BitVec.ofNat 32 n) (BitVec.ofNat 32 m) = IsCoprocessorRegisterImplemented n m := by
  decide

theorem isModeled_iff (rd sel : W32) (h1 : rd.toNat < 32) (h2 : sel.toNat < 8) :
    isModeledCp0Reg rd sel = IsCoprocessorRegisterImplemented rd.toNat sel.toNat := by
  have := isModeled_iff_nat rd.toNat h1 sel.toNat h2
  simpa using this

/-- **The Operation of a `Rejected` instruction always reaches an oracle choice**
(`Manual.ConsultsOracle`): `cp0Undefined`, `extOutOfRange` or `insLsbAboveMsb`. -/
theorem rejected_consults (j : Instruction) (h : Rejected j) (a : Arch) :
    ConsultsOracle j a = true := by
  cases j <;> simp only [Rejected] at h
  case mfc0 rt rd sel =>
    obtain ⟨-, h2, h3, h4⟩ := h
    simp [ConsultsOracle, ← isModeled_iff rd sel h2 h3, h4]
  case mtc0 rt rd sel =>
    obtain ⟨-, h2, h3, h4⟩ := h
    simp [ConsultsOracle, ← isModeled_iff rd sel h2 h3, h4]
  case ext rt rs pos size =>
    obtain ⟨-, -, h3, h4, h5, h6⟩ := h
    have : (size - 1#32).toNat = size.toNat - 1 := by bv_omega
    simp only [ConsultsOracle, low, decide_eq_true_eq, BitVec.extractLsb'_toNat, this,
      Nat.shiftRight_zero]
    omega
  case ins rt rs pos size =>
    obtain ⟨-, -, h3, msb, h4, rfl⟩ := h
    have e0 : pos + (msb - pos + 1#32) - 1#32 = msb := by bv_omega
    simp only [ConsultsOracle, low, decide_eq_true_eq, BitVec.extractLsb'_toNat, e0,
      Nat.shiftRight_zero]
    omega

/-! ## The instruction time with the spec's decoder -/

/-- The words of `Rejected` instructions are in no coprocessor 2 space. -/
theorem rejected_cop2 (j : Instruction) (h : Rejected j) (w : W32) (he : enc j = some w) :
    InCop2Space w = false := by
  rw [enc_eq_encode_gen j (rejected_selOK j h)] at he
  cases Option.some.inj he
  cases j <;> simp only [Rejected] at h <;>
    simp [InCop2Space, opcode_eq, encode]

/-- The model's resolution of a word `decode` rejects, when no coprocessor 2 space is involved. -/
theorem none_branch (w : W32) (a : Arch) (h2 : InCop2Space w = false) :
    (if UnpredictableEncoding w then some (Unpredictable modelCtx w a)
      else some (GeneralExceptionProcessing modelCtx.impl modelCtx.oracle (Undecodable w a) a)) =
    some (if InCop1Space w && !StatusCU1 a then
        GeneralExceptionProcessing modelImpl modelOracle (.CoprocessorUnusable 1) a
      else if InCop0Space w && !CP0Usable a then
        GeneralExceptionProcessing modelImpl modelOracle (.CoprocessorUnusable 0) a
      else GeneralExceptionProcessing modelImpl modelOracle .ReservedInstruction a) := by
  have hdis := cop01_disjoint w
  simp only [Unpredictable, Undecodable, modelCtx]
  cases UnpredictableEncoding w <;> cases h0 : InCop0Space w <;> cases h1 : InCop1Space w <;>
    cases StatusCU1 a <;> cases CP0Usable a <;> simp_all [modelOracle]

/-- An Execute whose Operation signals at once (not a CTI). -/
theorem execute_of_signal (j : Instruction) (w : W32) (a : Arch) (e : Exception)
    (hcti : IsCTI j = false) (op : Pseudo Unit) (hop : Operation j = some op)
    (hr : op.run modelCtx { arch := a } = (.signal e, { arch := a })) :
    Execute modelCtx w j a =
    some (if InCop1Space w && !StatusCU1 a then
        GeneralExceptionProcessing modelImpl modelOracle (.CoprocessorUnusable 1) a
      else if InCop0Space w && !CP0Usable a then
        GeneralExceptionProcessing modelImpl modelOracle (.CoprocessorUnusable 0) a
      else GeneralExceptionProcessing modelImpl modelOracle e a) := by
  unfold Execute Execute.runOperation
  rw [hcti, hop]
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, hr]
  cases InCop1Space w && !StatusCU1 a <;> cases InCop0Space w && !CP0Usable a <;> rfl

/-- **The Operation of a `Rejected` instruction signals Reserved Instruction at once** under the
model's choices (`cp0Undefined`, `extOutOfRange`, `insLsbAboveMsb`). -/
theorem op_rejected (j : Instruction) (h : Rejected j) (a : Arch) :
    ∃ op, Operation j = some op ∧
      op.run modelCtx { arch := a } = (.signal .ReservedInstruction, { arch := a }) := by
  cases j <;> simp only [Rejected] at h
  case mfc0 rt rd sel =>
    obtain ⟨-, h2, h3, h4⟩ := h
    have hi : IsCoprocessorRegisterImplemented rd.toNat sel.toNat = false := by
      rw [← isModeled_iff rd sel h2 h3, h4]
    refine ⟨_, rfl, ?_⟩
    simp only [Ops.MFC0, Pseudo.run, bind, Pseudo.impl, Pseudo.get, hi, Pseudo.oracle, resolve,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  case mtc0 rt rd sel =>
    obtain ⟨-, h2, h3, h4⟩ := h
    have hi : IsCoprocessorRegisterImplemented rd.toNat sel.toNat = false := by
      rw [← isModeled_iff rd sel h2 h3, h4]
    refine ⟨_, rfl, ?_⟩
    simp only [Ops.MTC0, Pseudo.run, bind, Pseudo.get, hi, Pseudo.oracle, resolve, GPR,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  case ext rt rs pos size =>
    obtain ⟨-, -, h3, h4, h5, h6⟩ := h
    have hc : (low pos 5).toNat + (low (size - 1#32) 5).toNat > 31 := by
      have : (size - 1#32).toNat = size.toNat - 1 := by bv_omega
      simp only [low, BitVec.extractLsb'_toNat, this, Nat.shiftRight_zero]
      omega
    refine ⟨_, rfl, ?_⟩
    simp only [Ops.EXT, Pseudo.run, bind, Pseudo.get, hc, Pseudo.oracle, GPR, unpredictableOr,
      ↓reduceIte]
    rfl
  case ins rt rs pos size =>
    obtain ⟨-, -, h3, msb, h4, rfl⟩ := h
    have e0 : pos + (msb - pos + 1#32) - 1#32 = msb := by bv_omega
    have hc : ((low pos 5).toNat : Int) > ((low (pos + (msb - pos + 1#32) - 1#32) 5).toNat : Int) := by
      simp only [low, BitVec.extractLsb'_toNat, e0, Nat.shiftRight_zero]; omega
    refine ⟨_, rfl, ?_⟩
    simp only [Ops.INS, Pseudo.run, bind, Pseudo.get, hc, Pseudo.oracle, GPR, unpredictableOr,
      ↓reduceIte]
    rfl

theorem rejected_not_cti (j : Instruction) (h : Rejected j) : IsCTI j = false := by
  cases j <;> simp only [Rejected] at h <;> rfl

/-- **The spec's Execute of a `Rejected` instruction under the model's choices**: the coprocessor
checks, then Reserved Instruction. -/
theorem execute_rejected (j : Instruction) (h : Rejected j) (w : W32) (a : Arch) :
    Execute modelCtx w j a =
    some (if InCop1Space w && !StatusCU1 a then
        GeneralExceptionProcessing modelImpl modelOracle (.CoprocessorUnusable 1) a
      else if InCop0Space w && !CP0Usable a then
        GeneralExceptionProcessing modelImpl modelOracle (.CoprocessorUnusable 0) a
      else GeneralExceptionProcessing modelImpl modelOracle .ReservedInstruction a) := by
  obtain ⟨op, h1, h2⟩ := op_rejected j h a
  exact execute_of_signal j w a _ (rejected_not_cti j h) op h1 h2

/-- **Fetch, decode, execute with the spec's decoder is the one with `decode`**, under the model's
choices, from every state. -/
theorem fetchExecute_diagram (a : Arch) :
    FetchExecute modelCtx decodeDiagram a = FetchExecute modelCtx decode a := by
  unfold FetchExecute
  rcases InstructionFetch.run modelCtx { arch := a } with ⟨r, f⟩
  cases r with
  | signal e => rfl
  | ok w =>
    simp only
    cases hd : decode w with
    | some i =>
      have : decodeDiagram w = some i := by simp [decodeDiagram, decode_agrees w i hd]
      rw [this]
    | none =>
      cases hD : Decode w with
      | instr j =>
        have hr := decode_none_rejected w hd j hD
        have : decodeDiagram w = some j := by simp [decodeDiagram, hD]
        rw [this]
        simp only
        rw [execute_rejected j hr w a,
          none_branch w a (rejected_cop2 j hr w (decode_diagram_sound w j hD))]
      | unpredictable =>
        have : decodeDiagram w = none := by simp [decodeDiagram, hD]
        rw [this]
      | reserved =>
        have : decodeDiagram w = none := by simp [decodeDiagram, hD]
        rw [this]

/-- **One instruction time with the spec's decoder is the one with `decode`**, under the model's
choices, from every state. -/
theorem instructionTime_diagram (a : Arch) :
    InstructionTime modelImpl modelOracle decodeDiagram a =
      InstructionTime modelImpl modelOracle decode a := by
  unfold InstructionTime
  simp only
  rw [show ({ impl := modelImpl, oracle := modelOracle } : Ctx) = modelCtx from rfl,
    fetchExecute_diagram]

theorem instructionTimes_diagram (n : Nat) (a : Arch) :
    InstructionTimes modelImpl modelOracle decodeDiagram n a =
      InstructionTimes modelImpl modelOracle decode n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [InstructionTimes, instructionTime_diagram]
    cases InstructionTime modelImpl modelOracle decode a <;> simp [ih]

/-- **The spec's decoder is sound** in the sense of `Manual.DecoderSound`. -/
theorem decoderSound_decodeDiagram : DecoderSound decodeDiagram := by
  intro w i v h hv
  unfold decodeDiagram at h
  split at h
  · cases h; rename_i hD; rw [decode_diagram_sound w _ hD] at hv; exact (Option.some.inj hv).symm
  · cases h

end Refine
