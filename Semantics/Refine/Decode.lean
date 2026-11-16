import Semantics.Refine.Bridge
import Semantics.Specs.DecodeSpec

/-!
# Refine.Decode — the model's decoder against the manual's format diagrams

* `enc_eq_encode_gen`: the manual's diagram `Manual.enc` is the model's `encode` for every
  instruction that meets its diagram's constraint (`SelOK`: the 3-bit `sel` fields, the compact
  branches' `rs`/`rt` relation, the `condn` table); `enc_eq_encode` for well-formed ones.
* `encode_of_decode`: the model's `decode` is strict, so a word it decodes is the canonical
  encoding of the result.
* `decode_enc` / `decoderSound_decode`: **`Manual.DecoderSound decode`**.
* `decode_of_enc`: completeness: a word that is the diagram of a well-formed instruction decodes
  to it.
-/

namespace Refine

open Manual DecodeSpec

/-! ## Word extensionality by fields (each shape's fields partition the 32 bits) -/

/-- Two words agree on bit `i` when they agree on a field `hi..lo` (the model's field extractors
`opcodeOf`, `rsOf`, ... are all of this form) that contains bit `i`. -/
theorem getLsbD_eq_of_field {x w : W32} {hi lo : Nat}
    (h : (x.extractLsb hi lo).zeroExtend 32 = (w.extractLsb hi lo).zeroExtend 32) {i : Nat}
    (h1 : lo ≤ i) (h2 : i ≤ hi) (h3 : hi < 32) : x.getLsbD i = w.getLsbD i := by
  have := congrArg (fun v => v.getLsbD (i - lo)) h
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb] at this
  rw [show lo + (i - lo) = i by omega] at this
  simpa [show i - lo < 32 by omega, show i - lo < hi - lo + 1 by omega] using this

/-- `field_bit [h₁, ..]` closes `x.getLsbD i = w.getLsbD i` for a concrete bit `i` from the first
field equation `hₖ : fieldOf x = fieldOf w` whose field contains `i` (or `i ≥ 32` by `omega`). -/
local syntax "field_bit" " [" ident,* "]" : tactic
macro_rules
  | `(tactic| field_bit []) => `(tactic| omega)
  | `(tactic| field_bit [$h:ident]) =>
    `(tactic| first | (refine getLsbD_eq_of_field $h ?_ ?_ ?_ <;> omega) | omega)
  | `(tactic| field_bit [$h:ident, $hs:ident,*]) =>
    `(tactic| first | (refine getLsbD_eq_of_field $h ?_ ?_ ?_ <;> omega) | field_bit [$hs,*])

/-- `ext_by_fields [h₁, ..]` proves `x = w` from equations of fields that together cover the 32 bits:
bit by bit, each bit from the field that contains it. -/
local macro "ext_by_fields" " [" hs:ident,* "]" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i
  all_goals field_bit [$hs,*]))

theorem ext_rt {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : rsOf x = rsOf w)
    (h3 : rtOf x = rtOf w) (h4 : rdOf x = rdOf w) (h5 : shamtOf x = shamtOf w)
    (h6 : functOf x = functOf w) : x = w := by ext_by_fields [h1, h2, h3, h4, h5, h6]

theorem ext_it {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : rsOf x = rsOf w)
    (h3 : rtOf x = rtOf w) (h4 : immOf x = immOf w) : x = w := by ext_by_fields [h1, h2, h3, h4]

theorem ext_jt {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : targetOf x = targetOf w) :
    x = w := by ext_by_fields [h1, h2]

/-- A Release 6 SPECIAL3 word with a 9-bit offset (`LL`, `SC`, `PREF`) by its fields. -/
theorem ext_off9 {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : rsOf x = rsOf w)
    (h3 : rtOf x = rtOf w) (h4 : off9Of x = off9Of w) (h5 : bit6Of x = bit6Of w)
    (h6 : functOf x = functOf w) : x = w := by ext_by_fields [h1, h2, h3, h4, h5, h6]

theorem ext_code20 {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : code20Of x = code20Of w)
    (h3 : functOf x = functOf w) : x = w := by ext_by_fields [h1, h2, h3]

theorem ext_trap {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : rsOf x = rsOf w)
    (h3 : rtOf x = rtOf w) (h4 : code10Of x = code10Of w) (h5 : functOf x = functOf w) : x = w := by
  ext_by_fields [h1, h2, h3, h4, h5]

theorem ext_wait {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : coOf x = coOf w)
    (h3 : code19Of x = code19Of w) (h4 : functOf x = functOf w) : x = w := by
  ext_by_fields [h1, h2, h3, h4]

/-- A word with a split `sa` field (`LSA`, `ALIGN`) by its fields. -/
theorem ext_rt2 {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : rsOf x = rsOf w)
    (h3 : rtOf x = rtOf w) (h4 : rdOf x = rdOf w) (h5 : sa3Of x = sa3Of w) (h6 : sa2Of x = sa2Of w)
    (h7 : functOf x = functOf w) : x = w := by ext_by_fields [h1, h2, h3, h4, h5, h6, h7]

/-- A PCREL word with a 19-bit immediate (`ADDIUPC`, `LWPC`) by its fields. -/
theorem ext_pc19 {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : rsOf x = rsOf w)
    (h3 : pcrelOf x = pcrelOf w) (h4 : imm19Of x = imm19Of w) : x = w := by ext_by_fields [h1, h2, h3, h4]

/-! ## Ranges of the narrow fields -/

theorem coOf_lt (w : W32) : (coOf w).toNat < 2 := by simp [coOf, BitVec.extractLsb]; omega
theorem bit6Of_lt (w : W32) : (bit6Of w).toNat < 2 := by simp [bit6Of, BitVec.extractLsb]; omega
theorem off9Of_lt' (w : W32) : (off9Of w).toNat < 512 := off9Of_lt w
theorem immOf_lt' (w : W32) : (immOf w).toNat < 65536 := immOf_lt w
theorem targetOf_lt' (w : W32) : (targetOf w).toNat < 67108864 := targetOf_lt w
theorem code20Of_lt' (w : W32) : (code20Of w).toNat < 1048576 := code20Of_lt w
theorem code10Of_lt' (w : W32) : (code10Of w).toNat < 1024 := code10Of_lt w
theorem code19Of_lt' (w : W32) : (code19Of w).toNat < 524288 := code19Of_lt w
theorem opcodeOf_lt (w : W32) : (opcodeOf w).toNat < 64 := by
  simp [opcodeOf, BitVec.extractLsb]; omega
theorem sa3Of_lt' (w : W32) : (sa3Of w).toNat < 8 := sa3Of_lt w
theorem pcrelOf_lt' (w : W32) : (pcrelOf w).toNat < 4 := pcrelOf_lt w
theorem imm19Of_lt' (w : W32) : (imm19Of w).toNat < 524288 := imm19Of_lt w

/-! ## The diagrams are the model's encoding -/

/-- A diagram whose constraint holds is its word. -/
theorem encIf_true {c : Bool} {w : W32} (h : c = true) : Manual.encIf c w = some w := by
  simp [Manual.encIf, h]

/-- A constrained diagram that gives a word: its constraint holds and the word is its own. -/
theorem encIf_some {c : Bool} {w v : W32} (h : Manual.encIf c w = some v) : c = true ∧ w = v := by
  unfold encIf at h; split at h
  · exact ⟨‹_›, Option.some.inj h⟩
  · cases h

/-- A register field as a number (`Manual.reg`). -/
theorem reg_val (x : W32) : (Manual.reg x).val = x.toNat % 32 := rfl

/-- The constraint of a compact branch's diagram, from `WellFormed` (field arithmetic). -/
macro "cb_cond" : tactic => `(tactic| (
  simp only [Instruction.WellFormed, ne_eq, ← BitVec.toNat_inj] at *
  simp only [bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq]
  simp only [Fin.ext_iff, reg_val, Fin.val_zero]
  omega))

theorem mask1 : (1#32 <<< 1) - 1#32 = 1#32 := by decide
theorem mask2 : (1#32 <<< 2) - 1#32 = 3#32 := by decide
theorem mask3 : (1#32 <<< 3) - 1#32 = 7#32 := by decide
theorem mask4 : (1#32 <<< 4) - 1#32 = 15#32 := by decide
theorem mask5 : (1#32 <<< 5) - 1#32 = 31#32 := by decide
theorem mask6 : (1#32 <<< 6) - 1#32 = 63#32 := by decide
theorem mask9 : (1#32 <<< 9) - 1#32 = 511#32 := by decide
theorem mask10 : (1#32 <<< 10) - 1#32 = 1023#32 := by decide
theorem mask16 : (1#32 <<< 16) - 1#32 = 65535#32 := by decide
theorem mask19 : (1#32 <<< 19) - 1#32 = 524287#32 := by decide
theorem mask20 : (1#32 <<< 20) - 1#32 = 1048575#32 := by decide
theorem mask26 : (1#32 <<< 26) - 1#32 = 67108863#32 := by decide
theorem mask21 : (1#32 <<< 21) - 1#32 = 2097151#32 := by decide

/-- The model's `condn` table of CMP.condn.fmt is the diagram's (Table A.17, p.457). -/
theorem cmpCondnOK_eq (c : W32) : cmpCondnOK c = Manual.CmpCondnOK c := rfl

theorem fld3_sel (sel : W32) (h : sel.toNat < 8) : fld 3 0 sel = field 6 0 sel := by
  have e : sel &&& 7#32 = sel := and_7 sel h
  have e' : sel &&& 63#32 = sel := and_63 sel (by omega)
  simp only [fld, field, maskLow, mask3, mask6, e, e']

/-! ## `enc` is `encode` (every instruction whose diagram constraint holds: `SelOK`) -/

/-- The `sel` field of `MFC0`/`MTC0`/`RDHWR` fits its 3 bits (`enc` writes 3 bits, `encode` 6 or 5). -/
def SelOK : Instruction → Prop
  | .mfc0 _ _ sel | .mtc0 _ _ sel | .rdhwr _ _ sel => sel.toNat < 8
  -- the compact branches: the constraint of the diagram (`Manual.encIf`) holds
  | .beqc rs rt _ | .bnec rs rt _ => (reg rs != 0 && decide ((reg rs).val < (reg rt).val)) = true
  | .bltc rs rt _ | .bgec rs rt _ | .bltuc rs rt _ | .bgeuc rs rt _ =>
    (reg rs != 0 && reg rt != 0 && reg rs != reg rt) = true
  | .blezc rt _ | .bgezc rt _ | .bgtzc rt _ | .bltzc rt _ | .blezalc rt _ | .bgezalc rt _
  | .bgtzalc rt _ | .bltzalc rt _ | .beqzalc rt _ | .bnezalc rt _ => (reg rt != 0) = true
  | .beqzc rs _ | .bnezc rs _ => (reg rs != 0) = true
  | .bovc rs rt _ | .bnvc rs rt _ => decide ((reg rt).val ≤ (reg rs).val) = true
  | .cmpS cond _ _ _ | .cmpD cond _ _ _ => CmpCondnOK cond = true
  | _ => True

-- one simp set serves every constructor; some members are unused in the `mfc0`/`mtc0` arms
set_option linter.unusedSimpArgs false in
/-- `enc_eq_encode` without the field ranges: the diagram masks each field to its width as `encode`
does. -/
theorem enc_eq_encode_gen (i : Instruction) (h : SelOK i) : enc i = some (encode i) := by
  cases i
  case mfc0 rt rd sel =>
    simp only [enc, encode, fld3_sel sel h]
    simp only [fld, field, maskLow, mkRT, BitVec.or_assoc, mask1, mask2, mask3, mask4, mask5, mask6, mask10, mask16, mask19, mask20, mask26, BitVec.shiftLeft_zero,
      BitVec.reduceAnd, BitVec.zero_and, BitVec.zero_shiftLeft, BitVec.or_zero, BitVec.zero_or]
  case mtc0 rt rd sel =>
    simp only [enc, encode, fld3_sel sel h]
    simp only [fld, field, maskLow, mkRT, BitVec.or_assoc, mask1, mask2, mask3, mask4, mask5, mask6, mask10, mask16, mask19, mask20, mask26, BitVec.shiftLeft_zero,
      BitVec.reduceAnd, BitVec.zero_and, BitVec.zero_shiftLeft, BitVec.or_zero, BitVec.zero_or]
  case rdhwr rt rd sel =>
    have e3 : sel &&& 7#32 = sel := and_7 sel h
    have e5 : sel &&& 31#32 = sel := and_31 sel (by have : sel.toNat < 8 := h; omega)
    simp only [enc, encode, fld, field, maskLow, mkRT, mask3, mask5, mask6, e3, e5, BitVec.or_assoc,
      BitVec.shiftLeft_zero, BitVec.reduceAnd, BitVec.zero_and, BitVec.zero_shiftLeft, BitVec.or_zero,
      BitVec.zero_or]
  case ei =>
    simp only [enc, encode, fld, field, maskLow, mkRT, BitVec.or_assoc, mask1, mask5, mask6,
      BitVec.shiftLeft_zero, BitVec.reduceAnd, BitVec.zero_and, BitVec.zero_shiftLeft,
      BitVec.or_zero, show (1#32 <<< 5 : W32) = 32#32 by decide]
  case eret => decide
  case eretnc => decide
  case dvp | evp =>
    simp only [enc, encode, fld, field, maskLow, mkRT, BitVec.or_assoc, mask1, mask3, mask5, mask6,
      BitVec.shiftLeft_zero, BitVec.reduceAnd, BitVec.zero_and, BitVec.zero_shiftLeft,
      BitVec.or_zero, BitVec.zero_or, BitVec.reduceOr, show (1#32 <<< 5 : W32) = 32#32 by decide]
  all_goals
    simp only [enc, encode, cop1R, rFormat, iFormat, trapFormat, codeFormat, off9Format, sa2Format,
      pc19Format, fld, field, maskLow,
      mkRT, mkIT, mkJT, mkOff9, mkCode20, mkTrap, mkWait, mkRT2, mkPc19, BitVec.or_assoc,
      mask1, mask2, mask3, mask4, mask5, mask6, mask9, mask10, mask16, mask19, mask20, mask26, BitVec.shiftLeft_zero, BitVec.reduceAnd, BitVec.zero_and,
      BitVec.zero_shiftLeft, BitVec.or_zero, BitVec.zero_or]
  -- the compact branches: `h` is the diagram's constraint; BEQZC/BNEZC's 21-bit field
  all_goals
    rw [encIf_true h]
    try simp only [mkOff21, fld, field, maskLow, mask5, mask6, mask21, BitVec.or_assoc,
      BitVec.shiftLeft_zero, BitVec.reduceAnd]

/-- A well-formed instruction meets its diagram's constraint. -/
theorem selOK_of_wellFormed (i : Instruction) (h : i.WellFormed) : SelOK i := by
  cases i <;> first
    | trivial
    | exact h.2.2
    | exact (cmpCondnOK_eq _).symm.trans h.1
    | (unfold SelOK; cb_cond)

/-- **The manual's format diagram of a well-formed instruction is the model's encoding.** -/
theorem enc_eq_encode (i : Instruction) (h : i.WellFormed) : enc i = some (encode i) :=
  enc_eq_encode_gen i (selOK_of_wellFormed i h)

/-! ## `decode` is strict: a decoded word is the canonical encoding -/

theorem ext_msbd (a : W32) : a + 1#32 - 1#32 = a := by bv_omega
theorem ins_msb (a b : W32) : a + (b - a + 1#32) - 1#32 = b := by bv_omega

attribute [local simp] ext_msbd ins_msb opcodeOf_or_mkRT rsOf_or_mkRT rtOf_or_mkRT rdOf_or_mkRT shamtOf_or_mkRT
  functOf_or_mkRT opcodeOf_mkRT rsOf_mkRT rtOf_mkRT rdOf_mkRT shamtOf_mkRT functOf_mkRT
  opcodeOf_mkIT rsOf_mkIT rtOf_mkIT immOf_mkIT opcodeOf_or_mkJT targetOf_or_mkJT
  coOf_or_mkRT
  opcodeOf_or_mkOff9 rsOf_or_mkOff9 rtOf_or_mkOff9 off9Of_or_mkOff9 bit6Of_or_mkOff9 functOf_or_mkOff9
  opcodeOf_mkCode20 functOf_mkCode20 code20Of_mkCode20
  opcodeOf_mkTrap functOf_mkTrap rsOf_mkTrap rtOf_mkTrap code10Of_mkTrap
  opcodeOf_mkWait coOf_mkWait functOf_mkWait code19Of_mkWait
  and_31 and_65535 and_67108863 and_1 and_7 and_15 and_63 and_511 and_1023 and_524287 and_1048575
  rsOf_lt rtOf_lt rdOf_lt shamtOf_lt immOf_lt targetOf_lt functOf_lt off9Of_lt
  code20Of_lt code10Of_lt code19Of_lt immOf_lt' targetOf_lt' code20Of_lt' code10Of_lt'
  code19Of_lt' coOf_lt bit6Of_lt off9Of_lt' opcodeOf_lt
  opcodeOf_or_mkRT2 rsOf_or_mkRT2 rtOf_or_mkRT2 rdOf_or_mkRT2 sa3Of_or_mkRT2 sa2Of_or_mkRT2
  functOf_or_mkRT2 shamtOf_or_mkRT2 opcodeOf_mkRT2 rsOf_mkRT2 rtOf_mkRT2 rdOf_mkRT2 sa3Of_mkRT2
  sa2Of_mkRT2 functOf_mkRT2 opcodeOf_or_mkPc19 rsOf_or_mkPc19 pcrelOf_or_mkPc19 imm19Of_or_mkPc19
  pcrelOf_mkIT sa3Of_or_mkRT and_3 sa2Of_lt sa3Of_lt' pcrelOf_lt' imm19Of_lt imm19Of_lt'

/-- One field of a decoded word: the field lemmas, then arithmetic on the guards. -/
local macro "field_goal" : tactic =>
  `(tactic| first
    | (simp; done)
    | ((try simp); simp only [BitVec.toNat_eq]; bv_omega))

local macro "word_goal" : tactic =>
  `(tactic| first
    | (apply ext_rt <;> field_goal)
    | (apply ext_it <;> field_goal)
    | (apply ext_jt <;> field_goal)
    | (apply ext_code20 <;> field_goal)
    | (apply ext_trap <;> field_goal)
    | (apply ext_wait <;> field_goal)
    | (apply ext_off9 <;> field_goal)
    | (apply ext_rt2 <;> field_goal)    -- R6-4
    | (apply ext_pc19 <;> field_goal))  -- R6-4

/-! ### The compact branches: the three shapes of a shared opcode (`decodeZeroEqTwo`,
`decodeLtGe`, `decodeJumpOrZ`) re-encode to the word they decoded -/

theorem ext_off21 {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : rsOf x = rsOf w)
    (h3 : off21Of x = off21Of w) : x = w := by ext_by_fields [h1, h2, h3]

theorem off21Of_lt' (w : W32) : (off21Of w).toNat < 2097152 := off21Of_lt w

/-- An I-format word with the opcode, `rs`, `rt` and offset of `w` is `w`. -/
theorem mkIT_fields (op rs rt : W32) (w : W32) (hop : opcodeOf w = op) (hrs : rsOf w = rs)
    (hrt : rtOf w = rt) : mkIT op rs rt (immOf w) = w := by
  subst hop hrs hrt
  apply ext_it <;> simp

/-- The opcode of a decoded word, from the `match` of `decodePrimary`. -/
theorem opcodeOf_of_toNat (w : W32) (n : Nat) (h : (opcodeOf w).toNat = n) :
    opcodeOf w = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; rw [h]; have := opcodeOf_lt w; simp; omega

theorem encode_zeroEqTwo (zero eq : W32 → W32 → Instruction) (two : W32 → W32 → W32 → Instruction)
    (n : Nat) (w : W32) (hop : (opcodeOf w).toNat = n)
    (hz : ∀ rt imm, encode (zero rt imm) = mkIT (BitVec.ofNat 32 n) 0#32 rt imm)
    (he : ∀ rt imm, encode (eq rt imm) = mkIT (BitVec.ofNat 32 n) rt rt imm)
    (ht : ∀ rs rt imm, encode (two rs rt imm) = mkIT (BitVec.ofNat 32 n) rs rt imm) :
    encode (decodeZeroEqTwo zero eq two w) = w := by
  have hop' := opcodeOf_of_toNat w n hop
  unfold decodeZeroEqTwo
  simp only [beq_iff_eq]
  split
  · rename_i h0; rw [hz]; exact mkIT_fields _ _ _ w hop' h0 rfl
  · split
    · rename_i _ h0; rw [he]; exact mkIT_fields _ _ _ w hop' h0 rfl
    · rw [ht]; exact mkIT_fields _ _ _ w hop' rfl rfl

theorem encode_ltGe (zero : W32 → W32 → Instruction) (two ovf : W32 → W32 → W32 → Instruction)
    (n : Nat) (w : W32) (hop : (opcodeOf w).toNat = n)
    (hz : ∀ rt imm, encode (zero rt imm) = mkIT (BitVec.ofNat 32 n) 0#32 rt imm)
    (ht : ∀ rs rt imm, encode (two rs rt imm) = mkIT (BitVec.ofNat 32 n) rs rt imm)
    (ho : ∀ rs rt imm, encode (ovf rs rt imm) = mkIT (BitVec.ofNat 32 n) rs rt imm) :
    encode (decodeLtGe zero two ovf w) = w := by
  have hop' := opcodeOf_of_toNat w n hop
  unfold decodeLtGe
  simp only [beq_iff_eq]
  split
  · split
    · rename_i _ h0; rw [hz]; exact mkIT_fields _ _ _ w hop' h0 rfl
    · rw [ht]; exact mkIT_fields _ _ _ w hop' rfl rfl
  · rw [ho]; exact mkIT_fields _ _ _ w hop' rfl rfl

theorem encode_jumpOrZ (jmp z : W32 → W32 → Instruction) (n : Nat) (w : W32)
    (hop : (opcodeOf w).toNat = n)
    (hj : ∀ rt imm, encode (jmp rt imm) = mkIT (BitVec.ofNat 32 n) 0#32 rt imm)
    (hz : ∀ rs off, encode (z rs off) = mkOff21 (BitVec.ofNat 32 n) rs off) :
    encode (decodeJumpOrZ jmp z w) = w := by
  have hop' := opcodeOf_of_toNat w n hop
  unfold decodeJumpOrZ
  simp only [beq_iff_eq]
  split
  · rename_i h0; rw [hj]; exact mkIT_fields _ _ _ w hop' h0 rfl
  · rw [hz]
    apply ext_off21
    · rw [opcodeOf_mkOff21, hop', and_63 _ (by have := opcodeOf_lt w; rw [← hop']; exact this)]
    · simp [rsOf_mkOff21]
    · simp [off21Of_mkOff21, and_2097151 _ (off21Of_lt w)]

/-- Close `encode (<shape> ... w) = w` for a compact-branch opcode. -/
local macro "compact_word" : tactic => `(tactic| (
  first
    | with_reducible refine encode_zeroEqTwo _ _ _ _ _ ‹_› ?_ ?_ ?_
    | with_reducible refine encode_ltGe _ _ _ _ _ ‹_› ?_ ?_ ?_
    | with_reducible refine encode_jumpOrZ _ _ _ _ ‹_› ?_ ?_
  all_goals intros
  all_goals rfl))

set_option maxHeartbeats 1000000 in
/-- **A word `decode` accepts is the encoding of the instruction it returns.** -/
theorem encode_of_decode (w : W32) (i : Instruction) (h : decode w = some i) : encode i = w := by
  have := coOf_lt w; have := bit6Of_lt w
  simp only [decode, decodeFor, decodePrimary, decodeSpecial, decodeRegimm, decodeSpecial3,
    decodeCop0, decodeCop1, decodeCop1Fmt, decodeFmtS, decodeFmtD, Option.bind_some, Option.bind_none,
    decodeIf] at h
  repeat' split at h
  all_goals (cases h)
  all_goals (try compact_word)
  all_goals (try simp only [beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_eq] at *)
  all_goals (rw [← BitVec.toNat_eq]; simp only [encode, cop1R])
  all_goals word_goal

/-! ## The decoder against the diagrams -/

/-- **Decoder soundness**: an instruction `decode` returns for `w` has the diagram `w`. -/
theorem decode_enc (w : W32) (i : Instruction) (h : decode w = some i) : enc i = some w := by
  rw [enc_eq_encode i (decode_wellFormed w i h), encode_of_decode w i h]

/-- **`Manual.DecoderSound decode`** (was checked by `#guard`s only, `Tests/ManualTests.lean`). -/
theorem decoderSound_decode : Manual.DecoderSound decode := fun w i v h hv => by
  rw [decode_enc w i h] at hv
  exact (Option.some.inj hv).symm

/-- **Decoder completeness**: the diagram of a well-formed instruction decodes to it. -/
theorem decode_of_enc (i : Instruction) (w : W32) (h : i.WellFormed) (hw : enc i = some w) :
    decode w = some i := by
  rw [enc_eq_encode i h] at hw
  rw [← Option.some.inj hw]
  exact decode_encode i h

end Refine
