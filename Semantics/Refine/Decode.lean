import Semantics.Refine.Bridge
import Semantics.Specs.DecodeSpec

/-!
# Refine.Decode — the model's decoder against the manual's format diagrams

* `enc_eq_encode`: for a well-formed instruction the manual's diagram `Manual.enc` is the model's
  `encode` (one theorem, by cases over the constructors).
* `encode_of_decode`: the model's `decode` is strict, so a word it decodes is the canonical
  encoding of the result.
* `decode_enc` / `decoderSound_decode`: **`Manual.DecoderSound decode`** (proved; it was checked
  only by `#guard`s before 7D).
* `decode_of_enc`: completeness: a word that is the diagram of a well-formed instruction decodes
  to it.
-/

namespace Refine

open Manual DecodeSpec

/-! ## Word extensionality by fields (each shape's fields partition the 32 bits) -/

set_option hygiene false in
local macro "ext_by_toNat" : tactic =>
  `(tactic| (simp only [BitVec.toNat_eq, opcodeOf, rsOf, rtOf, rdOf, shamtOf, functOf, immOf,
      targetOf, coOf, code20Of, code10Of, code19Of, off9Of, bit6Of, sa3Of, sa2Of, pcrelOf, imm19Of,
      BitVec.extractLsb, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
      Nat.shiftRight_eq_div_pow] at *; have := BitVec.isLt x; have := BitVec.isLt w; omega))

theorem ext_rt {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : rsOf x = rsOf w)
    (h3 : rtOf x = rtOf w) (h4 : rdOf x = rdOf w) (h5 : shamtOf x = shamtOf w)
    (h6 : functOf x = functOf w) : x = w := by ext_by_toNat

theorem ext_it {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : rsOf x = rsOf w)
    (h3 : rtOf x = rtOf w) (h4 : immOf x = immOf w) : x = w := by ext_by_toNat

theorem ext_jt {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : targetOf x = targetOf w) :
    x = w := by ext_by_toNat

/-- A Release 6 SPECIAL3 word with a 9-bit offset (`LL`, `SC`, `PREF`) by its fields. -/
theorem ext_off9 {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : rsOf x = rsOf w)
    (h3 : rtOf x = rtOf w) (h4 : off9Of x = off9Of w) (h5 : bit6Of x = bit6Of w)
    (h6 : functOf x = functOf w) : x = w := by ext_by_toNat

theorem ext_code20 {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : code20Of x = code20Of w)
    (h3 : functOf x = functOf w) : x = w := by ext_by_toNat

theorem ext_trap {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : rsOf x = rsOf w)
    (h3 : rtOf x = rtOf w) (h4 : code10Of x = code10Of w) (h5 : functOf x = functOf w) : x = w := by
  ext_by_toNat

theorem ext_wait {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : coOf x = coOf w)
    (h3 : code19Of x = code19Of w) (h4 : functOf x = functOf w) : x = w := by ext_by_toNat

-- BEGIN R6-4
/-- A word with a split `sa` field (`LSA`, `ALIGN`) by its fields. -/
theorem ext_rt2 {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : rsOf x = rsOf w)
    (h3 : rtOf x = rtOf w) (h4 : rdOf x = rdOf w) (h5 : sa3Of x = sa3Of w) (h6 : sa2Of x = sa2Of w)
    (h7 : functOf x = functOf w) : x = w := by ext_by_toNat

/-- A PCREL word with a 19-bit immediate (`ADDIUPC`, `LWPC`) by its fields. -/
theorem ext_pc19 {x w : W32} (h1 : opcodeOf x = opcodeOf w) (h2 : rsOf x = rsOf w)
    (h3 : pcrelOf x = pcrelOf w) (h4 : imm19Of x = imm19Of w) : x = w := by ext_by_toNat
-- END R6-4

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
-- BEGIN R6-4
theorem sa3Of_lt' (w : W32) : (sa3Of w).toNat < 8 := sa3Of_lt w
theorem pcrelOf_lt' (w : W32) : (pcrelOf w).toNat < 4 := pcrelOf_lt w
theorem imm19Of_lt' (w : W32) : (imm19Of w).toNat < 524288 := imm19Of_lt w
-- END R6-4

/-! ## The diagrams are the model's encoding -/

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

theorem fld3_sel (sel : W32) (h : sel.toNat < 8) : fld 3 0 sel = field 6 0 sel := by
  have e : sel &&& 7#32 = sel := and_7 sel h
  have e' : sel &&& 63#32 = sel := and_63 sel (by omega)
  simp only [fld, field, maskLow, mask3, mask6, e, e']

-- one simp set serves every constructor; some members are unused in the `mfc0`/`mtc0` arms
set_option linter.unusedSimpArgs false in
/-- **The manual's format diagram of a well-formed instruction is the model's encoding.** -/
theorem enc_eq_encode (i : Instruction) (h : i.WellFormed) : enc i = some (encode i) := by
  cases i
  case mfc0 rt rd sel =>
    have := h.2.2
    simp only [enc, encode, fld3_sel sel this]
    simp only [fld, field, maskLow, mkRT, BitVec.or_assoc, mask1, mask2, mask3, mask4, mask5, mask6, mask10, mask16, mask19, mask20, mask26, BitVec.shiftLeft_zero,
      BitVec.reduceAnd, BitVec.zero_and, BitVec.zero_shiftLeft, BitVec.or_zero, BitVec.zero_or]
  case mtc0 rt rd sel =>
    have := h.2.2
    simp only [enc, encode, fld3_sel sel this]
    simp only [fld, field, maskLow, mkRT, BitVec.or_assoc, mask1, mask2, mask3, mask4, mask5, mask6, mask10, mask16, mask19, mask20, mask26, BitVec.shiftLeft_zero,
      BitVec.reduceAnd, BitVec.zero_and, BitVec.zero_shiftLeft, BitVec.or_zero, BitVec.zero_or]
  case rdhwr rt rd sel =>
    have e3 : sel &&& 7#32 = sel := and_7 sel h.2.2
    have e5 : sel &&& 31#32 = sel := and_31 sel (by have := h.2.2; omega)
    simp only [enc, encode, fld, field, maskLow, mkRT, mask3, mask5, mask6, e3, e5, BitVec.or_assoc,
      BitVec.shiftLeft_zero, BitVec.reduceAnd, BitVec.zero_and, BitVec.zero_shiftLeft, BitVec.or_zero,
      BitVec.zero_or]
  case ei =>
    simp only [enc, encode, fld, field, maskLow, mkRT, BitVec.or_assoc, mask1, mask5, mask6,
      BitVec.shiftLeft_zero, BitVec.reduceAnd, BitVec.zero_and, BitVec.zero_shiftLeft,
      BitVec.or_zero, show (1#32 <<< 5 : W32) = 32#32 by decide]
  case eret => decide
  -- BEGIN R6-2
  case eretnc => decide
  -- END R6-2
  all_goals
    simp only [enc, encode, rFormat, iFormat, trapFormat, codeFormat, off9Format, sa2Format, pc19Format,
      fld, field, maskLow,
      mkRT, mkIT, mkJT, mkOff9, mkCode20, mkTrap, mkWait, mkRT2, mkPc19, BitVec.or_assoc,
      mask1, mask2, mask3, mask4, mask5, mask6, mask9, mask10, mask16, mask19, mask20, mask26, BitVec.shiftLeft_zero, BitVec.reduceAnd, BitVec.zero_and,
      BitVec.zero_shiftLeft, BitVec.or_zero, BitVec.zero_or]

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
  -- BEGIN R6-4
  opcodeOf_or_mkRT2 rsOf_or_mkRT2 rtOf_or_mkRT2 rdOf_or_mkRT2 sa3Of_or_mkRT2 sa2Of_or_mkRT2
  functOf_or_mkRT2 shamtOf_or_mkRT2 opcodeOf_mkRT2 rsOf_mkRT2 rtOf_mkRT2 rdOf_mkRT2 sa3Of_mkRT2
  sa2Of_mkRT2 functOf_mkRT2 opcodeOf_or_mkPc19 rsOf_or_mkPc19 pcrelOf_or_mkPc19 imm19Of_or_mkPc19
  pcrelOf_mkIT sa3Of_or_mkRT and_3 sa2Of_lt sa3Of_lt' pcrelOf_lt' imm19Of_lt imm19Of_lt'
  -- END R6-4

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

set_option maxHeartbeats 1000000 in
/-- **A word `decode` accepts is the encoding of the instruction it returns.** -/
theorem encode_of_decode (w : W32) (i : Instruction) (h : decode w = some i) : encode i = w := by
  have := coOf_lt w; have := bit6Of_lt w
  simp only [decode, decodeFor, decodePrimary, decodeSpecial, decodeRegimm, decodeSpecial3,
    decodeCop0, decodeCop1, decodeCop1S, decodeCop1D, decodeIf] at h
  repeat' split at h
  all_goals (cases h)
  all_goals (try simp only [beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_eq] at *)
  all_goals (rw [← BitVec.toNat_eq]; simp only [encode])
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
