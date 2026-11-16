import Semantics.Word
import Semantics.Types
import Semantics.Instruction
import Semantics.Specs.WellFormed

/-!
# DecodeSpec — `decode`/`encode` round trip

`decode (encode i) = some i` for every well-formed `Instruction`
(`Instruction.WellFormed`: each raw field fits its bit width), and conversely
every instruction produced by `decode` is well-formed.

Proof outline: unconditional field-extraction lemmas for each encoding shape
(`mkRT`, `(op <<< 26) ||| mkRT`, `mkIT`, `(op <<< 26) ||| mkJT`), proved
bitwise; "mask is identity on an in-range field" lemmas; then one `simp` per
constructor.
-/

namespace DecodeSpec

/-! ## Mask bits -/

private theorem getLsbD_lowMask (k : Nat) (hk : k ≤ 32) (i : Nat) :
    (BitVec.ofNat 32 (2 ^ k - 1)).getLsbD i = decide (i < k) := by
  rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]; simp; omega

private theorem m5 (i : Nat) : (31#32).getLsbD i = decide (i < 5) :=
  getLsbD_lowMask 5 (by omega) i
private theorem m6 (i : Nat) : (63#32).getLsbD i = decide (i < 6) :=
  getLsbD_lowMask 6 (by omega) i
private theorem m16 (i : Nat) : (65535#32).getLsbD i = decide (i < 16) :=
  getLsbD_lowMask 16 (by omega) i
private theorem m26 (i : Nat) : (67108863#32).getLsbD i = decide (i < 26) :=
  getLsbD_lowMask 26 (by omega) i
private theorem m1 (i : Nat) : (1#32).getLsbD i = decide (i < 1) :=
  getLsbD_lowMask 1 (by omega) i
private theorem m2 (i : Nat) : (3#32).getLsbD i = decide (i < 2) :=
  getLsbD_lowMask 2 (by omega) i
private theorem m3 (i : Nat) : (7#32).getLsbD i = decide (i < 3) :=
  getLsbD_lowMask 3 (by omega) i
private theorem m4 (i : Nat) : (15#32).getLsbD i = decide (i < 4) :=
  getLsbD_lowMask 4 (by omega) i
private theorem m10 (i : Nat) : (1023#32).getLsbD i = decide (i < 10) :=
  getLsbD_lowMask 10 (by omega) i
private theorem m19 (i : Nat) : (524287#32).getLsbD i = decide (i < 19) :=
  getLsbD_lowMask 19 (by omega) i
private theorem m20 (i : Nat) : (1048575#32).getLsbD i = decide (i < 20) :=
  getLsbD_lowMask 20 (by omega) i
private theorem m9 (i : Nat) : (511#32).getLsbD i = decide (i < 9) :=
  getLsbD_lowMask 9 (by omega) i

/-- Closes a field-extraction goal bit by bit. -/
local macro "field_ext" : tactic =>
  `(tactic| (apply BitVec.eq_of_getLsbD_eq; intro i hi
             simp [opcodeOf, rsOf, rtOf, rdOf, shamtOf, functOf, immOf, targetOf,
               coOf, code20Of, code10Of, code19Of, off9Of, bit6Of,
               mkRT, mkIT, mkJT, mkCode20, mkTrap, mkWait, mkOff9,
               field, maskLow, m5, m6, m16, m26, m1, m2, m3, m4, m9, m10, m19, m20]
             try grind))

/-! ## Field extraction: `x ||| mkRT ..` (SPECIAL2/SPECIAL3/COP0/COP1, where `x` is the
opcode already shifted into place; stated for arbitrary `x`) -/

theorem opcodeOf_or_mkRT (x a b c d e : W32) :
    opcodeOf (x ||| mkRT a b c d e) = x >>> 26 := by field_ext
theorem rsOf_or_mkRT (x a b c d e : W32) :
    rsOf (x ||| mkRT a b c d e) = ((x >>> 21) &&& 31#32) ||| (a &&& 31#32) := by field_ext
theorem rtOf_or_mkRT (x a b c d e : W32) :
    rtOf (x ||| mkRT a b c d e) = ((x >>> 16) &&& 31#32) ||| (b &&& 31#32) := by field_ext
theorem rdOf_or_mkRT (x a b c d e : W32) :
    rdOf (x ||| mkRT a b c d e) = ((x >>> 11) &&& 31#32) ||| (c &&& 31#32) := by field_ext
theorem shamtOf_or_mkRT (x a b c d e : W32) :
    shamtOf (x ||| mkRT a b c d e) = ((x >>> 6) &&& 31#32) ||| (d &&& 31#32) := by field_ext
theorem functOf_or_mkRT (x a b c d e : W32) :
    functOf (x ||| mkRT a b c d e) = (x &&& 63#32) ||| (e &&& 63#32) := by field_ext

theorem coOf_or_mkRT (x a b c d e : W32) :
    coOf (x ||| mkRT a b c d e) = ((x >>> 25) &&& 1#32) ||| ((a >>> 4) &&& 1#32) := by field_ext

/-! ## Field extraction: `x ||| mkOff9 ..` (Release 6 `LL`/`SC`/`PREF`) -/

theorem opcodeOf_or_mkOff9 (x a b c e : W32) : opcodeOf (x ||| mkOff9 a b c e) = x >>> 26 := by
  field_ext
theorem rsOf_or_mkOff9 (x a b c e : W32) :
    rsOf (x ||| mkOff9 a b c e) = ((x >>> 21) &&& 31#32) ||| (a &&& 31#32) := by field_ext
theorem rtOf_or_mkOff9 (x a b c e : W32) :
    rtOf (x ||| mkOff9 a b c e) = ((x >>> 16) &&& 31#32) ||| (b &&& 31#32) := by field_ext
theorem off9Of_or_mkOff9 (x a b c e : W32) :
    off9Of (x ||| mkOff9 a b c e) = ((x >>> 7) &&& 511#32) ||| (c &&& 511#32) := by field_ext
theorem bit6Of_or_mkOff9 (x a b c e : W32) :
    bit6Of (x ||| mkOff9 a b c e) = (x >>> 6) &&& 1#32 := by field_ext
theorem functOf_or_mkOff9 (x a b c e : W32) :
    functOf (x ||| mkOff9 a b c e) = (x &&& 63#32) ||| (e &&& 63#32) := by field_ext

/-! ## Field extraction: `mkCode20 ..`, `mkTrap ..`, `mkWait ..` -/

theorem opcodeOf_mkCode20 (c e : W32) : opcodeOf (mkCode20 c e) = 0#32 := by field_ext
theorem functOf_mkCode20 (c e : W32) : functOf (mkCode20 c e) = e &&& 63#32 := by field_ext
theorem code20Of_mkCode20 (c e : W32) : code20Of (mkCode20 c e) = c &&& 1048575#32 := by
  field_ext
theorem opcodeOf_mkTrap (a b c e : W32) : opcodeOf (mkTrap a b c e) = 0#32 := by field_ext
theorem functOf_mkTrap (a b c e : W32) : functOf (mkTrap a b c e) = e &&& 63#32 := by field_ext
theorem rsOf_mkTrap (a b c e : W32) : rsOf (mkTrap a b c e) = a &&& 31#32 := by field_ext
theorem rtOf_mkTrap (a b c e : W32) : rtOf (mkTrap a b c e) = b &&& 31#32 := by field_ext
theorem code10Of_mkTrap (a b c e : W32) : code10Of (mkTrap a b c e) = c &&& 1023#32 := by
  field_ext
theorem opcodeOf_mkWait (o k c e : W32) : opcodeOf (mkWait o k c e) = o &&& 63#32 := by field_ext
theorem coOf_mkWait (o k c e : W32) : coOf (mkWait o k c e) = k &&& 1#32 := by field_ext
theorem functOf_mkWait (o k c e : W32) : functOf (mkWait o k c e) = e &&& 63#32 := by field_ext
theorem code19Of_mkWait (o k c e : W32) : code19Of (mkWait o k c e) = c &&& 524287#32 := by
  field_ext

/-! ## Field extraction: plain `mkRT ..` (SPECIAL, opcode 0) -/

theorem opcodeOf_mkRT (a b c d e : W32) : opcodeOf (mkRT a b c d e) = 0#32 := by field_ext
theorem rsOf_mkRT (a b c d e : W32) : rsOf (mkRT a b c d e) = a &&& 31#32 := by field_ext
theorem rtOf_mkRT (a b c d e : W32) : rtOf (mkRT a b c d e) = b &&& 31#32 := by field_ext
theorem rdOf_mkRT (a b c d e : W32) : rdOf (mkRT a b c d e) = c &&& 31#32 := by field_ext
theorem shamtOf_mkRT (a b c d e : W32) : shamtOf (mkRT a b c d e) = d &&& 31#32 := by field_ext
theorem functOf_mkRT (a b c d e : W32) : functOf (mkRT a b c d e) = e &&& 63#32 := by field_ext

/-! ## Field extraction: `mkIT ..` -/

theorem opcodeOf_mkIT (op a b imm : W32) : opcodeOf (mkIT op a b imm) = op &&& 63#32 := by
  field_ext
theorem rsOf_mkIT (op a b imm : W32) : rsOf (mkIT op a b imm) = a &&& 31#32 := by field_ext
theorem rtOf_mkIT (op a b imm : W32) : rtOf (mkIT op a b imm) = b &&& 31#32 := by field_ext
theorem immOf_mkIT (op a b imm : W32) : immOf (mkIT op a b imm) = imm &&& 65535#32 := by
  field_ext

/-! ## Field extraction: `x ||| mkJT ..` -/

theorem opcodeOf_or_mkJT (x t : W32) : opcodeOf (x ||| mkJT t) = x >>> 26 := by field_ext
theorem targetOf_or_mkJT (x t : W32) :
    targetOf (x ||| mkJT t) = (x &&& 67108863#32) ||| (t &&& 67108863#32) := by field_ext

-- BEGIN R6-3
/-! ## Field extraction: `mkOff21 ..` (BEQZC/BNEZC) -/

private theorem m21 (i : Nat) : (2097151#32).getLsbD i = decide (i < 21) :=
  getLsbD_lowMask 21 (by omega) i

local macro "field_ext21" : tactic =>
  `(tactic| (apply BitVec.eq_of_getLsbD_eq; intro i hi
             simp [opcodeOf, rsOf, rtOf, off21Of, mkOff21, field, maskLow, m5, m6, m21]
             try grind))

theorem opcodeOf_mkOff21 (op a off : W32) : opcodeOf (mkOff21 op a off) = op &&& 63#32 := by
  field_ext21
theorem rsOf_mkOff21 (op a off : W32) : rsOf (mkOff21 op a off) = a &&& 31#32 := by field_ext21
theorem off21Of_mkOff21 (op a off : W32) : off21Of (mkOff21 op a off) = off &&& 2097151#32 := by
  field_ext21
-- END R6-3

/-! ## Masks are the identity on in-range fields -/

private theorem and_lowMask (k : Nat) (hk : k ≤ 32) (a : W32) (h : a.toNat < 2 ^ k) :
    a &&& BitVec.ofNat 32 (2 ^ k - 1) = a := by
  apply BitVec.eq_of_toNat_eq
  have : 2 ^ k ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hk
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

theorem and_31 (a : W32) (h : a.toNat < 32) : a &&& 31#32 = a := and_lowMask 5 (by decide) a h
theorem and_65535 (a : W32) (h : a.toNat < 2 ^ 16) : a &&& 65535#32 = a := and_lowMask 16 (by decide) a h
theorem and_67108863 (a : W32) (h : a.toNat < 2 ^ 26) : a &&& 67108863#32 = a :=
  and_lowMask 26 (by decide) a h

theorem and_1 (a : W32) (h : a.toNat < 2) : a &&& 1#32 = a := and_lowMask 1 (by decide) a h
theorem and_7 (a : W32) (h : a.toNat < 8) : a &&& 7#32 = a := and_lowMask 3 (by decide) a h
theorem and_15 (a : W32) (h : a.toNat < 16) : a &&& 15#32 = a := and_lowMask 4 (by decide) a h
theorem and_63 (a : W32) (h : a.toNat < 64) : a &&& 63#32 = a := and_lowMask 6 (by decide) a h
theorem and_511 (a : W32) (h : a.toNat < 2 ^ 9) : a &&& 511#32 = a := and_lowMask 9 (by decide) a h
theorem and_1023 (a : W32) (h : a.toNat < 2 ^ 10) : a &&& 1023#32 = a :=
  and_lowMask 10 (by decide) a h
theorem and_524287 (a : W32) (h : a.toNat < 2 ^ 19) : a &&& 524287#32 = a :=
  and_lowMask 19 (by decide) a h
theorem and_1048575 (a : W32) (h : a.toNat < 2 ^ 20) : a &&& 1048575#32 = a :=
  and_lowMask 20 (by decide) a h
-- BEGIN R6-3
theorem and_2097151 (a : W32) (h : a.toNat < 2 ^ 21) : a &&& 2097151#32 = a :=
  and_lowMask 21 (by decide) a h
-- END R6-3

theorem isModeledCp0Reg_lt (rd sel : W32) (h : isModeledCp0Reg rd sel = true) :
    rd.toNat < 32 ∧ sel.toNat < 8 := by
  simp only [isModeledCp0Reg, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ((⟨h0, h⟩ | ⟨h0, h⟩) | ⟨h0, h⟩) | ⟨h0, h⟩
  · subst h0
    rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h <;> subst h <;> decide
  · subst h0
    rcases h with (h | h) | h <;> subst h <;> decide
  · subst h0
    rcases h with h | h <;> subst h <;> decide
  · subst h0; subst h; decide

/-! ## Extracted fields are in range -/

theorem rsOf_lt (w : W32) : (rsOf w).toNat < 32 := by
  simp [rsOf, BitVec.extractLsb]; omega
theorem rtOf_lt (w : W32) : (rtOf w).toNat < 32 := by
  simp [rtOf, BitVec.extractLsb]; omega
theorem rdOf_lt (w : W32) : (rdOf w).toNat < 32 := by
  simp [rdOf, BitVec.extractLsb]; omega
theorem shamtOf_lt (w : W32) : (shamtOf w).toNat < 32 := by
  simp [shamtOf, BitVec.extractLsb]; omega
theorem immOf_lt (w : W32) : (immOf w).toNat < 2 ^ 16 := by
  simp [immOf, BitVec.extractLsb]; omega
theorem targetOf_lt (w : W32) : (targetOf w).toNat < 2 ^ 26 := by
  simp [targetOf, BitVec.extractLsb]; omega
theorem functOf_lt (w : W32) : (functOf w).toNat < 64 := by
  simp [functOf, BitVec.extractLsb]; omega
theorem off9Of_lt (w : W32) : (off9Of w).toNat < 2 ^ 9 := by
  simp [off9Of, BitVec.extractLsb]; omega
theorem code20Of_lt (w : W32) : (code20Of w).toNat < 2 ^ 20 := by
  simp [code20Of, BitVec.extractLsb]; omega
theorem code10Of_lt (w : W32) : (code10Of w).toNat < 2 ^ 10 := by
  simp [code10Of, BitVec.extractLsb]; omega
theorem code19Of_lt (w : W32) : (code19Of w).toNat < 2 ^ 19 := by
  simp [code19Of, BitVec.extractLsb]; omega
-- BEGIN R6-3
theorem off21Of_lt (w : W32) : (off21Of w).toNat < 2 ^ 21 := by
  simp [off21Of, BitVec.extractLsb]; omega
-- END R6-3

end DecodeSpec

open DecodeSpec

attribute [local simp] opcodeOf_or_mkRT rsOf_or_mkRT rtOf_or_mkRT rdOf_or_mkRT shamtOf_or_mkRT
  functOf_or_mkRT opcodeOf_mkRT rsOf_mkRT rtOf_mkRT rdOf_mkRT shamtOf_mkRT functOf_mkRT
  opcodeOf_mkIT rsOf_mkIT rtOf_mkIT immOf_mkIT opcodeOf_or_mkJT targetOf_or_mkJT
  coOf_or_mkRT
  opcodeOf_or_mkOff9 rsOf_or_mkOff9 rtOf_or_mkOff9 off9Of_or_mkOff9 bit6Of_or_mkOff9
  functOf_or_mkOff9
  opcodeOf_mkCode20 functOf_mkCode20 code20Of_mkCode20
  opcodeOf_mkTrap functOf_mkTrap rsOf_mkTrap rtOf_mkTrap code10Of_mkTrap
  opcodeOf_mkWait coOf_mkWait functOf_mkWait code19Of_mkWait
  and_31 and_65535 and_67108863 and_1 and_7 and_15 and_63 and_511 and_1023 and_524287 and_1048575
  -- BEGIN R6-3
  opcodeOf_mkOff21 rsOf_mkOff21 off21Of_mkOff21 and_2097151
  -- END R6-3

-- ~120 constructors, each unfolding the full `decode` match: needs more than
-- the default heartbeat budget.
set_option maxHeartbeats 1000000 in
/-- Round trip: decoding the encoding of a well-formed instruction returns it.
Covers every constructor of `Instruction`. -/
theorem decode_encode (i : Instruction) (h : i.WellFormed) : decode (encode i) = some i := by
  cases i <;> (revert h; simp only [Instruction.WellFormed]; intro h)
  case ext rt rs pos size =>
    obtain ⟨hrt, hrs, hpos, hs1, hs2⟩ := h
    have e1 : (size - 1#32) &&& 31#32 = size - 1#32 := and_31 _ (by bv_omega)
    have e2 : size - 1#32 + 1#32 = size := by bv_omega
    simp [encode, decode, decodeFor, decodePrimary, decodeSpecial3, decodeIf, hrt, hrs,
      hpos, e1, e2]
    omega
  case ins rt rs pos size =>
    obtain ⟨hrt, hrs, hpos, hs1, hs2⟩ := h
    have e1 : (pos + size - 1#32) &&& 31#32 = pos + size - 1#32 := and_31 _ (by bv_omega)
    have e2 : pos + size - 1#32 - pos + 1#32 = size := by bv_omega
    simp [encode, decode, decodeFor, decodePrimary, decodeSpecial3, decodeIf, hrt, hrs,
      hpos, e1, e2]
    omega
  case mfc0 rt rd sel =>
    obtain ⟨h1, h2⟩ := isModeledCp0Reg_lt rd sel h.2
    have h3 : sel.toNat < 64 := by omega
    simp [encode, decode, decodeFor, decodePrimary, decodeCop0, decodeIf, h, h1, h2, h3]
  case mtc0 rt rd sel =>
    obtain ⟨h1, h2⟩ := isModeledCp0Reg_lt rd sel h.2
    have h3 : sel.toNat < 64 := by omega
    simp [encode, decode, decodeFor, decodePrimary, decodeCop0, decodeIf, h, h1, h2, h3]
  case rdhwr rt rd sel =>
    obtain ⟨h1, h2, h3⟩ := h
    have e : sel &&& 31#32 = sel := and_31 _ (by omega)
    simp [encode, decode, decodeFor, decodePrimary, decodeSpecial3, decodeIf, h1, h2, h3, e]
  case sll rd rt shamt =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    by_cases e : rd = 0#32 ∧ rt = 0#32 ∧ shamt = 5#32
    · exact absurd e h4
    · simp only [not_and] at e
      simp [encode, decode, decodeFor, decodePrimary, decodeSpecial, decodeIf, h1, h2, h3]
      bv_omega
  -- BEGIN R6-3
  -- The compact branches: the `rs`/`rt` constraint selects the constructor within its opcode.
  case beqc rs rt off | bnec rs rt off =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    have h5 : rs.toNat < 32 := by omega
    have h6 : rs ≠ 0#32 := by intro e; subst e; simp at h1
    simp [encode, decode, decodeFor, decodePrimary, decodeLtGe, h2, h3, h4, h5, h6]
  case bltc rs rt off | bgec rs rt off | bltuc rs rt off | bgeuc rs rt off =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    have h7 : rs ≠ 0#32 := by intro e; subst e; simp at h1
    have h8 : rt ≠ 0#32 := by intro e; subst e; simp at h3
    simp [encode, decode, decodeFor, decodePrimary, decodeIf, decodeZeroEqTwo, h2, h4, h5, h6, h7, h8]
  case blezc rt off | bgezc rt off | bgtzc rt off | bltzc rt off | blezalc rt off | bgezalc rt off
      | bgtzalc rt off | bltzalc rt off =>
    obtain ⟨h1, h2, h3⟩ := h
    have h4 : rt ≠ 0#32 := by intro e; subst e; simp at h1
    simp [encode, decode, decodeFor, decodePrimary, decodeIf, decodeZeroEqTwo, h2, h3, h4]
  case beqzalc rt off | bnezalc rt off =>
    obtain ⟨h1, h2, h3⟩ := h
    simp [encode, decode, decodeFor, decodePrimary, decodeLtGe, h1, h2, h3]
  case bovc rs rt off | bnvc rs rt off =>
    obtain ⟨h1, h2, h3⟩ := h
    have h4 : rt.toNat < 32 := by omega
    simp [encode, decode, decodeFor, decodePrimary, decodeLtGe, h2, h3, h4]
    omega
  case beqzc rs off | bnezc rs off =>
    obtain ⟨h1, h2, h3⟩ := h
    have h4 : rs ≠ 0#32 := by intro e; subst e; simp at h1
    simp [encode, decode, decodeFor, decodePrimary, decodeJumpOrZ, h2, h3, h4]
  case jic rt off | jialc rt off =>
    simp [encode, decode, decodeFor, decodePrimary, decodeJumpOrZ, h]
  -- END R6-3
  all_goals simp [encode, decode, decodeFor, decodePrimary, decodeSpecial, decodeRegimm,
    decodeSpecial3, decodeCop0, decodeCop1, decodeCop1S, decodeCop1D, decodeIf, h]

-- Splits the whole `decode` table (~150 leaves).
set_option maxHeartbeats 1000000 in
/-- Everything `decode` produces is well-formed. -/
theorem decode_wellFormed (w : W32) (i : Instruction) (h : decode w = some i) :
    i.WellFormed := by
  have h1 := rsOf_lt w; have h2 := rtOf_lt w; have h3 := rdOf_lt w
  have h4 := shamtOf_lt w; have h5 := immOf_lt w; have h6 := targetOf_lt w
  have h7 := off9Of_lt w
  have h10 := code20Of_lt w; have h11 := code10Of_lt w; have h12 := code19Of_lt w
  -- BEGIN R6-3
  have h13 := off21Of_lt w
  -- END R6-3
  simp only [decode, decodeFor, decodePrimary, decodeSpecial, decodeRegimm, decodeSpecial3,
    decodeCop0, decodeCop1, decodeCop1S, decodeCop1D, decodeIf,
    -- BEGIN R6-3
    decodeZeroEqTwo, decodeLtGe, decodeJumpOrZ
    -- END R6-3
    ] at h
  repeat' split at h
  all_goals
    (cases h <;>
      simp only [Instruction.WellFormed, h1, h2, h3, h4, h5, h6, h7, h10, h11, h12,
        -- BEGIN R6-3
        h13,
        -- END R6-3
        and_self, true_and])
  -- Left over: `ext`, `ins` (arithmetic on fields), `mfc0`, `mtc0` (CP0 guard).
  all_goals rename_i hc
  all_goals first
    | (simp only [decide_eq_true_eq] at hc; bv_omega)
    | (simp only [Bool.and_eq_true] at hc; exact hc.2)
    | (simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.2)
    | (rename_i hp; intro ⟨ha, hb, hs⟩; simp [ha, hb, hs] at hp)
    -- BEGIN R6-3
    -- the compact branches: the decoder's `rs`/`rt` tests are the `WellFormed` constraint
    | (simp only [beq_iff_eq, beq_eq_false_iff_ne, Bool.not_eq_true', ne_eq,
        and_true, BitVec.toNat_eq, BitVec.toNat_zero] at *; omega)
    -- END R6-3
