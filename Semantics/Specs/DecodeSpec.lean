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

/-- Closes a field-extraction goal bit by bit. -/
local macro "field_ext" : tactic =>
  `(tactic| (apply BitVec.eq_of_getLsbD_eq; intro i hi
             simp [opcodeOf, rsOf, rtOf, rdOf, shamtOf, functOf, immOf, targetOf,
               ccOf, ndOf, tfOf, fccOf, fcOf, z76Of, coOf, condOf, code20Of, code10Of, code19Of,
               mkRT, mkIT, mkJT, mkCCR, mkCCI, mkCmp, mkCode20, mkTrap, mkWait,
               field, maskLow, m5, m6, m16, m26, m1, m2, m3, m4, m10, m19, m20]
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

theorem fcOf_or_mkRT (x a b c d e : W32) :
    fcOf (x ||| mkRT a b c d e) = ((x >>> 4) &&& 3#32) ||| ((e >>> 4) &&& 3#32) := by field_ext
theorem coOf_or_mkRT (x a b c d e : W32) :
    coOf (x ||| mkRT a b c d e) = ((x >>> 25) &&& 1#32) ||| ((a >>> 4) &&& 1#32) := by field_ext

/-! ## Field extraction: `mkCCR ..` (`MOVCI`, `MOVCF.fmt`) -/

theorem opcodeOf_mkCCR (o a c n t r d e : W32) :
    opcodeOf (mkCCR o a c n t r d e) = o &&& 63#32 := by field_ext
theorem rsOf_mkCCR (o a c n t r d e : W32) : rsOf (mkCCR o a c n t r d e) = a &&& 31#32 := by
  field_ext
theorem ccOf_mkCCR (o a c n t r d e : W32) : ccOf (mkCCR o a c n t r d e) = c &&& 7#32 := by
  field_ext
theorem ndOf_mkCCR (o a c n t r d e : W32) : ndOf (mkCCR o a c n t r d e) = n &&& 1#32 := by
  field_ext
theorem tfOf_mkCCR (o a c n t r d e : W32) : tfOf (mkCCR o a c n t r d e) = t &&& 1#32 := by
  field_ext
theorem rdOf_mkCCR (o a c n t r d e : W32) : rdOf (mkCCR o a c n t r d e) = r &&& 31#32 := by
  field_ext
theorem shamtOf_mkCCR (o a c n t r d e : W32) :
    shamtOf (mkCCR o a c n t r d e) = d &&& 31#32 := by field_ext
theorem functOf_mkCCR (o a c n t r d e : W32) :
    functOf (mkCCR o a c n t r d e) = e &&& 63#32 := by field_ext
theorem fcOf_mkCCR (o a c n t r d e : W32) :
    fcOf (mkCCR o a c n t r d e) = (e >>> 4) &&& 3#32 := by field_ext

/-! ## Field extraction: `mkCCI ..` (FP branches) -/

theorem opcodeOf_mkCCI (o a c n t imm : W32) : opcodeOf (mkCCI o a c n t imm) = o &&& 63#32 := by
  field_ext
theorem rsOf_mkCCI (o a c n t imm : W32) : rsOf (mkCCI o a c n t imm) = a &&& 31#32 := by
  field_ext
theorem ccOf_mkCCI (o a c n t imm : W32) : ccOf (mkCCI o a c n t imm) = c &&& 7#32 := by
  field_ext
theorem ndOf_mkCCI (o a c n t imm : W32) : ndOf (mkCCI o a c n t imm) = n &&& 1#32 := by
  field_ext
theorem tfOf_mkCCI (o a c n t imm : W32) : tfOf (mkCCI o a c n t imm) = t &&& 1#32 := by
  field_ext
theorem immOf_mkCCI (o a c n t imm : W32) : immOf (mkCCI o a c n t imm) = imm &&& 65535#32 := by
  field_ext

/-! ## Field extraction: `mkCmp ..` (`C.cond.fmt`) -/

theorem opcodeOf_mkCmp (o f a b c x d : W32) : opcodeOf (mkCmp o f a b c x d) = o &&& 63#32 := by
  field_ext
theorem rsOf_mkCmp (o f a b c x d : W32) : rsOf (mkCmp o f a b c x d) = f &&& 31#32 := by
  field_ext
theorem rtOf_mkCmp (o f a b c x d : W32) : rtOf (mkCmp o f a b c x d) = a &&& 31#32 := by
  field_ext
theorem rdOf_mkCmp (o f a b c x d : W32) : rdOf (mkCmp o f a b c x d) = b &&& 31#32 := by
  field_ext
theorem fccOf_mkCmp (o f a b c x d : W32) : fccOf (mkCmp o f a b c x d) = c &&& 7#32 := by
  field_ext
theorem condOf_mkCmp (o f a b c x d : W32) : condOf (mkCmp o f a b c x d) = d &&& 15#32 := by
  field_ext
theorem fcOf_mkCmp (o f a b c x d : W32) : fcOf (mkCmp o f a b c x d) = x &&& 3#32 := by
  field_ext
theorem z76Of_mkCmp (o f a b c x d : W32) : z76Of (mkCmp o f a b c x d) = 0#32 := by field_ext

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
theorem and_1023 (a : W32) (h : a.toNat < 2 ^ 10) : a &&& 1023#32 = a :=
  and_lowMask 10 (by decide) a h
theorem and_524287 (a : W32) (h : a.toNat < 2 ^ 19) : a &&& 524287#32 = a :=
  and_lowMask 19 (by decide) a h
theorem and_1048575 (a : W32) (h : a.toNat < 2 ^ 20) : a &&& 1048575#32 = a :=
  and_lowMask 20 (by decide) a h

theorem isModeledCp0Reg_lt (rd sel : W32) (h : isModeledCp0Reg rd sel = true) :
    rd.toNat < 32 ∧ sel.toNat < 8 := by
  simp only [isModeledCp0Reg, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨h0, h⟩ | ⟨h0, h⟩
  · subst h0
    rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h <;> subst h <;> decide
  · subst h0
    rcases h with h | h <;> subst h <;> decide

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
theorem ccOf_lt (w : W32) : (ccOf w).toNat < 8 := by
  simp [ccOf, BitVec.extractLsb]; omega
theorem fccOf_lt (w : W32) : (fccOf w).toNat < 8 := by
  simp [fccOf, BitVec.extractLsb]; omega
theorem condOf_lt (w : W32) : (condOf w).toNat < 16 := by
  simp [condOf, BitVec.extractLsb]; omega
theorem code20Of_lt (w : W32) : (code20Of w).toNat < 2 ^ 20 := by
  simp [code20Of, BitVec.extractLsb]; omega
theorem code10Of_lt (w : W32) : (code10Of w).toNat < 2 ^ 10 := by
  simp [code10Of, BitVec.extractLsb]; omega
theorem code19Of_lt (w : W32) : (code19Of w).toNat < 2 ^ 19 := by
  simp [code19Of, BitVec.extractLsb]; omega

end DecodeSpec

open DecodeSpec

attribute [local simp] opcodeOf_or_mkRT rsOf_or_mkRT rtOf_or_mkRT rdOf_or_mkRT shamtOf_or_mkRT
  functOf_or_mkRT opcodeOf_mkRT rsOf_mkRT rtOf_mkRT rdOf_mkRT shamtOf_mkRT functOf_mkRT
  opcodeOf_mkIT rsOf_mkIT rtOf_mkIT immOf_mkIT opcodeOf_or_mkJT targetOf_or_mkJT
  fcOf_or_mkRT coOf_or_mkRT
  opcodeOf_mkCCR rsOf_mkCCR ccOf_mkCCR ndOf_mkCCR tfOf_mkCCR rdOf_mkCCR shamtOf_mkCCR
  functOf_mkCCR fcOf_mkCCR
  opcodeOf_mkCCI rsOf_mkCCI ccOf_mkCCI ndOf_mkCCI tfOf_mkCCI immOf_mkCCI
  opcodeOf_mkCmp rsOf_mkCmp rtOf_mkCmp rdOf_mkCmp fccOf_mkCmp condOf_mkCmp fcOf_mkCmp z76Of_mkCmp
  opcodeOf_mkCode20 functOf_mkCode20 code20Of_mkCode20
  opcodeOf_mkTrap functOf_mkTrap rsOf_mkTrap rtOf_mkTrap code10Of_mkTrap
  opcodeOf_mkWait coOf_mkWait functOf_mkWait code19Of_mkWait
  and_31 and_65535 and_67108863 and_1 and_7 and_15 and_63 and_1023 and_524287 and_1048575

-- ~180 constructors, each unfolding the full `decode` match: needs more than
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
    simp [encode, decode, decodeIf, hrt, hrs, hpos, e1, e2]
    omega
  case ins rt rs pos size =>
    obtain ⟨hrt, hrs, hpos, hs1, hs2⟩ := h
    have e1 : (pos + size - 1#32) &&& 31#32 = pos + size - 1#32 := and_31 _ (by bv_omega)
    have e2 : pos + size - 1#32 - pos + 1#32 = size := by bv_omega
    simp [encode, decode, decodeIf, hrt, hrs, hpos, e1, e2]
    omega
  case mfc0 rt rd sel =>
    obtain ⟨h1, h2⟩ := isModeledCp0Reg_lt rd sel h.2
    have h3 : sel.toNat < 64 := by omega
    simp [encode, decode, decodeIf, h, h1, h2, h3]
  case mtc0 rt rd sel =>
    obtain ⟨h1, h2⟩ := isModeledCp0Reg_lt rd sel h.2
    have h3 : sel.toNat < 64 := by omega
    simp [encode, decode, decodeIf, h, h1, h2, h3]
  all_goals simp [encode, decode, decodeIf, h]

-- Splits the whole `decode` match (~230 leaves).
set_option maxHeartbeats 1000000 in
/-- Everything `decode` produces is well-formed. -/
theorem decode_wellFormed (w : W32) (i : Instruction) (h : decode w = some i) :
    i.WellFormed := by
  have h1 := rsOf_lt w; have h2 := rtOf_lt w; have h3 := rdOf_lt w
  have h4 := shamtOf_lt w; have h5 := immOf_lt w; have h6 := targetOf_lt w
  have h7 := ccOf_lt w; have h8 := fccOf_lt w; have h9 := condOf_lt w
  have h10 := code20Of_lt w; have h11 := code10Of_lt w; have h12 := code19Of_lt w
  simp only [decode, decodeIf] at h
  repeat' split at h
  all_goals
    (cases h <;>
      simp only [Instruction.WellFormed, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
        and_self, true_and])
  -- Left over: `ext`, `ins` (arithmetic on fields), `mfc0`, `mtc0` (CP0 guard).
  all_goals rename_i hc
  all_goals first
    | (simp only [decide_eq_true_eq] at hc; bv_omega)
    | (simp only [Bool.and_eq_true] at hc; exact hc.2)
