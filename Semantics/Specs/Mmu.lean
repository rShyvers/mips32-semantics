import Std.Data.HashMap.Lemmas
import Semantics.Specs.Memory
import Semantics.Specs.Fetch
import Semantics.Specs.SelfModifying

/-!
# Mmu — the Fixed Mapping MMU: translation, address-error check, aliasing

The model's MMU is the Fixed Mapping MMU (`Config.MT = 3`; MD00090 Vol III Rev 6.02 Appendix A.1,
p.313-317). `State.lean` implements it once: `fixedMappingPA` (Table A.1, p.313-314) and
`translate` (the address-error check of Table 4.2, p.30, done "before the translation process",
§A.1.1, p.313). Every fetch, load and store goes through `translate` (the six `readMem*` /
`writeMem*` functions), so the per-instruction `_spec_raw` statements, which mention those
functions, are statements about translated memory without any change of form.

## Theorems in this file (21)

  `fixedMappingPA_kuseg_erl0` `fixedMappingPA_kuseg_erl1` `fixedMappingPA_kseg0`
  `fixedMappingPA_kseg1` `fixedMappingPA_kseg23` `fixedMappingPA_kseg0_kseg1_alias`
  `fixedMappingPA_low512` `translate_kernel` `translate_user_useg` `translate_user_kernel_address`
  `translate_erl1_kuseg_identity` `readMemWord_user_kernel_address`
  `readMemHalf_user_kernel_address` `readMemByte_user_kernel_address`
  `writeMemWord_user_kernel_address` `writeMemHalf_user_kernel_address`
  `writeMemByte_user_kernel_address` `step_fetch_user_kernel_address`
  `lw_user_kernel_address` `sw_user_kernel_address` `kseg1_store_visible_through_kseg0`
-/

set_option maxRecDepth 4000

/-! ## The fixed mapping, segment by segment (Table A.1, p.313-314) -/

/-- **useg/kuseg with `ERL = 0`: `PA = VA + 1 GB`** ("mapped by adding 1GB to the virtual address
when the ERL bit is zero"). Virtual `0x0000_0000`-`0x7FFF_FFFF` → physical `0x4000_0000`-
`0xBFFF_FFFF`. -/
theorem fixedMappingPA_kuseg_erl0 (va : W32) (h : va.toNat < 0x80000000) :
    fixedMappingPA false va = va + 0x40000000#32 ∧
      (fixedMappingPA false va).toNat = va.toNat + 0x40000000 := by
  unfold fixedMappingPA
  rw [ite_of_pos h]
  refine ⟨rfl, ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  bv_omega

/-- **useg/kuseg with `ERL = 1`: identity** ("mapped using an identity mapping when the ERL bit is
one"; §4.7, p.31: "the kuseg Segment becomes an unmapped, uncached Segment"). -/
theorem fixedMappingPA_kuseg_erl1 (va : W32) (h : va.toNat < 0x80000000) :
    fixedMappingPA true va = va := by
  unfold fixedMappingPA; rw [ite_of_pos h]; rfl

/-- **kseg0 → the low 512 MB**: `0x8000_0000`-`0x9FFF_FFFF` → `0x0000_0000`-`0x1FFF_FFFF`
(Table 4.3, p.31; Table A.1), whatever `ERL` is. -/
theorem fixedMappingPA_kseg0 (erl : Bool) (va : W32) (h1 : 0x80000000 ≤ va.toNat)
    (h2 : va.toNat < 0xA0000000) : (fixedMappingPA erl va).toNat = va.toNat - 0x80000000 := by
  unfold fixedMappingPA
  rw [ite_of_neg (by omega), ite_of_pos (by omega), BitVec.toNat_and]
  have : (0x1FFFFFFF#32).toNat = 2 ^ 29 - 1 := by simp
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- **kseg1 → the same low 512 MB**: `0xA000_0000`-`0xBFFF_FFFF` → `0x0000_0000`-`0x1FFF_FFFF`
(Table 4.3, p.31; Table A.1), whatever `ERL` is. -/
theorem fixedMappingPA_kseg1 (erl : Bool) (va : W32) (h1 : 0xA0000000 ≤ va.toNat)
    (h2 : va.toNat < 0xC0000000) : (fixedMappingPA erl va).toNat = va.toNat - 0xA0000000 := by
  unfold fixedMappingPA
  rw [ite_of_neg (by omega), ite_of_pos (by omega), BitVec.toNat_and]
  have : (0x1FFFFFFF#32).toNat = 2 ^ 29 - 1 := by simp
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- **kseg2 (sseg/ksseg) and kseg3: identity** ("Sseg/Ksseg/Kseg2/Kseg3 addresses are mapped
using an identity mapping"), whatever `ERL` is. -/
theorem fixedMappingPA_kseg23 (erl : Bool) (va : W32) (h : 0xC0000000 ≤ va.toNat) :
    fixedMappingPA erl va = va := by
  unfold fixedMappingPA; rw [ite_of_neg (by omega), ite_of_neg (by omega)]

/-- **kseg0 and kseg1 alias**: `0x8000_0000 + x` and `0xA000_0000 + x` (for `x < 512 MB`) are the
same physical address, `x` ("they both map to the low 512MB of physical memory", §A.1.1, p.313). -/
theorem fixedMappingPA_kseg0_kseg1_alias (erl : Bool) (x : W32) (hx : x.toNat < 0x20000000) :
    fixedMappingPA erl (0x80000000#32 + x) = x ∧ fixedMappingPA erl (0xA0000000#32 + x) = x := by
  have h0 : (0x80000000#32 + x).toNat = 0x80000000 + x.toNat := by
    rw [BitVec.toNat_add]; have : (0x80000000#32).toNat = 0x80000000 := rfl; omega
  have h1 : (0xA0000000#32 + x).toNat = 0xA0000000 + x.toNat := by
    rw [BitVec.toNat_add]; have : (0xA0000000#32).toNat = 0xA0000000 := rfl; omega
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [fixedMappingPA_kseg0 erl _ (by omega) (by omega)]; omega
  · apply BitVec.eq_of_toNat_eq
    rw [fixedMappingPA_kseg1 erl _ (by omega) (by omega)]; omega

/-- kseg0 and kseg1 reach only the low 512 MB (`PA < 0x2000_0000`). -/
theorem fixedMappingPA_low512 (erl : Bool) (va : W32) (h1 : 0x80000000 ≤ va.toNat)
    (h2 : va.toNat < 0xC0000000) : (fixedMappingPA erl va).toNat < 0x20000000 := by
  by_cases h : va.toNat < 0xA0000000
  · rw [fixedMappingPA_kseg0 erl va h1 h]; omega
  · rw [fixedMappingPA_kseg1 erl va (by omega) h2]; omega

/-! ## Translation and the address-error check (Table 4.2, p.30; §6.2.9, p.92) -/

/-- **Kernel Mode references every segment**, through the fixed mapping. -/
theorem translate_kernel (s : State) (va : W32) (h : kernelMode s = true) :
    translate s va = some (fixedMappingPA (erlSet s) va) :=
  translate_of_allowed s va (by simp [accessAllowed, h])

/-- **User Mode references useg** (`VA < 0x8000_0000`), through the fixed mapping (in User Mode
`ERL = 0`, so this is `VA + 1 GB`). -/
theorem translate_user_useg (s : State) (va : W32) (h : isUseg va = true) :
    translate s va = some (fixedMappingPA (erlSet s) va) :=
  translate_of_allowed s va (by simp [accessAllowed, h])

/-- **A kernel address from User Mode does not translate** (Address Error): kseg0, kseg1,
kseg2 and kseg3 are "Address Error" from User Mode (Table 4.2, p.30). -/
theorem translate_user_kernel_address (s : State) (va : W32) (hum : userMode s = true)
    (hk : isUseg va = false) : translate s va = none := by
  apply translate_of_not_allowed
  simp only [userMode, Bool.not_eq_eq_eq_not, Bool.not_true] at hum
  simp [accessAllowed, hum, hk]

/-- **With `Status.ERL = 1` kuseg is the identity map** (§4.7, p.31; Table A.1): `ERL = 1` is
Kernel Mode, so the reference is legal. -/
theorem translate_erl1_kuseg_identity (s : State) (va : W32) (herl : erlSet s = true)
    (h : va.toNat < 0x80000000) : translate s va = some va := by
  have hk : kernelMode s = true := by
    simp only [erlSet] at herl; simp [kernelMode, herl]
  rw [translate_kernel s va hk, herl, fixedMappingPA_kuseg_erl1 va h]

theorem readMemWord_user_kernel_address (s : State) (va : W32) (hum : userMode s = true)
    (hk : isUseg va = false) : readMemWord s va = none := by
  unfold readMemWord; split
  · rfl
  · rw [translate_user_kernel_address s va hum hk]

theorem readMemHalf_user_kernel_address (s : State) (va : W32) (hum : userMode s = true)
    (hk : isUseg va = false) : readMemHalf s va = none := by
  unfold readMemHalf; split
  · rfl
  · rw [translate_user_kernel_address s va hum hk]

theorem readMemByte_user_kernel_address (s : State) (va : W32) (hum : userMode s = true)
    (hk : isUseg va = false) : readMemByte s va = none := by
  unfold readMemByte; rw [translate_user_kernel_address s va hum hk]

theorem writeMemWord_user_kernel_address (s : State) (va v : W32) (hum : userMode s = true)
    (hk : isUseg va = false) : writeMemWord s va v = none := by
  unfold writeMemWord; split
  · rfl
  · rw [translate_user_kernel_address s va hum hk]

theorem writeMemHalf_user_kernel_address (s : State) (va v : W32) (hum : userMode s = true)
    (hk : isUseg va = false) : writeMemHalf s va v = none := by
  unfold writeMemHalf; split
  · rfl
  · rw [translate_user_kernel_address s va hum hk]

theorem writeMemByte_user_kernel_address (s : State) (va : W32) (v : UInt8)
    (hum : userMode s = true) (hk : isUseg va = false) : writeMemByte s va v = none := by
  unfold writeMemByte; rw [translate_user_kernel_address s va hum hk]

/-! ## Access control at the step level -/

/-- **Fetching from a kernel address in User Mode raises Address Error (AdEL)** with
`BadVAddr = EPC = pc` (MD00090 Vol III Rev 6.02 §6.2.9, p.92-93: "A reference is made to a kernel
address space from User Mode"; AdEL "Reference was a load or an instruction fetch"). -/
theorem step_fetch_user_kernel_address (s : State) (hum : userMode s = true)
    (hk : isUseg s.pc = false) : step s = timerTick (takeAddressException s excCodeAdEL s.pc) := by
  unfold step execute; rw [readMemWord_user_kernel_address s s.pc hum hk]

/-- **A User-Mode `lw` of a kernel address raises Address Error (AdEL)**, with `BadVAddr` = the
effective address, and changes no memory. -/
theorem lw_user_kernel_address (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none) (hum : userMode s = true)
    (hk : isUseg (readReg s (regIdxSpec rs) + signExt16 imm) = false) :
    step s = timerTick (takeAddressException s excCodeAdEL (readReg s (regIdxSpec rs) + signExt16 imm)) ∧
      (step s).physMem = s.physMem ∧
      (step s).cp0BadVAddr = readReg s (regIdxSpec rs) + signExt16 imm := by
  have h : step s = timerTick (takeAddressException s excCodeAdEL (readReg s (regIdxSpec rs) + signExt16 imm)) := by
    rw [lw_spec_raw s w rs rt imm hfetch hdecode hpb]
    dsimp only
    rw [readMemWord_user_kernel_address s _ hum hk]
  exact ⟨h, by rw [h]; rfl, by rw [h]; rfl⟩

/-- **A User-Mode `sw` to a kernel address raises Address Error (AdES)**, with `BadVAddr` = the
effective address, and the store does not happen (physical memory unchanged). -/
theorem sw_user_kernel_address (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none) (hum : userMode s = true)
    (hk : isUseg (readReg s (regIdxSpec rs) + signExt16 imm) = false) :
    step s = timerTick (takeAddressException s excCodeAdES (readReg s (regIdxSpec rs) + signExt16 imm)) ∧
      (step s).physMem = s.physMem ∧
      (step s).cp0BadVAddr = readReg s (regIdxSpec rs) + signExt16 imm := by
  have h : step s = timerTick (takeAddressException s excCodeAdES (readReg s (regIdxSpec rs) + signExt16 imm)) := by
    rw [sw_spec_raw s w rs rt imm hfetch hdecode hpb]
    dsimp only
    rw [writeMemWord_user_kernel_address s _ _ hum hk]
  exact ⟨h, by rw [h]; rfl, by rw [h]; rfl⟩

/-! ## Aliasing: one physical word, several virtual names -/

/-- **kseg0/kseg1 data aliasing**: in Kernel Mode, a word stored through kseg1 (uncached)
at `0xA000_0000 + x` is what a load through kseg0 at `0x8000_0000 + x` returns (both are physical
`x`, Table 4.3, p.31; §A.1.1, p.313). -/
theorem kseg1_store_visible_through_kseg0 (s s' : State) (x v : W32) (hk : kernelMode s = true)
    (hx : x.toNat < 0x20000000) (hal : x.toNat % 4 = 0)
    (h : writeMemWord s (0xA0000000#32 + x) v = some s') :
    readMemWord s' (0x80000000#32 + x) = some v := by
  apply readMemWord_writeMemWord_alias s s' _ _ v h
  · rw [BitVec.toNat_add]; have : (0x80000000#32).toNat = 0x80000000 := rfl; omega
  · rw [translate_kernel s _ hk, translate_kernel s _ hk,
      (fixedMappingPA_kseg0_kseg1_alias (erlSet s) x hx).1,
      (fixedMappingPA_kseg0_kseg1_alias (erlSet s) x hx).2]
