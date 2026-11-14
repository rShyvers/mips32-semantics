import Std.Data.HashMap.Lemmas
import Semantics.Specs.Mmu
import Semantics.Specs.Reset

/-!
# Loader — the image word is where the running program's fetch finds it

The loader (`Env.lean`, `loadImage`/`load`/`loadAtReset`; environment, not architecture) writes
each word of an assembled image (keyed by **virtual** address) into **physical** memory at
`loadAddr va = fixedMappingPA false va`: the Fixed Mapping translation with `Status.ERL = 0`
(MD00090 Vol III Rev 6.02 Table A.1, p.313-314). This file proves that a word read (instruction
fetch or `lw`) of an image address then returns the image word, whenever the reading state
translates that address to `loadAddr` of it — in particular in the hosted start state (Kernel
Mode, `ERL = 0`), in User Mode for useg addresses (`ERL = 0` in User Mode), and, for kseg0, kseg1,
kseg2 and kseg3 addresses, whatever `ERL` is (`loadAtReset`). The hypotheses on the image: its
addresses are word-aligned, and no two of them are loaded at the same physical address (an image
holding both `0x8000_0180` and `0xA000_0180` would load two words at physical `0x180`; the later
one wins).

The last section relates the loader to the observer's naming of physical addresses,
`Env.canonicalVAddr` (used by `MipsRun`'s `memory` JSON field). `loadAddr` is not injective (kseg0
and kseg1 alias the low 512 MB) and not surjective (it never yields `0x2000_0000`-`0x3FFF_FFFF`,
which only kuseg with `ERL = 1` reaches), so there is no two-sided inverse. What holds:
`canonicalVAddr` is a left inverse of `loadAddr` on every virtual address outside kseg1
(`canonicalVAddr_loadAddr`; a kseg1 address comes back as its kseg0 alias,
`canonicalVAddr_loadAddr_kseg1`), and a right inverse on the range of `loadAddr`, i.e. on every
physical address outside `0x2000_0000`-`0x3FFF_FFFF` (`loadAddr_canonicalVAddr`,
`loadAddr_not_hole`).

## Theorems in this file (21)

  `loadAddr_mod4` `addr_ne_of_aligned` `get?_loadWord_other` `get?_loadWord_same`
  `foldl_loadWord_other` `foldl_loadWord_mem` `loadImage_readMemWord` `translate_hostedStart`
  `load_readMemWord` `executesInstr_load` `load_step_fetches_image` `loadAtReset_readMemWord_kseg`
  `loadAddr_examples` `ofNat_0` `and_1fff_toNat` `loadAddr_toNat` `canonicalVAddr_toNat`
  `loadAddr_not_hole` `canonicalVAddr_loadAddr` `canonicalVAddr_loadAddr_kseg1`
  `loadAddr_canonicalVAddr`
-/

set_option maxRecDepth 4000

/-- The loader keeps the low two address bits: an aligned virtual word is an aligned physical word. -/
theorem loadAddr_mod4 (va : W32) : (loadAddr va).toNat % 4 = va.toNat % 4 := by
  unfold loadAddr fixedMappingPA
  split
  · simp only [Bool.false_eq_true, ↓reduceIte]
    bv_omega
  · split
    · rw [BitVec.toNat_and]
      have : (0x1FFFFFFF#32).toNat = 2 ^ 29 - 1 := by simp
      rw [this, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_mod_of_dvd _ (by decide)
    · rfl

/-- Two distinct word-aligned addresses have disjoint 4-byte ranges. -/
theorem addr_ne_of_aligned (p q : W32) (hp : p.toNat % 4 = 0) (hq : q.toNat % 4 = 0) (hne : p ≠ q)
    (i j : Nat) (hi : i < 4) (hj : j < 4) : (p + BitVec.ofNat 32 i == q + BitVec.ofNat 32 j) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  apply hne
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h'
  apply BitVec.eq_of_toNat_eq
  have hp' := p.isLt; have hq' := q.isLt
  have : i % 2 ^ 32 = i := Nat.mod_eq_of_lt (by omega)
  have : j % 2 ^ 32 = j := Nat.mod_eq_of_lt (by omega)
  omega

private theorem ofNat_0 (p : W32) : p + BitVec.ofNat 32 0 = p := by simp

/-- `loadWord m q w` leaves the bytes of another aligned word `pa` alone. -/
theorem get?_loadWord_other (m : Std.HashMap W32 UInt8) (q pa w : W32) (hq : q.toNat % 4 = 0)
    (hpa : pa.toNat % 4 = 0) (hne : q ≠ pa) (i : Nat) (hi : i < 4) :
    (loadWord m q w).get? (pa + BitVec.ofNat 32 i) = m.get? (pa + BitVec.ofNat 32 i) := by
  have e : ∀ j, j < 4 → (q + BitVec.ofNat 32 j == pa + BitVec.ofNat 32 i) = false :=
    fun j hj => addr_ne_of_aligned q pa hq hpa hne j i hj hi
  have e0 := e 0 (by omega); have e1 := e 1 (by omega)
  have e2 := e 2 (by omega); have e3 := e 3 (by omega)
  rw [ofNat_0] at e0
  unfold loadWord
  simp only [Std.HashMap.get?_insert]
  simp only [e0, e1, e2, e3, Bool.false_eq_true, ↓reduceIte]

/-- After `loadWord m pa w`, the four bytes at `pa` are `w`'s, big-endian. -/
theorem get?_loadWord_same (m : Std.HashMap W32 UInt8) (pa w : W32) :
    (loadWord m pa w).get? pa = some ((w >>> 24) &&& 0xff#32).toNat.toUInt8 ∧
    (loadWord m pa w).get? (pa + 1#32) = some ((w >>> 16) &&& 0xff#32).toNat.toUInt8 ∧
    (loadWord m pa w).get? (pa + 2#32) = some ((w >>> 8) &&& 0xff#32).toNat.toUInt8 ∧
    (loadWord m pa w).get? (pa + 3#32) = some (w &&& 0xff#32).toNat.toUInt8 := by
  have d1 : (pa + 1#32 == pa) = false := by simp
  have d2 : (pa + 2#32 == pa) = false := by simp
  have d3 : (pa + 3#32 == pa) = false := by simp
  have d21 : (pa + 2#32 == pa + 1#32) = false := by simp
  have d31 : (pa + 3#32 == pa + 1#32) = false := by simp
  have d32 : (pa + 3#32 == pa + 2#32) = false := by simp
  unfold loadWord
  simp only [Std.HashMap.get?_insert, d1, d2, d3, d21, d31, d32,
    beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, and_self]

/-- The four bytes at `pa` after loading a list of words none of which is loaded at `pa`. -/
theorem foldl_loadWord_other (l : List (W32 × W32)) (m : Std.HashMap W32 UInt8) (pa : W32)
    (hpa : pa.toNat % 4 = 0)
    (hl : ∀ x ∈ l, (loadAddr x.1).toNat % 4 = 0 ∧ loadAddr x.1 ≠ pa) (i : Nat) (hi : i < 4) :
    (l.foldl (fun m x => loadWord m (loadAddr x.1) x.2) m).get? (pa + BitVec.ofNat 32 i) =
      m.get? (pa + BitVec.ofNat 32 i) := by
  induction l generalizing m with
  | nil => rfl
  | cons x rest ih =>
    rw [List.foldl_cons, ih _ (fun y hy => hl y (List.mem_cons_of_mem _ hy))]
    have hx := hl x List.mem_cons_self
    exact get?_loadWord_other m _ pa x.2 hx.1 hpa hx.2 i hi

/-- The bytes at `loadAddr a` after loading a duplicate-free list containing `(a, w)` in which no
other key is loaded at the same physical address. -/
theorem foldl_loadWord_mem (l : List (W32 × W32)) (m : Std.HashMap W32 UInt8) (a w : W32)
    (hmem : (a, w) ∈ l) (hnd : l.Pairwise (fun x y => (x.1 == y.1) = false))
    (hal : (loadAddr a).toNat % 4 = 0)
    (hl : ∀ x ∈ l, x.1 ≠ a → (loadAddr x.1).toNat % 4 = 0 ∧ loadAddr x.1 ≠ loadAddr a) (i : Nat)
    (hi : i < 4) :
    (l.foldl (fun m x => loadWord m (loadAddr x.1) x.2) m).get? (loadAddr a + BitVec.ofNat 32 i) =
      (loadWord ∅ (loadAddr a) w).get? (loadAddr a + BitVec.ofNat 32 i) := by
  induction l generalizing m with
  | nil => cases hmem
  | cons x rest ih =>
    rw [List.foldl_cons]
    rw [List.pairwise_cons] at hnd
    by_cases hx : x.1 = a
    · -- `x` is the image entry for `a`: no later entry has key `a`
      have hrest : ∀ y ∈ rest, y.1 ≠ a := by
        intro y hy h
        have := hnd.1 y hy
        rw [hx, h] at this
        simp at this
      have hxw : x = (a, w) := by
        rcases List.mem_cons.mp hmem with h | h
        · exact h.symm
        · exact absurd rfl (hrest _ h)
      subst hxw
      rw [foldl_loadWord_other rest _ _ hal
        (fun y hy => hl y (List.mem_cons_of_mem _ hy) (hrest y hy)) i hi]
      have hs := get?_loadWord_same m (loadAddr a) w
      have hs0 := get?_loadWord_same (∅ : Std.HashMap W32 UInt8) (loadAddr a) w
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h
      · rw [ofNat_0, hs.1, hs0.1]
      · exact hs.2.1.trans hs0.2.1.symm
      · exact hs.2.2.1.trans hs0.2.2.1.symm
      · exact hs.2.2.2.trans hs0.2.2.2.symm
    · have hmem' : (a, w) ∈ rest := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd (by rw [← h]) hx
        · exact h
      exact ih _ hmem' hnd.2 (fun y hy => hl y (List.mem_cons_of_mem _ hy))

/-- **Loader correctness.** If the image `p` has the word `w` at the virtual address `a`, all image
addresses are word-aligned, no other image address is loaded at the same physical address, and the
state `s` translates `a` to `loadAddr a`, then after loading `p` into `s` a word read of `a`
(instruction fetch or `lw`) returns `w`. -/
theorem loadImage_readMemWord (p : Program) (s : State) (a w : W32) (hw : p.get? a = some w)
    (halign : ∀ b v, p.get? b = some v → b.toNat % 4 = 0)
    (hdisj : ∀ b v, p.get? b = some v → b ≠ a → loadAddr b ≠ loadAddr a)
    (htr : translate s a = some (loadAddr a)) :
    readMemWord (loadImage p s) a = some w := by
  have hal : a.toNat % 4 = 0 := halign a w hw
  have hpal : (loadAddr a).toNat % 4 = 0 := by rw [loadAddr_mod4]; exact hal
  have hmem : (a, w) ∈ p.toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]; simpa using hw
  have hl : ∀ x ∈ p.toList, x.1 ≠ a → (loadAddr x.1).toNat % 4 = 0 ∧ loadAddr x.1 ≠ loadAddr a := by
    intro x hx hne
    have hx' : p.get? x.1 = some x.2 := by
      have := (Std.HashMap.mem_toList_iff_getElem?_eq_some (m := p) (k := x.1) (v := x.2)).mp hx
      simpa using this
    exact ⟨by rw [loadAddr_mod4]; exact halign _ _ hx', hdisj _ _ hx' hne⟩
  have key := fun i hi => foldl_loadWord_mem p.toList s.physMem a w hmem
    Std.HashMap.distinct_keys_toList hpal hl i hi
  have hs0 := get?_loadWord_same (∅ : Std.HashMap W32 UInt8) (loadAddr a) w
  have tr : translate (loadImage p s) a = some (loadAddr a) := by
    rw [translate_congr (loadImage p s) s rfl a, htr]
  unfold readMemWord
  rw [ite_of_neg (by omega), tr]
  unfold loadImage
  simp only [Std.HashMap.fold_eq_foldl_toList]
  have k0 := key 0 (by omega); rw [ofNat_0, hs0.1] at k0
  have k1 := key 1 (by omega); rw [show BitVec.ofNat 32 1 = (1#32 : W32) from rfl, hs0.2.1] at k1
  have k2 := key 2 (by omega); rw [show BitVec.ofNat 32 2 = (2#32 : W32) from rfl, hs0.2.2.1] at k2
  have k3 := key 3 (by omega); rw [show BitVec.ofNat 32 3 = (3#32 : W32) from rfl, hs0.2.2.2] at k3
  rw [k0, k1, k2, k3]
  simp only [Option.getD_some, byte_toUInt8_toNat]
  rw [word_of_bytes]

/-- The hosted start state (Kernel Mode, `ERL = 0`) translates every address by `loadAddr`. -/
theorem translate_hostedStart (p : Program) (a : W32) : translate (load p) a = some (loadAddr a) := by
  have hst : (load p).cp0Status = hostedStart.cp0Status := rfl
  have hk : kernelMode hostedStart = true := by decide
  have he : erlSet hostedStart = false := by decide
  rw [translate_congr (load p) hostedStart hst a, translate_kernel hostedStart a hk, he]
  rfl

/-- **The hosted loader**: a word read of an image address in the loaded state returns the image
word (under the image hypotheses of `loadImage_readMemWord`). -/
theorem load_readMemWord (p : Program) (a w : W32) (hw : p.get? a = some w)
    (halign : ∀ b v, p.get? b = some v → b.toNat % 4 = 0)
    (hdisj : ∀ b v, p.get? b = some v → b ≠ a → loadAddr b ≠ loadAddr a) :
    readMemWord (load p) a = some w :=
  loadImage_readMemWord p hostedStart a w hw halign hdisj (translate_hostedStart p a)

/-- **A loaded program's first step executes an instruction**: the hosted start has `Status.IE = 0`
(`bootConvention`), so no interrupt is taken, and it is not in standby. -/
theorem executesInstr_load (p : Program) : executesInstr (load p) = true := by
  have hst : (load p).cp0Status = statusCu1Mask := rfl
  have hsb : (load p).standby = false := rfl
  have hie : (statusCu1Mask &&& statusIeMask != 0#32) = false := by decide
  unfold executesInstr interruptTaken interruptsEnabled
  rw [hst, hsb, hie]
  rfl

/-- **The first step of a loaded program executes the image word at `textBase`.** -/
theorem load_step_fetches_image (p : Program) (w : W32) (instr : Instruction)
    (hw : p.get? textBase = some w) (hdecode : decode w = some instr)
    (halign : ∀ b v, p.get? b = some v → b.toNat % 4 = 0)
    (hdisj : ∀ b v, p.get? b = some v → b ≠ textBase → loadAddr b ≠ loadAddr textBase) :
    step (load p) = timerTick (execInstr (load p) instr) :=
  step_fetches_from_memory (load p) w instr (load_readMemWord p textBase w hw halign hdisj) hdecode
    (executesInstr_load p)

/-- **The reset loader**, for kernel segments (kseg0, kseg1, kseg2, kseg3, where `ERL` does not
change the mapping): a word read of an image address in `loadAtReset p` (Kernel Mode, `ERL = 1`)
returns the image word — in particular the boot code at the reset vector `0xBFC0_0000`. -/
theorem loadAtReset_readMemWord_kseg (p : Program) (a w : W32) (hw : p.get? a = some w)
    (hk : 0x80000000 ≤ a.toNat)
    (halign : ∀ b v, p.get? b = some v → b.toNat % 4 = 0)
    (hdisj : ∀ b v, p.get? b = some v → b ≠ a → loadAddr b ≠ loadAddr a) :
    readMemWord (loadAtReset p) a = some w := by
  apply loadImage_readMemWord p resetState a w hw halign hdisj
  rw [translate_kernel resetState a (by decide)]
  have h8 : ¬ a.toNat < 0x80000000 := by omega
  unfold loadAddr fixedMappingPA
  simp only [h8, ↓reduceIte]

/-- Where the loader puts the MARS-convention sections (Table A.1 with `ERL = 0`). -/
theorem loadAddr_examples :
    loadAddr 0x00400000#32 = 0x40400000#32 ∧ loadAddr 0x10010000#32 = 0x50010000#32 ∧
    loadAddr 0x7FFFEFFC#32 = 0xBFFFEFFC#32 ∧ loadAddr 0x80000180#32 = 0x00000180#32 ∧
    loadAddr 0x90000000#32 = 0x10000000#32 ∧ loadAddr 0xBFC00000#32 = 0x1FC00000#32 ∧
    loadAddr 0xC0000000#32 = 0xC0000000#32 := by
  decide

/-! ## `canonicalVAddr`, the observer's inverse of `loadAddr` -/

private theorem and_1fff_toNat (va : W32) : (va &&& 0x1FFFFFFF#32).toNat = va.toNat % 2 ^ 29 := by
  rw [BitVec.toNat_and]
  have : (0x1FFFFFFF#32).toNat = 2 ^ 29 - 1 := by simp
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

/-- `loadAddr` on numbers: kuseg `+ 0x4000_0000`, kseg0/kseg1 the low 29 bits, kseg2/kseg3 identity. -/
theorem loadAddr_toNat (va : VAddr) :
    (loadAddr va).toNat =
      if va.toNat < 0x80000000 then va.toNat + 0x40000000
      else if va.toNat < 0xC0000000 then va.toNat % 2 ^ 29 else va.toNat := by
  unfold loadAddr fixedMappingPA
  by_cases h1 : va.toNat < 0x80000000
  · simp only [h1, ↓reduceIte, Bool.false_eq_true]; bv_omega
  · by_cases h2 : va.toNat < 0xC0000000
    · simp only [h1, h2, ↓reduceIte, and_1fff_toNat]
    · simp only [h1, h2, ↓reduceIte]

/-- `canonicalVAddr` on numbers. -/
theorem canonicalVAddr_toNat (pa : PAddr) :
    (canonicalVAddr pa).toNat =
      if pa.toNat < 0x20000000 then pa.toNat + 0x80000000
      else if pa.toNat < 0x40000000 then pa.toNat
      else if pa.toNat < 0xC0000000 then pa.toNat - 0x40000000 else pa.toNat := by
  unfold canonicalVAddr
  by_cases h1 : pa.toNat < 0x20000000
  · simp only [h1, ↓reduceIte]; bv_omega
  · by_cases h2 : pa.toNat < 0x40000000
    · simp only [h1, h2, ↓reduceIte]
    · by_cases h3 : pa.toNat < 0xC0000000
      · simp only [h1, h2, h3, ↓reduceIte]; bv_omega
      · simp only [h1, h2, h3, ↓reduceIte]

/-- **The range of `loadAddr`** misses `0x2000_0000`-`0x3FFF_FFFF` (reached only by kuseg with
`ERL = 1`, MD00090 Vol III Rev 6.02 Table A.1, p.314). -/
theorem loadAddr_not_hole (va : VAddr) :
    ¬ (0x20000000 ≤ (loadAddr va).toNat ∧ (loadAddr va).toNat < 0x40000000) := by
  rw [loadAddr_toNat]
  split <;> (try split) <;> omega

/-- **`canonicalVAddr` is a left inverse of `loadAddr` outside kseg1**: for every virtual address
not in kseg1 (`0xA000_0000`-`0xBFFF_FFFF`), the observer names the loaded physical address by the
virtual address it was loaded from. So every image word outside kseg1 appears in `MipsRun`'s
`memory` at its image address. -/
theorem canonicalVAddr_loadAddr (va : VAddr) (h : isKseg1 va = false) :
    canonicalVAddr (loadAddr va) = va := by
  unfold isKseg1 at h
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le, Nat.not_lt] at h
  apply BitVec.eq_of_toNat_eq
  rw [canonicalVAddr_toNat, loadAddr_toNat]
  have := va.isLt
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega

/-- **A kseg1 address comes back as its kseg0 alias** (`va - 0x2000_0000`): kseg0 and kseg1 map to
the same physical address, and `canonicalVAddr` picks the kseg0 name. -/
theorem canonicalVAddr_loadAddr_kseg1 (va : VAddr) (h : isKseg1 va = true) :
    canonicalVAddr (loadAddr va) = va - 0x20000000#32 := by
  unfold isKseg1 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  apply BitVec.eq_of_toNat_eq
  rw [canonicalVAddr_toNat, loadAddr_toNat, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  have := va.isLt
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega

/-- **`canonicalVAddr` is a right inverse of `loadAddr` on its range**: every physical address
outside `0x2000_0000`-`0x3FFF_FFFF` (the range of `loadAddr`, `loadAddr_not_hole`) is `loadAddr` of
its canonical virtual name. -/
theorem loadAddr_canonicalVAddr (pa : PAddr)
    (h : ¬ (0x20000000 ≤ pa.toNat ∧ pa.toNat < 0x40000000)) :
    loadAddr (canonicalVAddr pa) = pa := by
  apply BitVec.eq_of_toNat_eq
  rw [loadAddr_toNat, canonicalVAddr_toNat]
  have := pa.isLt
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega
