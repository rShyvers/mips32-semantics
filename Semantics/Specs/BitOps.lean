import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# BitOps — bit counting, sign extension, byte swap, bit-field extract/insert

Constructors: `clo` `clz` `seb` `seh` `wsbh` `ext` `ins`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  CLO p.134; CLZ p.135; SEB p.365; SEH p.366-367; WSBH p.445; EXT p.183-184; INS p.192-193.

Reference: `docs/spec/INSTRUCTION-REF.md`, sections "MIPS32 / MIPS32r2 additions (beyond the MARS-matched v1 baseline)"; "MIPS32r2 rotate and bitfield extract/insert (v1.x addition)".

## Theorems in this file (9)

  `clo_spec_raw` `clz_spec_raw` `seb_spec_raw` `seh_spec_raw` `wsbh_spec_raw` `ext_spec_raw`
  `ins_spec_raw` `ins_mask_absorb` `ins_outside_field_unchanged`
-/

set_option maxRecDepth 4000

/-! ## `clo`, `clz`, `seb`, `seh`, `wsbh`, `ext`, `ins`

MIPS32 / MIPS32r2 additions (`docs/spec/MIPS-COVERAGE-GAPS.md` §3.4/§3.5). The statements use
`countLeadingZerosSpec`, `countLeadingOnesSpec`, `signExtLowByteSpec` and `lowBitsMaskSpec`
(`Defs.lean`). (`mul` is in `MulDiv.lean`.) -/

/-- **`clo` counts `$rs`'s leading one bits (from the MSB) into `$rd`**;
`32` if `$rs` is all-ones (SPECIAL2 opcode 0x1c, funct 0x21; INSTRUCTION-REF
"clo"). -/
theorem clo_spec_raw (s : State) (w rs rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.clo rs rd))
    (hpb : s.pendingBranch = none) :
    step s =
      { (writeReg s (regIdxSpec rd)
            (BitVec.ofNat 32 (countLeadingOnesSpec (readReg s (regIdxSpec rs))))) with
          pc := (writeReg s (regIdxSpec rd)
            (BitVec.ofNat 32 (countLeadingOnesSpec (readReg s (regIdxSpec rs))))).pc + 4#32 } := by
  step_spec

/-- **`clz` counts `$rs`'s leading zero bits (from the MSB) into `$rd`**;
`32` if `$rs` is all-zero (SPECIAL2 opcode 0x1c, funct 0x20; INSTRUCTION-REF
"clz"). -/
theorem clz_spec_raw (s : State) (w rs rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.clz rs rd))
    (hpb : s.pendingBranch = none) :
    step s =
      { (writeReg s (regIdxSpec rd)
            (BitVec.ofNat 32 (countLeadingZerosSpec (readReg s (regIdxSpec rs))))) with
          pc := (writeReg s (regIdxSpec rd)
            (BitVec.ofNat 32 (countLeadingZerosSpec (readReg s (regIdxSpec rs))))).pc + 4#32 } := by
  step_spec

-- `clo`/`clz` satisfiable examples, matching `Step.lean`'s own `#guard`s:
-- all-ones -> 32 leading ones, all-zero -> 0; all-zero -> 32 leading zeros.
#guard (let s := stepIn (prog1Spec (.clo 8#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)])
        readReg s 10 == 32#32) = true

#guard (let s := stepIn (prog1Spec (.clo 8#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xfff0ffff#32)])
        readReg s 10 == 12#32) = true

#guard (let s := stepIn (prog1Spec (.clz 8#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x00000000#32)])
        readReg s 10 == 32#32) = true

#guard (let s := stepIn (prog1Spec (.clz 8#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x0000ffff#32)])
        readReg s 10 == 16#32) = true

/-- **`seb` sign-extends `$rt`'s low byte into `$rd`**, ignoring `$rt`'s
higher bits entirely (SPECIAL3 BSHFL opcode 0x1f, funct 0x20, sub-field
0x10; INSTRUCTION-REF "seb"). -/
theorem seb_spec_raw (s : State) (w rd rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.seb rd rt))
    (hpb : s.pendingBranch = none) :
    step s =
      { (writeReg s (regIdxSpec rd) (signExtLowByteSpec (readReg s (regIdxSpec rt)))) with
          pc := (writeReg s (regIdxSpec rd)
            (signExtLowByteSpec (readReg s (regIdxSpec rt)))).pc + 4#32 } := by
  step_spec

/-- **`seh` sign-extends `$rt`'s low halfword into `$rd`**, ignoring `$rt`'s
upper 16 bits entirely (SPECIAL3 BSHFL opcode 0x1f, funct 0x20, sub-field
0x18; INSTRUCTION-REF "seh"). Reuses the already-public `signExt16` directly
— no new mirror needed (same helper `addi`/`lw`/etc. already use for
immediates). -/
theorem seh_spec_raw (s : State) (w rd rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.seh rd rt))
    (hpb : s.pendingBranch = none) :
    step s =
      { (writeReg s (regIdxSpec rd) (signExt16 (readReg s (regIdxSpec rt)))) with
          pc := (writeReg s (regIdxSpec rd) (signExt16 (readReg s (regIdxSpec rt)))).pc + 4#32 } := by
  step_spec

-- `seb`/`seh` satisfiable examples, matching `Step.lean`'s own `#guard`s.
#guard (let s := stepIn (prog1Spec (.seb 10#32 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345680#32)])
        readReg s 10 == 0xffffff80#32) = true

#guard (let s := stepIn (prog1Spec (.seb 10#32 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x1234567f#32)])
        readReg s 10 == 0x0000007f#32) = true

#guard (let s := stepIn (prog1Spec (.seh 10#32 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x1234ffff#32)])
        readReg s 10 == 0xffffffff#32) = true

#guard (let s := stepIn (prog1Spec (.seh 10#32 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x12347fff#32)])
        readReg s 10 == 0x00007fff#32) = true

/-- **`wsbh` swaps the two bytes within each 16-bit half of `$rt`
independently, leaving the halfwords themselves in place** — not a full
32-bit byte-reverse (SPECIAL3 BSHFL opcode 0x1f, funct 0x20, sub-field 0x02;
INSTRUCTION-REF "wsbh"). The formula is small enough that `Step.lean` writes
it out inline with no helper, so this restates it directly. -/
theorem wsbh_spec_raw (s : State) (w rd rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.wsbh rd rt))
    (hpb : s.pendingBranch = none) :
    step s =
      let v := readReg s (regIdxSpec rt)
      let b0 := v &&& 0xff#32
      let b1 := (v >>> 8) &&& 0xff#32
      let b2 := (v >>> 16) &&& 0xff#32
      let b3 := (v >>> 24) &&& 0xff#32
      let result := (b2 <<< 24) ||| (b3 <<< 16) ||| (b0 <<< 8) ||| b1
      { (writeReg s (regIdxSpec rd) result) with
          pc := (writeReg s (regIdxSpec rd) result).pc + 4#32 } := by
  step_spec

-- `wsbh` satisfiable example, matching `Step.lean`'s own `#guard`: halfword0
-- `0x5678` swaps to `0x7856`, halfword1 `0x1234` swaps to `0x3412`, halfwords
-- stay in place -> `0x34127856`.
#guard (let s := stepIn (prog1Spec (.wsbh 10#32 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)])
        readReg s 10 == 0x34127856#32) = true

/-- **`ext` extracts a `size`-bit field of `$rs` starting at bit `pos`,
zero-extended, into `$rt`** (SPECIAL3 opcode 0x1f, funct 0x00;
INSTRUCTION-REF "ext"). `pos`/`size` are already the semantic values here —
`decode` did the raw-field +-1 arithmetic — so this is pure bit masking,
with no special case for the real `pos + size <= 32` hardware constraint
(matching `Step.lean`'s own documented choice). -/
theorem ext_spec_raw (s : State) (w rt rs pos size : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ext rt rs pos size))
    (hpb : s.pendingBranch = none) :
    step s =
      let field := (readReg s (regIdxSpec rs) >>> pos.toNat) &&& lowBitsMaskSpec size.toNat
      { (writeReg s (regIdxSpec rt) field) with
          pc := (writeReg s (regIdxSpec rt) field).pc + 4#32 } := by
  step_spec

/-- **`ins` inserts the low `size` bits of `$rs`, shifted up to bit `pos`,
into `$rt`, leaving every other bit of `$rt` untouched** (SPECIAL3 opcode
0x1f, funct 0x04; INSTRUCTION-REF "ins"). See `ins_outside_field_unchanged`
below for the "every other bit" half of this claim isolated and proved on
its own, the same way `movn`/`movz`'s "genuinely unchanged" properties are
proved elsewhere in this file. -/
theorem ins_spec_raw (s : State) (w rt rs pos size : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ins rt rs pos size))
    (hpb : s.pendingBranch = none) :
    step s =
      let mask := lowBitsMaskSpec size.toNat
      let srcField := (readReg s (regIdxSpec rs) &&& mask) <<< pos.toNat
      let clearMask := ~~~(mask <<< pos.toNat)
      let newVal := (readReg s (regIdxSpec rt) &&& clearMask) ||| srcField
      { (writeReg s (regIdxSpec rt) newVal) with
          pc := (writeReg s (regIdxSpec rt) newVal).pc + 4#32 } := by
  step_spec

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
theorem ins_outside_field_unchanged (s s' : State) (w rt rs pos size : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ins rt rs pos size))
    (hpb : s.pendingBranch = none)
    (hrt : regIdxSpec rt ≠ 0) (hsize32 : s.regs.size = 32)
    (hstep : step s = s') :
    let clearMask := ~~~(lowBitsMaskSpec size.toNat <<< pos.toNat)
    readReg s' (regIdxSpec rt) &&& clearMask = readReg s (regIdxSpec rt) &&& clearMask := by
  rw [ins_spec_raw s w rt rs pos size hfetch hdecode hpb] at hstep
  have hs := hstep
  have hr : readReg s' (regIdxSpec rt) =
      (readReg s (regIdxSpec rt) &&& ~~~(lowBitsMaskSpec size.toNat <<< pos.toNat)) |||
        ((readReg s (regIdxSpec rs) &&& lowBitsMaskSpec size.toNat) <<< pos.toNat) := by
    rw [← hs]
    exact writeReg_reads_back s (regIdxSpec rt) _ hrt hsize32
  dsimp only
  rw [hr]
  exact ins_mask_absorb _ _ _ _

-- `ext`/`ins` satisfiable examples, matching `Step.lean`'s own `#guard`s.
#guard (let s := stepIn (prog1Spec (.ext 10#32 8#32 6#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)])
        readReg s 10 == ((0x12345678#32 >>> 6) &&& 0x3ff#32)) = true

#guard (let s := stepIn (prog1Spec (.ext 10#32 8#32 0#32 32#32))
          (setRegsSpec (initialState textBase) [(8, 0x89abcdef#32)])
        readReg s 10 == 0x89abcdef#32) = true

#guard (let s := stepIn (prog1Spec (.ins 10#32 8#32 6#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x159#32), (10, 0x12345678#32)])
        readReg s 10 == ((0x12345678#32 &&& ~~~(0x3ff#32 <<< 6)) ||| ((0x159#32 &&& 0x3ff#32) <<< 6))) = true

-- `ins_outside_field_unchanged` concrete witness: bits outside `[6, 16)` of
-- `$t2` survive the `ins` untouched.
#guard (let s := stepIn (prog1Spec (.ins 10#32 8#32 6#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x159#32), (10, 0x12345678#32)])
        (readReg s 10 &&& ~~~(0x3ff#32 <<< 6)) == (0x12345678#32 &&& ~~~(0x3ff#32 <<< 6))) = true
