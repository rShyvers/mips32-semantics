import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# MulDiv — multiply, divide, multiply-accumulate and the HI/LO registers

Constructors: `mult` `multu` `div` `divu` `mflo` `mfhi` `mthi` `mtlo` `mul` `madd` `maddu` `msub` `msubu`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  MULT p.303; MULTU p.304-305; DIV p.165-167; DIVU p.171; MFLO p.274; MFHI p.273; MTHI p.297;
  MTLO p.298; MUL p.299; MADD p.255; MADDU p.261; MSUB p.286; MSUBU p.289.

Reference: `docs/spec/INSTRUCTION-REF.md`, sections "Multiply / divide"; "Integer multiply-accumulate and HI/LO register moves (v1.x addition)"; "MIPS32 GPR multiply and variable shifts (v1.x addition)".

## Theorems in this file (18)

  `div_spec_raw` `div_by_zero_spec` `div_negative_dividend_spec` `mult_spec_raw` `multu_spec_raw`
  `divu_spec_raw` `divu_by_zero_spec` `mflo_spec_raw` `mfhi_spec_raw` `mthi_spec_raw`
  `mtlo_spec_raw` `mthi_mfhi_round_trip` `madd_spec_raw` `maddu_spec_raw` `msub_spec_raw`
  `msubu_spec_raw` `mul_spec_raw` `mul_leaves_hi_lo_unchanged`
-/

set_option maxRecDepth 4000

/-- **`div` by a nonzero divisor truncates toward zero; the remainder takes
the dividend's sign** (Lean's `Int.tdiv`/`Int.tmod`, matching Java's `/`/`%`
used by MARS — INSTRUCTION-REF "div" section). **`div` by zero leaves `hi`
and `lo` untouched and raises no exception** (SPEC-NOTES §9.2 / INSTRUCTION-REF
"div" MARS-note: this is a deliberate MIPS32-spec reading, not a MARS bug).
Both cases always advance the program counter by 4. -/
theorem div_spec_raw (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.div rs rt))
    (hpb : s.pendingBranch = none) :
    step s = timerTick (
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      if b == 0 then
        { s with pc := s.pc + 4#32 }
      else
        { s with lo := ofInt32 (a.tdiv b), hi := ofInt32 (a.tmod b), pc := s.pc + 4#32 }) := by
  step_spec

/-- Corollary of `div_spec_raw`: dividing by `0` leaves `hi`/`lo` exactly as
they were and raises no exception — INSTRUCTION-REF "div" MARS-note, SPEC-NOTES
§9.2. -/
theorem div_by_zero_spec (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.div rs rt))
    (hpb : s.pendingBranch = none)
    (hzero : readReg s (regIdxSpec rt) = 0#32) :
    step s = timerTick ({ s with pc := s.pc + 4#32 }) := by
  rw [div_spec_raw s w rs rt hfetch hdecode hpb, hzero]
  rfl

/-- Corollary of `div_spec_raw`: with a **negative dividend** and a nonzero
divisor, `div` rounds toward zero, so the remainder written to `hi`
(`Int.tmod`) is **never positive** — it takes the dividend's sign, whatever
the divisor's sign (INSTRUCTION-REF "div" section). A floor-rounding
division would give a positive remainder for a positive divisor. -/
theorem div_negative_dividend_spec (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.div rs rt))
    (hpb : s.pendingBranch = none)
    (hnz : asSigned (readReg s (regIdxSpec rt)) ≠ 0)
    (hneg : asSigned (readReg s (regIdxSpec rs)) < 0) :
    step s = timerTick (
      { s with
          lo := ofInt32 ((asSigned (readReg s (regIdxSpec rs))).tdiv (asSigned (readReg s (regIdxSpec rt))))
          hi := ofInt32 ((asSigned (readReg s (regIdxSpec rs))).tmod (asSigned (readReg s (regIdxSpec rt))))
          pc := s.pc + 4#32 }) ∧
      (asSigned (readReg s (regIdxSpec rs))).tmod (asSigned (readReg s (regIdxSpec rt))) ≤ 0 := by
  constructor
  · rw [div_spec_raw s w rs rt hfetch hdecode hpb]
    simp [hnz]
  · have h1 := Int.tmod_nonneg (a := -asSigned (readReg s (regIdxSpec rs)))
      (asSigned (readReg s (regIdxSpec rt))) (by omega)
    rw [Int.neg_tmod] at h1
    omega

/-! ### Satisfiable examples -/

-- `div_by_zero_spec`: dividing by `0` leaves a pre-seeded `hi`/`lo` alone.
#guard (let s := stepIn (prog1Spec (.div 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 10#32), (9, 0#32)]) with
            hi := 0xdeadbeef#32, lo := 0xcafef00d#32 }
        s.hi == 0xdeadbeef#32 && s.lo == 0xcafef00d#32) = true

-- `div_negative_dividend_spec`: `-17 / 5` truncates to `-3`; the remainder
-- `-2` carries the dividend's sign (`tdiv`/`tmod`, not Euclidean division).
#guard (let s := stepIn (prog1Spec (.div 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffef#32), (9, 5#32)])
        s.lo == 0xfffffffd#32 && s.hi == 0xfffffffe#32) = true

/-! ## `mult`, `multu`, `divu`, `mflo`, `mfhi`, `mthi`, `mtlo`, `madd`, `maddu`, `msub`, `msubu`, `mul`

`docs/spec/INSTRUCTION-REF.md` "Multiply / divide" and the "mthi (R)"/"mtlo (R)" sections. -/

/-- **`mult` forms the exact signed 64-bit product of `$rs` and `$rt`,
splitting it into `hi`/`lo`.** No GPR is written, and `mult` raises no exception
(INSTRUCTION-REF "mult" section: MARS never traps on multiply overflow —
the full 64-bit result always fits in `hi:lo`). -/
theorem mult_spec_raw (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mult rs rt))
    (hpb : s.pendingBranch = none) :
    step s = timerTick (
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
      { s with lo := prod64.extractLsb 31 0, hi := prod64.extractLsb 63 32, pc := s.pc + 4#32 }) := by
  step_spec

/-- **`multu` forms the exact unsigned 64-bit product of `$rs` and `$rt`,
splitting it into `hi`/`lo`.** Mirrors `mult_spec_raw`, except both
operands are read as unsigned `Nat`s first (INSTRUCTION-REF "multu"
section). Raises no exception. -/
theorem multu_spec_raw (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.multu rs rt))
    (hpb : s.pendingBranch = none) :
    step s = timerTick (
      let a := (readReg s (regIdxSpec rs)).toNat
      let b := (readReg s (regIdxSpec rt)).toNat
      let prod64 : BitVec 64 := BitVec.ofNat 64 (a * b)
      { s with lo := prod64.extractLsb 31 0, hi := prod64.extractLsb 63 32, pc := s.pc + 4#32 }) := by
  step_spec

-- `mult_spec_raw`: `5 * 7 = 35` fits entirely in `lo`, `hi = 0`.
#guard (let s := stepIn (prog1Spec (.mult 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)])
        s.lo == 35#32 && s.hi == 0#32) = true

-- `mult_spec_raw`: a negative times a positive operand gives a negative
-- 64-bit product, so `hi` is all-ones (sign-extension of the product).
#guard (let s := stepIn (prog1Spec (.mult 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffe#32), (9, 5#32)])
        s.lo == 0xfffffff6#32 && s.hi == 0xffffffff#32) = true

-- `multu_spec_raw`: the same bit pattern `0xfffffffe` is unsigned, so
-- `0xfffffffe * 5` overflows into a nonzero `hi` without any sign-extension.
#guard (let s := stepIn (prog1Spec (.multu 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffe#32), (9, 5#32)])
        s.lo == 0xfffffff6#32 && s.hi == 4#32) = true

/-- **`divu` by a nonzero divisor is ordinary unsigned division/remainder;
`divu` by zero leaves `hi`/`lo` untouched and raises no exception.** Unsigned
counterpart of `div_spec_raw` (INSTRUCTION-REF "divu" section — same
by-zero-is-a-silent-no-op MARS deviation documented for `div`). Always
advances the program counter by 4. -/
theorem divu_spec_raw (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.divu rs rt))
    (hpb : s.pendingBranch = none) :
    step s = timerTick (
      let a := (readReg s (regIdxSpec rs)).toNat
      let b := (readReg s (regIdxSpec rt)).toNat
      if b == 0 then
        { s with pc := s.pc + 4#32 }
      else
        { s with lo := BitVec.ofNat 32 (a / b), hi := BitVec.ofNat 32 (a % b), pc := s.pc + 4#32 }) := by
  step_spec

/-- Corollary of `divu_spec_raw`: dividing by `0` leaves `hi`/`lo` exactly
as they were and raises no exception — the unsigned counterpart of
`div_by_zero_spec` (INSTRUCTION-REF "divu" section). -/
theorem divu_by_zero_spec (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.divu rs rt))
    (hpb : s.pendingBranch = none)
    (hzero : readReg s (regIdxSpec rt) = 0#32) :
    step s = timerTick ({ s with pc := s.pc + 4#32 }) := by
  rw [divu_spec_raw s w rs rt hfetch hdecode hpb, hzero]
  rfl

-- `divu_spec_raw`: `17u / 5u = 3` remainder `2`, ordinary unsigned division.
#guard (let s := stepIn (prog1Spec (.divu 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 17#32), (9, 5#32)])
        s.lo == 3#32 && s.hi == 2#32) = true

-- `divu_by_zero_spec`: dividing by `0` leaves a pre-seeded `hi`/`lo` alone,
-- the unsigned counterpart of the `div_by_zero_spec` example above.
#guard (let s := stepIn (prog1Spec (.divu 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 10#32), (9, 0#32)]) with
            hi := 0x11#32, lo := 0x22#32 }
        s.lo == 0x22#32 && s.hi == 0x11#32) = true

/-- **`mflo` copies `lo` into `$rd`.** Trivial register read
(INSTRUCTION-REF "mflo" section); raises no exception. -/
theorem mflo_spec_raw (s : State) (w rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mflo rd))
    (hpb : s.pendingBranch = none) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rd) s.lo) with
          pc := (writeReg s (regIdxSpec rd) s.lo).pc + 4#32 }) := by
  step_spec

/-- **`mfhi` copies `hi` into `$rd`.** Trivial register read
(INSTRUCTION-REF "mfhi" section); raises no exception. -/
theorem mfhi_spec_raw (s : State) (w rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfhi rd))
    (hpb : s.pendingBranch = none) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rd) s.hi) with
          pc := (writeReg s (regIdxSpec rd) s.hi).pc + 4#32 }) := by
  step_spec

/-- **`mthi` copies `$rs` into `hi`; `lo` is left unchanged.** Write-direction
counterpart to `mfhi_spec_raw` (INSTRUCTION-REF "mthi (R)" section); no GPR
is written, raises no exception. -/
theorem mthi_spec_raw (s : State) (w rs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mthi rs))
    (hpb : s.pendingBranch = none) :
    step s = timerTick ({ s with hi := readReg s (regIdxSpec rs), pc := s.pc + 4#32 }) := by
  step_spec

/-- **`mtlo` copies `$rs` into `lo`; `hi` is left unchanged.** Write-direction
counterpart to `mflo_spec_raw` (INSTRUCTION-REF "mtlo (R)" section); no GPR
is written, raises no exception. -/
theorem mtlo_spec_raw (s : State) (w rs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtlo rs))
    (hpb : s.pendingBranch = none) :
    step s = timerTick ({ s with lo := readReg s (regIdxSpec rs), pc := s.pc + 4#32 }) := by
  step_spec

/-- **Round-trip check: `mthi` immediately followed by `mfhi` recovers
`$rs`'s original value through `hi`.** This is the "the half-pair actually
composes" check for `mthi`/`mfhi`: it is not enough for each instruction to
close on its own — writing `hi := $rs` and then reading `$rd := hi` two
steps later must produce exactly the value `$rs` held *before* either
instruction ran. Needs `regIdxSpec rd ≠ 0` (a write to `$zero` is a no-op,
INSTRUCTION-REF Global rule 2) and `s.regs.size = 32` (`writeReg_reads_back`'s
side condition, guaranteed by `initialState` — `State.lean`). -/
theorem mthi_mfhi_round_trip (s : State) (w w2 rs rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mthi rs))
    (hpb : s.pendingBranch = none)
    (hfetch2 : readMemWord s (s.pc + 4#32) = some w2) (hdecode2 : decode w2 = some (.mfhi rd))
    (hrd : regIdxSpec rd ≠ 0) (hsize32 : s.regs.size = 32) :
    ∃ s1 s2,
      step s = s1 ∧
      step s1 = s2 ∧
      readReg s2 (regIdxSpec rd) = readReg s (regIdxSpec rs) := by
  have h1 := mthi_spec_raw s w rs hfetch hdecode hpb
  have h2 := mfhi_spec_raw (timerTick { s with hi := readReg s (regIdxSpec rs), pc := s.pc + 4#32 }) w2 rd
    hfetch2 hdecode2 hpb
  refine ⟨_, _, h1, h2, ?_⟩
  exact writeReg_reads_back _ (regIdxSpec rd) _ hrd hsize32

-- `mthi_spec_raw`/`mfhi_spec_raw` concrete witness, standalone: `mthi` sets
-- `hi` from `$t0`, `mfhi` reads it back into `$t1`.
#guard (let s := stepIn (prog1Spec (.mthi 8#32)) (setRegsSpec (initialState textBase) [(8, 0x2a#32)])
        s.hi == 0x2a#32 && s.lo == 0#32) = true

-- `mtlo_spec_raw` concrete witness: `mtlo` sets `lo` from `$t0`, `hi`
-- untouched.
#guard (let s := stepIn (prog1Spec (.mtlo 8#32)) (setRegsSpec (initialState textBase) [(8, 0x2a#32)])
        s.lo == 0x2a#32 && s.hi == 0#32) = true

-- `mthi_mfhi_round_trip` concrete witness: `mthi $t0; mfhi $t1` leaves
-- `$t1` holding exactly `$t0`'s original value.
#guard (let s1 := stepIn (buildProgSpec textBase [.mthi 8#32, .mfhi 9#32])
          (setRegsSpec (initialState textBase) [(8, 0x2a#32)])
        let s2 := step s1
        readReg s2 9 == 0x2a#32) = true

/-- **`madd` adds the signed 64-bit product of `$rs`/`$rt` onto the
EXISTING `{hi,lo}` accumulator — it does not overwrite it.** The addend is
`s.hi ++ s.lo` (the 64-bit value already sitting in the accumulator
*before* this instruction runs), reassembled exactly as `Step.lean` does
and genuinely used as one operand of the `+` below, not discarded
(INSTRUCTION-REF "madd (R, SPECIAL2)" section). The 64-bit add wraps on
overflow, matching `mult`'s non-trapping precedent; raises no exception. -/
theorem madd_spec_raw (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.madd rs rt))
    (hpb : s.pendingBranch = none) :
    step s = timerTick (
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
      let acc64 : BitVec 64 := s.hi ++ s.lo
      let sum64 := acc64 + prod64
      { s with lo := sum64.extractLsb 31 0, hi := sum64.extractLsb 63 32, pc := s.pc + 4#32 }) := by
  step_spec

/-- **`maddu` adds the unsigned 64-bit product of `$rs`/`$rt` onto the
EXISTING `{hi,lo}` accumulator.** Unsigned counterpart of `madd_spec_raw`
(INSTRUCTION-REF "maddu (R, SPECIAL2)" section); same "accumulate, don't
overwrite" shape — `acc64` is built from `s.hi`/`s.lo` as they stood before
this instruction ran. Raises no exception. -/
theorem maddu_spec_raw (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.maddu rs rt))
    (hpb : s.pendingBranch = none) :
    step s = timerTick (
      let a := (readReg s (regIdxSpec rs)).toNat
      let b := (readReg s (regIdxSpec rt)).toNat
      let prod64 : BitVec 64 := BitVec.ofNat 64 (a * b)
      let acc64 : BitVec 64 := s.hi ++ s.lo
      let sum64 := acc64 + prod64
      { s with lo := sum64.extractLsb 31 0, hi := sum64.extractLsb 63 32, pc := s.pc + 4#32 }) := by
  step_spec

/-- **`msub` subtracts the signed 64-bit product of `$rs`/`$rt` from the
EXISTING `{hi,lo}` accumulator — it does not overwrite it.** Same
accumulator-reassembly shape as `madd_spec_raw`, but `acc64 - prod64`
instead of `acc64 + prod64` (INSTRUCTION-REF "msub (R, SPECIAL2)" section).
Wraps on underflow; raises no exception. -/
theorem msub_spec_raw (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.msub rs rt))
    (hpb : s.pendingBranch = none) :
    step s = timerTick (
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
      let acc64 : BitVec 64 := s.hi ++ s.lo
      let diff64 := acc64 - prod64
      { s with lo := diff64.extractLsb 31 0, hi := diff64.extractLsb 63 32, pc := s.pc + 4#32 }) := by
  step_spec

/-- **`msubu` subtracts the unsigned 64-bit product of `$rs`/`$rt` from the
EXISTING `{hi,lo}` accumulator.** Unsigned counterpart of `msub_spec_raw`
(INSTRUCTION-REF "msubu (R, SPECIAL2)" section); same accumulate-not-
overwrite shape. Raises no exception. -/
theorem msubu_spec_raw (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.msubu rs rt))
    (hpb : s.pendingBranch = none) :
    step s = timerTick (
      let a := (readReg s (regIdxSpec rs)).toNat
      let b := (readReg s (regIdxSpec rt)).toNat
      let prod64 : BitVec 64 := BitVec.ofNat 64 (a * b)
      let acc64 : BitVec 64 := s.hi ++ s.lo
      let diff64 := acc64 - prod64
      { s with lo := diff64.extractLsb 31 0, hi := diff64.extractLsb 63 32, pc := s.pc + 4#32 }) := by
  step_spec

-- `madd_spec_raw`: a pre-seeded accumulator of `{hi=0,lo=100}` plus
-- `5 * 7 = 35` gives `135`, i.e. the existing `lo` value is genuinely an
-- addend, not discarded.
#guard (let s := stepIn (prog1Spec (.madd 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with hi := 0#32, lo := 100#32 }
        s.lo == 135#32 && s.hi == 0#32) = true

-- `maddu_spec_raw`: same pre-seeded accumulator, unsigned product.
#guard (let s := stepIn (prog1Spec (.maddu 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with hi := 0#32, lo := 100#32 }
        s.lo == 135#32 && s.hi == 0#32) = true

-- `msub_spec_raw`: a pre-seeded accumulator of `{hi=0,lo=100}` minus
-- `5 * 7 = 35` gives `65`, i.e. the existing `lo` value is genuinely a
-- minuend, not discarded.
#guard (let s := stepIn (prog1Spec (.msub 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with hi := 0#32, lo := 100#32 }
        s.lo == 65#32 && s.hi == 0#32) = true

-- `msubu_spec_raw`: same pre-seeded accumulator, unsigned product.
#guard (let s := stepIn (prog1Spec (.msubu 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with hi := 0#32, lo := 100#32 }
        s.lo == 65#32 && s.hi == 0#32) = true

/-- **`mul` writes the low 32 bits of the signed product `$rs * $rt` to
`$rd`; `hi`/`lo` are left completely unchanged** (SPECIAL2 opcode 0x1c,
funct 0x02; INSTRUCTION-REF "mul"). Unlike `mult`, this never touches the
`hi`/`lo` accumulator at all — see `mul_leaves_hi_lo_unchanged` below for
that half of the claim isolated. -/
theorem mul_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mul rs rt rd))
    (hpb : s.pendingBranch = none) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs) * readReg s (regIdxSpec rt))) with
          pc := (writeReg s (regIdxSpec rd)
            (readReg s (regIdxSpec rs) * readReg s (regIdxSpec rt))).pc + 4#32 }) := by
  step_spec

/-- **"Bad output rejection" for `mul`**: the resulting state's `hi`/`lo`
read back *exactly* their pre-step values — a buggy implementation that
routed `mul` through the same `hi`/`lo`-writing path as `mult` could never
satisfy this. -/
theorem mul_leaves_hi_lo_unchanged (s s' : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mul rs rt rd))
    (hpb : s.pendingBranch = none)
    (hstep : step s = s') :
    s'.hi = s.hi ∧ s'.lo = s.lo := by
  rw [mul_spec_raw s w rs rt rd hfetch hdecode hpb] at hstep
  have hs := hstep
  rw [← hs]
  exact ⟨writeReg_hi s _ _, writeReg_lo s _ _⟩

-- `mul` satisfiable examples, matching `Step.lean`'s own `#guard`s: the
-- regular product case, and signed wraparound ((-1) * 2 = -2).
#guard (let s := stepIn (prog1Spec (.mul 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 6#32), (9, 7#32)])
        readReg s 10 == 42#32) = true

#guard (let s := stepIn (prog1Spec (.mul 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 2#32)])
        readReg s 10 == 0xfffffffe#32) = true
