import Semantics.Specs.Defs
import Semantics.Refine.Defs
import Semantics.FpOpsSpec
import Semantics.Manual.Accuracy

/-!
# Statements — the trusted surface, statements only

This is the **challenge** module of `lake comparator` (`comparator.json`): the theorems a reviewer
is asked to read, each stated exactly as in the proof files and with its proof elided (`sorry`).
The **solution** module is `Semantics/StatementsProofs.lean`, which states the same theorems in
the same order and proves each one by citing the real theorem of the same name in
`Semantics/Specs/`. `lake comparator` builds the two modules separately and accepts only if, for
every name listed in `comparator.json`, the solution proves *the same statement* (the same type,
over identical definitions) using no axiom other than `propext`, `Classical.choice`,
`Quot.sound`, and Lean's kernel accepts the proof. So: read this file (and the definitions it
mentions) instead of the proofs; if a statement here and the proved one drifted apart, the gate
would be red.

What this file imports — and therefore what its statements are *about* — is the model itself
(`Word`, `Types`, `State`, `Instruction`, `FpOps`, `Step`), the environment layer `Env` (loader,
hosted run: not part of the architecture), plus the statement vocabulary of
`Semantics/Specs/Defs.lean` and `Semantics/Specs/WellFormed.lean`, and, for the last section (the
refinement of the manual specification, Wave 7D), the manual specification `Semantics/Manual/*`
and the refinement vocabulary `Semantics/Refine/Defs.lean` (`Refine.abs`, `Refine.Inv`; definitions
only). It imports no proof file.

**This is the only Lean file in the project that contains `sorry`.** It is deliberately *not*
imported by `Semantics.lean` or `Checked.lean`, so neither `lake build` of the libraries nor
`lake check` ever sees a `sorry`; `scripts/gate-allow.txt` allow-lists `sorry` for this one path in
the gate's forbidden-construct scan. See `docs/PROOF-NOTES.md`, "The comparator arrangement"
(which also explains why the theorems live in `namespace Trusted` and why a bridging solution
module is needed).

The surface is a deliberate selection: every global theorem (round trip, invariants, exception
entry, fetch/decode failure, delay slots, Coprocessor Unusable, FP trap, self-modifying code,
where the hosted environment differs from `step`) and at least one
per-instruction statement from each family. The remaining per-instruction statements have the
same shape and are in `Semantics/Specs/<Family>.lean`; all of them are kernel-replayed by
`lake check`.
-/

set_option maxRecDepth 4000

namespace Trusted

/-! ## Decode / encode

Proved in `Semantics/Specs/` — DecodeSpec.lean. -/

/-- Round trip: decoding the encoding of a well-formed instruction returns it.
Covers every constructor of `Instruction`. -/
theorem decode_encode (i : Instruction) (h : i.WellFormed) : decode (encode i) = some i := by
  sorry

/-! ## Global invariants

Proved in `Semantics/Specs/` — Invariants.lean, RegFileSize.lean. -/

/-- **Global invariant: `$zero` is never changed by a step.** Register `0` reads the same thing
after a step as before — for **every** state and instruction, with no side conditions
(INSTRUCTION-REF Global rule 2, "writes to `$zero` are a no-op"). -/
theorem step_preserves_zero_register (s : State) : readReg (step s) 0 = readReg s 0 := by
  sorry

/-- **Whole-run invariant: `$zero` is the same at the end of any bare run as at its start**, for
any start state and any number of steps. -/
theorem run_preserves_zero_register (s₀ : State) (n : Nat) :
    readReg (run s₀ n) 0 = readReg s₀ 0 := by
  sorry

/-- **`$zero` reads `0` at the end of every run started from `initialState`.** -/
theorem run_initialState_zero_register (pc : W32) (n : Nat) :
    readReg (run (initialState pc) n) 0 = 0#32 := by
  sorry

/-- **A write to `$zero` is never observable.** No matter what value gets
"written" to register `0`, reading it straight back always gives `0` —
exactly INSTRUCTION-REF Global rule 2, stated as a rejection of the bad
behavior "the write took effect". -/
theorem zero_write_not_observable (s : State) (v : W32) (hv : readReg s 0 ≠ v) :
    readReg (writeReg s 0 v) 0 ≠ v := by
  sorry

/-- **Well-formedness is preserved by `step`**: if both register files have 32 entries before a
step, they have 32 entries after it. This discharges the `hsize` / `hsize32` side conditions of
the per-instruction theorems along any execution that starts well-formed. -/
theorem step_preserves_wellFormed (s : State) (hwf : s.RegFilesWF) : (step s).RegFilesWF := by
  sorry

/-- **Every state reached by `run` from `initialState` is well-formed.** -/
theorem run_initialState_wellFormed (pc : W32) (n : Nat) :
    (run (initialState pc) n).RegFilesWF := by
  sorry

/-! ## Exception entry

Proved in `Semantics/Specs/` — Exception.lean. -/

/-- **What exception entry always does**, whatever `EXL`, the delay-slot
status and the coprocessor number `ce`: `PC ←` the general vector (`EBase`'s
base with offset `0x180` — `0x80000180` at reset — or `0xBFC00380` when
`Status.BEV = 1`); `Status.EXL ← 1` (no other `Status` bit changes); **the
pending branch is abandoned**; **`LLbit ← 0`** (MD00086 Rev 6.06 "SC",
programming notes: "Exceptions between the LL and SC cause SC to fail");
and nothing else outside `EPC`/`Cause` is touched — no general register,
`hi`/`lo`, memory, FP register, `FCSR`, `BadVAddr`, `ErrorEPC`,
`EBase` or the LL address. -/
theorem exceptionEntry_always (s : State) (code ce : W32) :
    (exceptionEntry s code ce).pc =
        (if s.cp0Status &&& statusBevMask == 0#32 then
          ((s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32) ||| 0x180#32
         else 0xBFC00380#32) ∧
      (exceptionEntry s code ce).cp0Status = s.cp0Status ||| statusExlMask ∧
      (exceptionEntry s code ce).pendingBranch = none ∧
      (exceptionEntry s code ce).regs = s.regs ∧
      (exceptionEntry s code ce).hi = s.hi ∧ (exceptionEntry s code ce).lo = s.lo ∧
      (exceptionEntry s code ce).physMem = s.physMem ∧
      (exceptionEntry s code ce).fpRegs = s.fpRegs ∧
      (exceptionEntry s code ce).fcsr = s.fcsr ∧
      (exceptionEntry s code ce).llBit = false ∧
      (exceptionEntry s code ce).cp0BadVAddr = s.cp0BadVAddr ∧
      (exceptionEntry s code ce).cp0ErrorEpc = s.cp0ErrorEpc ∧
      (exceptionEntry s code ce).cp0EBase = s.cp0EBase ∧
      (exceptionEntry s code ce).llAddr = s.llAddr := by
  sorry

/-- **`EXL = 0`, not in a delay slot**: `EPC ← PC` (the faulting
instruction), `Cause.BD ← 0`, `Cause.ExcCode ← code`, `Cause.CE ← ce`. -/
theorem exceptionEntry_exl0_not_in_delay_slot (s : State) (code ce : W32)
    (hexl : s.cp0Status &&& statusExlMask = 0#32) (hpb : s.pendingBranch = none) :
    (exceptionEntry s code ce).cp0Epc = s.pc ∧
      (exceptionEntry s code ce).cp0Cause =
        (((s.cp0Cause &&& ~~~causeBdMask) &&& ~~~(causeExcCodeMask ||| causeCeMask))
          ||| ((code <<< 2) &&& causeExcCodeMask)) ||| ((ce <<< 28) &&& causeCeMask) := by
  sorry

/-- **`EXL = 0`, in a branch delay slot** (after a taken *or* not-taken
branch — `pendingBranch = some t` either way): `EPC ← PC − 4` (the branch),
`Cause.BD ← 1`, `Cause.ExcCode ← code`, `Cause.CE ← ce`. -/
theorem exceptionEntry_exl0_in_delay_slot (s : State) (code ce t : W32)
    (hexl : s.cp0Status &&& statusExlMask = 0#32) (hpb : s.pendingBranch = some t) :
    (exceptionEntry s code ce).cp0Epc = s.pc - 4#32 ∧
      (exceptionEntry s code ce).cp0Cause =
        (((s.cp0Cause ||| causeBdMask) &&& ~~~(causeExcCodeMask ||| causeCeMask))
          ||| ((code <<< 2) &&& causeExcCodeMask)) ||| ((ce <<< 28) &&& causeCeMask) := by
  sorry

/-- **`EXL = 1`** (an exception inside an exception handler), in a delay
slot or not: `EPC` is left unchanged and so is `Cause.BD`; only
`Cause.ExcCode ← code` and `Cause.CE ← ce`. -/
theorem exceptionEntry_exl1 (s : State) (code ce : W32)
    (hexl : s.cp0Status &&& statusExlMask ≠ 0#32) :
    (exceptionEntry s code ce).cp0Epc = s.cp0Epc ∧
      (exceptionEntry s code ce).cp0Cause =
        ((s.cp0Cause &&& ~~~(causeExcCodeMask ||| causeCeMask))
          ||| ((code <<< 2) &&& causeExcCodeMask)) ||| ((ce <<< 28) &&& causeCeMask) := by
  sorry

/-- **After exception entry, `Cause.ExcCode` (bits 6..2) is `code`** (its
low five bits), in every case. -/
theorem exceptionEntry_excCode (s : State) (code ce : W32) :
    causeExcCode (exceptionEntry s code ce) = code &&& 31#32 := by
  sorry

/-! ## Fetch and decode failures

Proved in `Semantics/Specs/` — Fetch.lean. -/

/-- **A misaligned `pc` raises Address Error (AdEL)** with `BadVAddr = pc`
(and `EPC = pc`, by `exceptionEntry_*`). -/
theorem step_misaligned_pc (s : State) (h : s.pc.toNat % 4 ≠ 0) (hexec : executesInstr s = true) :
    step s = timerTick (takeAddressException s excCodeAdEL s.pc) := by
  sorry

/-- **`step` executes the word in memory at `pc`**: if the big-endian word at `pc` decodes to
`instr`, the step is `execInstr s instr`. There is no "no instruction" case in the processor:
memory that was never written reads as 0 (`sll $0, $0, 0`). -/
theorem step_fetches_from_memory (s : State) (w : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr) (hexec : executesInstr s = true) :
    step s = timerTick (execInstr s instr) := by
  sorry

/-- **A word that does not decode** raises Reserved Instruction (ExcCode
10) — unless it lies in a coprocessor's encoding space and that coprocessor
is unusable, in which case Coprocessor Unusable takes precedence (MD00090
Vol III Rev 6.02 §6.2.21, p.99; Table 6.6, p.83): coprocessor 0 (`isCop0Word`:
COP0 or CACHE) when coprocessor 0 is not usable (`cp0Usable`: not Kernel Mode
and `Status.CU0 = 0`), with `Cause.CE = 0`; coprocessor 1 (`isCop1Word`) when
`Status.CU1 = 0`, with `Cause.CE = 1`; coprocessor 2 (`isCop2Word`), which
the model does not have, always, with `Cause.CE = 2`. -/
theorem step_undecodable (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if isCop0Word w && !cp0Usable s then (exceptionEntry s excCodeCpU 0#32)
      else if isCop1Word w && !cu1Enabled s then (exceptionEntry s excCodeCpU 1#32)
      else if isCop2Word w then (exceptionEntry s excCodeCpU 2#32)
      else takeException s excCodeRI) := by
  sorry

/-- **A word that does not decode and is in no unusable coprocessor's encoding space
raises Reserved Instruction** (ExcCode 10): not a COP1/COP2 word, and either not a COP0/CACHE
word or coprocessor 0 is usable (Kernel Mode, or `Status.CU0 = 1`). -/
theorem step_reserved_instruction (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = none)
    (hc0 : isCop0Word w = false ∨ cp0Usable s = true)
    (hc1 : isCop1Word w = false) (hc2 : isCop2Word w = false) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeRI) := by
  sorry

/-- **A COP0 or CACHE word that does not decode, executed when coprocessor 0 is not usable,
raises Coprocessor Unusable with `Cause.CE = 0`**, not Reserved Instruction (MD00090 Vol III
Rev 6.02 §6.2.21, p.99; §6.2.22, p.100). Covers the unimplemented COP0 instructions (TLB
instructions, DERET, reserved encodings) and CACHE. -/
theorem step_reserved_cop0_unusable (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = none)
    (hc0 : isCop0Word w = true) (hcu : cp0Usable s = false) (hexec : executesInstr s = true) :
    step s = timerTick (takeCop0Unusable s) := by
  sorry

/-! ## Delay slots

Proved in `Semantics/Specs/` — DelaySlot.lean. -/

/-- **The general delay-slot theorem, for `step`.** If the instruction at
`pc` is not a control transfer and, executed outside a delay slot, it
completes normally with result `s'`, then executed in a delay slot with
pending branch target `t` it produces `{ s' with pc := t }`: **the
resulting `pc` is `t`, and every other effect is identical.** This lifts
every `hpb : s.pendingBranch = none` theorem in this file to the
delay-slot case. -/
theorem delay_slot_commits_target (s : State) (t w : W32) (instr : Instruction)
    (s' : State)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr)
    (hnb : isBranchLike instr = false) (hvec : s.pc + 4#32 ≠ exceptionVector s)
    (h0 : step { s with pendingBranch := none } = s')
    (hnormal : s'.pc = s.pc + 4#32) (hexec : executesInstr s = true) :
    step { s with pendingBranch := some t } = { s' with pc := t } := by
  sorry

/-- **A control transfer in a branch delay slot raises Reserved Instruction** (pin). The
architecture makes a branch, jump, `eret` or `wait` in a delay slot UNPREDICTABLE (pre-Release-6
branches/jumps: MD00086 Vol II-A Rev 6.06, BEQ, p.72) or UNDEFINED (ERET, p.177; WAIT, p.442),
and "UNPREDICTABLE operations may cause arbitrary exceptions" (§1.2.1, p.3); Release 6 requires
exactly this exception (MD00082 Vol I-A Rev 6.01 §5.3.2.1, p.62). Whenever the instruction about
to execute is in a delay slot (`s.pendingBranch = some _`) and is one of the 26 instructions of
`isBranchLike`, `step` takes Reserved Instruction from the delay slot. -/
theorem branch_in_delay_slot_reserved_instruction (s : State) (w : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr)
    (hpb : s.pendingBranch.isSome = true) (hbr : isBranchLikeSpec instr = true) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeRI) := by
  sorry

/-! ## R-type arithmetic

Proved in `Semantics/Specs/` — Arith.lean. -/

/-- **`add` computes the exact sum, or traps exactly on signed overflow.**
This is `step`'s own code, restated with public names: the raw sum is
formed, `addOverflowsSpec` is INSTRUCTION-REF's Java-derived overflow test
("add" section), and the instruction either raises
Integer Overflow (`takeException s excCodeOv`) or writes the sum and advances the program counter by
4. Every other `add`-related theorem is a corollary of this one. -/
theorem add_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.add rs rt rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let av := readReg s (regIdxSpec rs)
      let bv := readReg s (regIdxSpec rt)
      let sumBV := av + bv
      if addOverflowsSpec (asSigned av) (asSigned bv) (asSigned sumBV) then
        takeException s excCodeOv
      else
        { (writeReg s (regIdxSpec rd) sumBV) with
            pc := (writeReg s (regIdxSpec rd) sumBV).pc + 4#32 }) := by
  sorry

/-- **`sub` computes the exact difference, or traps exactly on signed
overflow.** Mirrors `add_spec_raw`; `subOverflowsSpec` is INSTRUCTION-REF's
"sub" overflow test. -/
theorem sub_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sub rs rt rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let av := readReg s (regIdxSpec rs)
      let bv := readReg s (regIdxSpec rt)
      let diffBV := av - bv
      if subOverflowsSpec (asSigned av) (asSigned bv) (asSigned diffBV) then
        takeException s excCodeOv
      else
        { (writeReg s (regIdxSpec rd) diffBV) with
            pc := (writeReg s (regIdxSpec rd) diffBV).pc + 4#32 }) := by
  sorry

/-- **`add` overflow raises Integer Overflow (ExcCode 12), in or out of a
delay slot** — no `pendingBranch` hypothesis. `$rd` is not written
(`exceptionEntry_always`: exception entry changes no general register);
`EPC`/`Cause.BD` follow `exceptionEntry_*`. -/
theorem add_overflow_raises_ov (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.add rs rt rd))
    (hov : addOverflowsSpec (asSigned (readReg s (regIdxSpec rs))) (asSigned (readReg s (regIdxSpec rt)))
      (asSigned (readReg s (regIdxSpec rs) + readReg s (regIdxSpec rt))) = true) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeOv) := by
  sorry

/-- **Overflow does not silently wrap.** A buggy `add` might wrap
`0x7fffffff + 1` to `0x80000000`, write it to `$10` and continue; the real
`add` raises the Integer Overflow exception (ExcCode 12) instead: the step
is exactly exception entry, and exception entry changes no general
register — in particular the destination `$10` is not written. -/
theorem add_overflow_not_wrapped (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.add 8#32 9#32 10#32))
    (hpb : s.pendingBranch = none)
    (ha : readReg s (regIdxSpec 8#32) = 0x7fffffff#32)
    (hb : readReg s (regIdxSpec 9#32) = 1#32) (hexec : executesInstr s = true) :
    step s = timerTick (exceptionEntry s excCodeOv) ∧
      (exceptionEntry s excCodeOv).regs = s.regs := by
  sorry

/-! ## Immediates

Proved in `Semantics/Specs/` — Immediate.lean. -/

/-- **`addi` computes `$rs + sext16(imm)` exactly, or traps exactly on
signed overflow.** The immediate is sign-extended first (INSTRUCTION-REF
"addi" section), then the same overflow test as `add` applies. -/
theorem addi_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addi rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let av := readReg s (regIdxSpec rs)
      let bv := signExt16 imm
      let sumBV := av + bv
      if addOverflowsSpec (asSigned av) (asSigned bv) (asSigned sumBV) then
        takeException s excCodeOv
      else
        { (writeReg s (regIdxSpec rt) sumBV) with
            pc := (writeReg s (regIdxSpec rt) sumBV).pc + 4#32 }) := by
  sorry

/-- **`addi` overflow raises Integer Overflow**, in or out of a delay slot. -/
theorem addi_overflow_raises_ov (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addi rs rt imm))
    (hov : addOverflowsSpec (asSigned (readReg s (regIdxSpec rs))) (asSigned (signExt16 imm))
      (asSigned (readReg s (regIdxSpec rs) + signExt16 imm)) = true) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeOv) := by
  sorry

/-! ## Shifts

Proved in `Semantics/Specs/` — Shift.lean. -/

/-- **`sll` shifts `$rt` left by the fixed `shamt` field, zero-filling the
vacated low bits.** `shamt` comes straight from the instruction encoding
(INSTRUCTION-REF "sll"), not a register. -/
theorem sll_spec_raw (s : State) (w rd rt shamt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sll rd rt shamt))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< shamt.toNat)) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< shamt.toNat)).pc + 4#32 }) := by
  sorry

/-! ## Multiply / divide

Proved in `Semantics/Specs/` — MulDiv.lean. -/

/-- **`mult` forms the exact signed 64-bit product of `$rs` and `$rt`,
splitting it into `hi`/`lo`.** No GPR is written, and `mult` raises no exception
(INSTRUCTION-REF "mult" section: MARS never traps on multiply overflow —
the full 64-bit result always fits in `hi:lo`). -/
theorem mult_spec_raw (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mult rs rt))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
      { s with lo := prod64.extractLsb 31 0, hi := prod64.extractLsb 63 32, pc := s.pc + 4#32 }) := by
  sorry

/-- **`div` by a nonzero divisor truncates toward zero; the remainder takes
the dividend's sign** (Lean's `Int.tdiv`/`Int.tmod`, matching Java's `/`/`%`
used by MARS — INSTRUCTION-REF "div" section). **`div` by zero leaves `hi`
and `lo` untouched and raises no exception** (SPEC-NOTES §9.2 / INSTRUCTION-REF
"div" MARS-note: this is a deliberate MIPS32-spec reading, not a MARS bug).
Both cases always advance the program counter by 4. -/
theorem div_spec_raw (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.div rs rt))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      if b == 0 then
        { s with pc := s.pc + 4#32 }
      else
        { s with lo := ofInt32 (a.tdiv b), hi := ofInt32 (a.tmod b), pc := s.pc + 4#32 }) := by
  sorry

/-- Corollary of `div_spec_raw`: dividing by `0` leaves `hi`/`lo` exactly as
they were and raises no exception — INSTRUCTION-REF "div" MARS-note, SPEC-NOTES
§9.2. -/
theorem div_by_zero_spec (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.div rs rt))
    (hpb : s.pendingBranch = none)
    (hzero : readReg s (regIdxSpec rt) = 0#32) (hexec : executesInstr s = true) :
    step s = timerTick ({ s with pc := s.pc + 4#32 }) := by
  sorry

/-! ## Bit operations

Proved in `Semantics/Specs/` — BitOps.lean. -/

/-- **`ext` extracts a `size`-bit field of `$rs` starting at bit `pos`,
zero-extended, into `$rt`** (SPECIAL3 opcode 0x1f, funct 0x00;
INSTRUCTION-REF "ext"). `pos`/`size` are already the semantic values here —
`decode` did the raw-field +-1 arithmetic — so this is pure bit masking,
with no special case for the real `pos + size <= 32` hardware constraint
(matching `Step.lean`'s own documented choice). -/
theorem ext_spec_raw (s : State) (w rt rs pos size : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ext rt rs pos size))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let field := (readReg s (regIdxSpec rs) >>> pos.toNat) &&& lowBitsMaskSpec size.toNat
      { (writeReg s (regIdxSpec rt) field) with
          pc := (writeReg s (regIdxSpec rt) field).pc + 4#32 }) := by
  sorry

/-! ## Loads and stores

Proved in `Semantics/Specs/` — Memory.lean, Atomic.lean, Unaligned.lean. -/

/-- **`lw` composes a big-endian word from memory at `$rs + sext16(offset)`,
or raises Address Error on a misaligned effective address**
(INSTRUCTION-REF "lw" section; SPEC-NOTES §9.3 — the offset is
sign-extended, unlike MARS's own latent zero-extension bug for raw-decoded
binaries). -/
theorem lw_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v =>
        { (writeReg s (regIdxSpec rt) v) with
            pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }) := by
  sorry

/-- Corollary of `lw_spec_raw`: a misaligned effective address raises Address
Error, naming that exact address. -/
theorem lw_misaligned_spec (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none)
    (hmisaligned : (readReg s (regIdxSpec rs) + signExt16 imm).toNat % 4 ≠ 0) (hexec : executesInstr s = true) :
    step s = timerTick (takeAddressException s excCodeAdEL (readReg s (regIdxSpec rs) + signExt16 imm)) := by
  sorry

/-- **`sw` stores `$rt` as a big-endian word at `$rs + sext16(offset)` and
clears `llBit`** (any store invalidates a pending `ll`/`sc` pair, so a
subsequent `sc` correctly fails if memory changed underneath it), or raises
Address Error on a misaligned effective address (INSTRUCTION-REF "sw"
section). -/
theorem sw_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemWord s addr (readReg s (regIdxSpec rt)) with
      | none => takeAddressException s excCodeAdES addr
      | some s' =>
        { ({ s' with llBit := false }) with
            pc := ({ s' with llBit := false }).pc + 4#32 }) := by
  sorry

/-- **`sb` stores the low byte of `$rt` at `$rs + sext16(offset)` and
clears `llBit`** (MD00086 "SB": `StoreMemory(BYTE, GPR[rt] 7..0)`). There is
no alignment requirement; the effective address is translated by the MMU (`translate`): a
kernel address from User Mode raises Address Error (AdES, `BadVAddr` = the address, MD00090
Vol III Rev 6.02 Table 4.2, p.30) and stores nothing; otherwise exactly one byte of physical
memory changes, at the translated address. Clearing `llBit` is the model's pinned choice for
every store (see `State.llBit`). -/
theorem sb_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sb rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      match translate s (readReg s (regIdxSpec rs) + signExt16 imm) with
      | none => takeAddressException s excCodeAdES (readReg s (regIdxSpec rs) + signExt16 imm)
      | some pa =>
        { s with
              physMem := s.physMem.insert pa (readReg s (regIdxSpec rt) &&& 0xff#32).toNat.toUInt8
              llBit := false
              pc := s.pc + 4#32 }) := by
  sorry

/-- **`ll` loads a word exactly like `lw`, and additionally sets `llBit`
and records its effective address in `llAddr`** — the link state that a
later `sc` checks (INSTRUCTION-REF "ll" section; MD00086 Vol II-A Rev 6.06,
LL, p.223-224). It raises Address Error on a word-misaligned effective
address, exactly like `lw`. -/
theorem ll_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ll rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v =>
        { ({ (writeReg s (regIdxSpec rt) v) with llBit := true, llAddr := addr }) with
            pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }) := by
  sorry

/-- **`sc` is conditional on `llBit` and on its address matching the
preceding `ll`'s, checked before `llBit` is cleared.** The effective address
is computed and alignment-checked unconditionally, just like `sw` (so a
misaligned `sc` raises Address Error regardless of `llBit`). Once the
address is valid: if `s.llBit` was `true` **and** the address equals
`s.llAddr` in bits 31..2, the aligned word ("An SC will fail if the aligned address of the SC does not match
that of the preceding LL" — MD00086 Vol II-A Rev 6.06, SC, p.347), the store
commits (`$rt`'s old value is written to memory) and `$rt` is overwritten
with `1` (success); otherwise the store does **not** commit and `$rt` is
overwritten with `0` (failure). Either way `llBit`
ends up `false`. This single theorem states both outcomes together
(mirroring how `beq_spec_raw` states taken/not-taken as one `if`), because
the whole point of `ll`/`sc` is this exact atomic-primitive contract, not
just "some memory operation happened" (INSTRUCTION-REF "sc" section). -/
theorem sc_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sc rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemWord s addr (readReg s (regIdxSpec rt)) with
      | none => takeAddressException s excCodeAdES addr
      | some stored =>
        if s.llBit && s.llAddr >>> 2 == addr >>> 2 then
          { ({ (writeReg stored (regIdxSpec rt) 1#32) with llBit := false }) with
              pc := ({ (writeReg stored (regIdxSpec rt) 1#32) with llBit := false }).pc + 4#32 }
        else
          { ({ (writeReg s (regIdxSpec rt) 0#32) with llBit := false }) with
              pc := ({ (writeReg s (regIdxSpec rt) 0#32) with llBit := false }).pc + 4#32 }) := by
  sorry

/-- **`lwl` ("load word left") merges 1–4 most-significant bytes starting at
`$rs + sext16(offset)` into the most-significant end of `$rt`, leaving
`$rt`'s existing least-significant bytes untouched** — exactly how many
bytes merge depends on `addr.toNat % 4` (4 at `off = 0`, behaving exactly
like a plain `lw`; down to 1 at `off = 3`). Raises no exception on a misaligned
address, unlike `lw` (INSTRUCTION-REF `lwl` section); the only exception is the MMU's Address
Error (AdEL, `BadVAddr = addr`) for a kernel address referenced from User Mode (MD00090 Vol III
Rev 6.02 Table 4.2, p.30). -/
theorem lwl_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lwl rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemByte s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some b0 =>
        let off := addr.toNat % 4
        let old := readReg s (regIdxSpec rt)
        let v :=
          match off with
          | 0 =>
            let b1 := (readMemByte s (addr + 1#32)).getD 0
            let b2 := (readMemByte s (addr + 2#32)).getD 0
            let b3 := (readMemByte s (addr + 3#32)).getD 0
            setByteSlotSpec (setByteSlotSpec (setByteSlotSpec (setByteSlotSpec old 0 b0) 1 b1) 2 b2) 3 b3
          | 1 =>
            let b1 := (readMemByte s (addr + 1#32)).getD 0
            let b2 := (readMemByte s (addr + 2#32)).getD 0
            setByteSlotSpec (setByteSlotSpec (setByteSlotSpec old 0 b0) 1 b1) 2 b2
          | 2 =>
            let b1 := (readMemByte s (addr + 1#32)).getD 0
            setByteSlotSpec (setByteSlotSpec old 0 b0) 1 b1
          | _ =>  -- off = 3 (Nat match needs a default; addr.toNat % 4 is always < 4)
            setByteSlotSpec old 0 b0
        { (writeReg s (regIdxSpec rt) v) with
            pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }) := by
  sorry

/-! ## Branches and jumps

Proved in `Semantics/Specs/` — Branch.lean, BranchLikely.lean, Jump.lean. -/

/-- **`beq`/`bne` branch target and condition, in one equation — real
MIPS32 one-delay-slot semantics.** Mirrors `step`'s own code: the
comparison `$rs == $rt` picks between an ordinary fallthrough to `PC_next`
and *scheduling* (not jumping to) `PC_next + (sext16(offset) << 2)` via
`pendingBranch`, with `beq` and `bne` using the comparison the opposite way
around. A taken branch never updates `pc` past `PC_next` in this same step
— the delay-slot instruction at `PC_next` always executes first; the
schedule is committed by the *next* step's `advance` (`Step.lean`), see
`beq_taken_delay_slot_lands_on_target` below for the two-step composition
(SPEC-NOTES §9 item 1; INSTRUCTION-REF Global rule 3 — this supersedes the
old no-delay-slot MARS-default behavior). The hypothesis `hpb` restricts
this equation to the ordinary case where `s` is not itself sitting in
another pending delay slot; see `branch_in_delay_slot_reserved_instruction` for that other
case. -/
theorem beq_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  sorry

/-- **`beq`, taken**: when `$rs = $rt`, `beq` schedules
`PC_next + (offset << 2)` as the pending delay-slot transfer and itself
falls through to `PC_next` — it does **not** jump immediately
(INSTRUCTION-REF Global rule 3: real MIPS32 always executes one delay-slot
instruction first). -/
theorem beq_taken_spec (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rs) = readReg s (regIdxSpec rt)) (hexec : executesInstr s = true) :
    step s = timerTick ({ s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }) := by
  sorry

/-- **`beql`/`bnel` step-level shape**: identical field layout and taken
condition to `beq` (`$rs == $rt`), but the not-taken case nullifies the delay
slot (`pc := pc + 4`, the slot marked `nullified`, consumed by the next step
without being fetched) instead of executing it (INSTRUCTION-REF "beql / bnel" section). -/
theorem beql_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beql rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32), nullified := true }) := by
  sorry

/-- **A not-taken `beql` nullifies its delay slot in the next instruction time**, whatever the
memory holds there (MD00086 Vol II-A Rev 6.06, BEQL p.73: "I+1: ... else
NullifyCurrentInstruction()"; §2.2.2.5.4 p.26): the first `step` marks the slot as nullified, and,
unless an interrupt is taken at the slot, the second reaches `pc + 8` with nothing executed and
nothing pending; the timer ticks once per step. -/
theorem beql_not_taken_squashes_delay_slot (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beql rs rt imm))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt)) (hexec : executesInstr s = true) :
    step s = timerTick
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32), nullified := true } ∧
      (interruptTaken (step s) = false →
        run s 2 = timerTick (timerTick { s with pc := s.pc + 8#32 })) := by
  sorry

/-- **The nullified instruction's own instruction time**: when the instruction at `pc` is nullified
(`nullified`, the delay slot of a not-taken branch-likely), no interrupt is taken and the processor
is not in standby, `step` neither fetches nor executes it and raises no exception
(NullifyCurrentInstruction, MD00086 Vol II-A Rev 6.06 §2.2.2.5.4, p.26): `pc ← pc + 4`, the delay
slot is over, and the timer advances. -/
theorem step_nullified (s : State) (hi : interruptTaken s = false) (hs : s.standby = false)
    (hn : s.nullified = true) :
    step s = timerTick { s with pc := s.pc + 4#32, pendingBranch := none, nullified := false } := by
  sorry

/-- **`j` unconditionally schedules a jump whose top 4 bits come from
`PC_next`, not from `j`'s own address** — the same pseudo-direct target
composition as `jal`, minus the link-register write (INSTRUCTION-REF "j"
section). Like every other jump/branch here, `j` itself falls through to
`PC_next` and never jumps in the same step; the delay-slot instruction
always executes first. -/
theorem j_spec_raw (s : State) (w target : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.j target))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let pcNext := s.pc + 4#32
      { s with pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) }) := by
  sorry

/-- **`jal` links `$ra` to `pc + 8` — past the delay slot, not `PC_next`
(`pc + 4`) — and schedules a jump to a target whose top 4 bits come from
`PC_next`, not from `jal`'s own address** (INSTRUCTION-REF Global rule 3:
real MIPS32's `jal` link value is the address of the instruction *after*
the delay slot, since the delay-slot instruction itself still executes
before control can return to `$ra`). Like `beq`/`bne`, `jal` schedules the
jump via `pendingBranch` and itself falls through to `PC_next`; it never
jumps in the same step. -/
theorem jal_spec_raw (s : State) (w target : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.jal target))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let pcNext := s.pc + 4#32
      { (writeReg s 31 (pcNext + 4#32)) with
          pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) }) := by
  sorry

/-- Corollary of `jal_spec_raw`: `$ra` (register 31) reads back exactly
`pc + 8`, i.e. the address of the instruction *after* the delay slot
(`jal`'s own address plus 8), not `pc + 4`. -/
theorem jal_sets_ra (s : State) (w target : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.jal target))
    (hpb : s.pendingBranch = none)
    (hsize32 : s.regs.size = 32) (hexec : executesInstr s = true) :
    ∃ s', step s = s' ∧ readReg s' (regIdxSpec 31#32) = s.pc + 8#32 := by
  sorry

/-- **`jalr` links `$rd` to `pc + 8` (the same `jal`/`jalr` link-value
convention — past the delay slot) and schedules a jump to the raw value
held in `$rs`, read *before* `$rd` is overwritten** — so `rd == rs`
aliasing is always safe (INSTRUCTION-REF "jalr" section). This is `step`'s
own code restated: the target expression reads `$rs` from the original `s`,
not from the just-written state, exactly matching the "If `rd == rs`..."
paragraph in the spec. -/
theorem jalr_spec_raw (s : State) (w rs rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.jalr rs rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let pcNext := s.pc + 4#32
      { (writeReg s (regIdxSpec rd) (pcNext + 4#32)) with
          pc := pcNext, pendingBranch := some (readReg s (regIdxSpec rs)) }) := by
  sorry

/-! ## Traps, `break`, `syscall`

Proved in `Semantics/Specs/` — Trap.lean, Syscall.lean. -/

/-- **`teq` traps iff `$rs == $rt`**, taking the shared coprocessor-0
exception with `excCode = excCodeTr`; otherwise it is a complete no-op
beyond the ordinary fallthrough to `pc + 4#32` — no CP0 state touched at
all (INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu" section). -/
theorem teq_spec_raw (s : State) (w rs rt code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.teq rs rt code))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        takeException s excCodeTr
      else
        { s with pc := s.pc + 4#32 }) := by
  sorry

/-- **`break` unconditionally raises the Breakpoint exception** (ExcCode
9) — in any state, in or out of a delay slot. What `takeException` does to
`EPC`/`Cause`/`Status`/`pc`/`pendingBranch` is stated once, in `Exception.lean`
(`exceptionEntry_*`) (INSTRUCTION-REF "break" section). -/
theorem break_spec_raw (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.break code)) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeBp) := by
  sorry

/-- **`syscall` raises the System Call exception (ExcCode 8)**, whatever `$v0` holds, in or out
of a delay slot: "A system call exception occurs, immediately and unconditionally transferring
control to the exception handler" (MD00086 Vol II-A Rev 6.06, SYSCALL, p.415). The MARS-style
services are the hosted environment's (`hostStep_syscall_spec`, `Specs/Hosted.lean`). -/
theorem syscall_spec_raw (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.syscall code)) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeSys) := by
  sorry

/-! ## Coprocessor 0

Proved in `Semantics/Specs/` — Cp0.lean. -/

/-- **`mfc0` reads a modeled CP0 register `(rd, sel)` into GPR `$rt`**:
`(7,0)` HWREna, `(8,0)` BadVAddr, `(9,0)` Count, `(11,0)` Compare, `(12,0)` Status,
`(12,1)` IntCtl (reads `0xE000_0000`: `IPTI = 7`, every other field 0, MD00090 Vol III Rev 6.02
Table 9.48, p.199-201), `(12,2)` SRSCtl (reads 0: `HSS = 0`, Table 9.49, p.203-204), `(13,0)` Cause, `(14,0)` EPC, `(15,0)` PRId, `(15,1)` EBase, `(16,0)` Config, `(16,1)` Config1
(reads `0x8000_0001`: `M = 1`, `FP = 1`, Table 9.65, p.237-240), `(16,2)` Config2 (reads `0x8000_0000`:
`M = 1`, no level 2/3 cache, §9.47, Table 9.66, p.241-243), `(16,3)` Config3 (reads 0: none of its
optional features, no Config4, §9.48, Table 9.67, p.245-251), `(30,0)` ErrorEPC. `Cause` reads the stored bits plus the hardware interrupt lines in `IP7..IP2` (`State.hwInt`) and the timer
request: `TI` (bit 30) and, merged
into it (`IntCtl.IPTI = 7` pin), `IP7` (bit 15) while a timer interrupt is pending (MD00090 Vol III
Rev 6.02 Table 9.52, p.209, 211; Table 6.2, p.73). The read happens before the step's timer tick, so
`Count` reads the value the step started with.
`decode` produces `mfc0` only for these; for any other pair (reachable only
through a hand-built `Instruction`) the step raises Reserved Instruction,
which is also what the undecodable word does. Coprocessor 0 must be usable
(`hcp0`: Kernel Mode or `Status.CU0 = 1`); otherwise see
`cp0_instruction_user_mode_unusable`. -/
theorem mfc0_spec_raw (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc0 rt rd sel))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      let read (v : W32) : State :=
        { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }
      match rd.toNat, sel.toNat with
      | 7, 0 => read s.cp0HWREna
      | 8, 0 => read s.cp0BadVAddr
      | 9, 0 => read s.cp0Count
      | 11, 0 => read s.cp0Compare
      | 12, 0 => read s.cp0Status
      | 12, 1 => read 0xE0000000#32
      | 12, 2 => read 0#32
      | 13, 0 => read (s.cp0Cause ||| (s.hwInt.setWidth 32 <<< 10) |||
          (if s.cp0TimerInt then causeTiMask ||| causeIp7Mask else 0#32))
      | 14, 0 => read s.cp0Epc
      | 15, 0 => read 0x00010000#32
      | 15, 1 => read ((s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32)
      | 16, 0 => read (0x80008580#32 ||| (s.cp0ConfigK23.setWidth 32 <<< 28) |||
          (s.cp0ConfigKU.setWidth 32 <<< 25) ||| s.cp0ConfigK0.setWidth 32)
      | 16, 1 => read 0x80000001#32
      | 16, 2 => read 0x80000000#32
      | 16, 3 => read 0#32
      | 30, 0 => read s.cp0ErrorEpc
      | _, _ => takeException s excCodeRI) := by
  sorry

/-- **`mtc0` writes GPR `$rt` into a modeled CP0 register, through that
register's write mask.** `Status` (12,0) keeps only `statusWriteMask` (IE,
EXL, ERL, UM, IM7..0, BEV, CU0, CU1; every other bit reads as zero). `Cause` (13,0)
changes only `causeWriteMask` (DC, IV, IP1..0) and keeps `BD`, `CE`,
`ExcCode` and everything else. `EPC` (14,0) and `ErrorEPC` (30,0) are fully
writable, and so is `Count` (9,0) (MD00090 Vol III Rev 6.02 §9.27, p.183). A write to `Compare`
(11,0) stores the value and clears the timer interrupt (`Cause.TI`; §9.30, p.187). `HWREna` (7,0)
keeps bits 3..0 (`hwrenaWriteMask`; Table 9.39, p.175). `EBase` (15,1) takes bits 29..12 of the
written value under the fixed bits 31..30 = `10`. `Config` (16,0) takes only `K23` (bits 30..28), `KU` (27..25) and `K0` (2..0)
(Read/Write: MD00090 Vol III Rev 6.02 Table 9.64, p.233-235; Table A.2, p.317);
`BadVAddr` (8,0), `PRId` (15,0), `Config1` (16,1), `Config2` (16,2: `TU`/`SU` not implemented, "read as
zero and be ignored on write", Table 9.66, p.241-242), `Config3` (16,3: "All fields in the Config3
register are read-only", §9.48, p.245), `IntCtl` (12,1: no writable field, `VS` "is
ignored on write" without VI/EIC, MD00090 Vol III Rev 6.02 Table 9.48, p.201) and `SRSCtl` (12,2: with
`HSS = 0` its fields can only hold 0, Table 9.49, p.203-204; pin) are read-only: the write is ignored. Any other pair
raises Reserved Instruction, as for `mfc0_spec_raw`. Coprocessor 0 must be
usable (`hcp0`). -/
theorem mtc0_spec_raw (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt rd sel))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      match rd.toNat, sel.toNat with
      | 7, 0 =>
        { s with cp0HWREna := readReg s (regIdxSpec rt) &&& hwrenaWriteMask, pc := s.pc + 4#32 }
      | 8, 0 => { s with pc := s.pc + 4#32 }
      | 9, 0 => { s with cp0Count := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | 11, 0 =>
        { s with cp0Compare := readReg s (regIdxSpec rt), cp0TimerInt := false, pc := s.pc + 4#32 }
      | 12, 0 =>
        { s with cp0Status := readReg s (regIdxSpec rt) &&& statusWriteMask, pc := s.pc + 4#32 }
      | 12, 1 => { s with pc := s.pc + 4#32 }
      | 12, 2 => { s with pc := s.pc + 4#32 }
      | 13, 0 =>
        { s with
              cp0Cause := (s.cp0Cause &&& ~~~causeWriteMask) |||
                (readReg s (regIdxSpec rt) &&& causeWriteMask)
              pc := s.pc + 4#32 }
      | 14, 0 => { s with cp0Epc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | 15, 0 => { s with pc := s.pc + 4#32 }
      | 15, 1 =>
        { s with
              cp0EBase := (readReg s (regIdxSpec rt) &&& 0x3ffff000#32) ||| 0x80000000#32
              pc := s.pc + 4#32 }
      | 16, 0 =>
        { s with
              cp0ConfigK0 := (readReg s (regIdxSpec rt)).setWidth 3
              cp0ConfigK23 := (readReg s (regIdxSpec rt) >>> 28).setWidth 3
              cp0ConfigKU := (readReg s (regIdxSpec rt) >>> 25).setWidth 3
              pc := s.pc + 4#32 }
      | 16, 1 => { s with pc := s.pc + 4#32 }
      | 16, 2 => { s with pc := s.pc + 4#32 }
      | 16, 3 => { s with pc := s.pc + 4#32 }
      | 30, 0 =>
        { s with cp0ErrorEpc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | _, _ => takeException s excCodeRI) := by
  sorry

/-- **`eret`** (MD00086 "ERET"), executed outside a delay slot:
`if Status.ERL = 1 then PC ← ErrorEPC, ERL ← 0 else PC ← EPC, EXL ← 0`,
and **always `LLbit ← 0`**. It has no delay slot of its own: `pc` is set in
this very step. Coprocessor 0 must be usable (`hcp0`). -/
theorem eret_spec_raw (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      if s.cp0Status &&& statusErlMask != 0#32 then
        { s with pc := s.cp0ErrorEpc, cp0Status := s.cp0Status &&& ~~~statusErlMask, llBit := false }
      else
        { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask, llBit := false }) := by
  sorry


/-! ## Operating modes and reset

Proved in `Semantics/Specs/` — Cp0.lean, Mode.lean, Reset.lean. -/

/-- **Every coprocessor-0 instruction executed outside Kernel Mode with `Status.CU0 = 0` raises
Coprocessor Unusable with `Cause.CE = 0`, and does nothing else.** `usesCop0`: `mfc0`, `mtc0`,
`di`, `ei`, `eret`, `wait` (MD00086 Vol II-A Rev 6.06: MFC0 p.266, MTC0 p.291, DI p.164, EI
p.176, ERET p.178, WAIT p.443, "Exceptions: Coprocessor Unusable"); the rule is MD00090 Vol III
Rev 6.02 §6.2.22, p.100 ("A COP0 or Cache instruction was executed while the processor was running
in a mode other than Debug Mode or Kernel Mode, and the CU0 bit in the Status register was a
zero"). `hnb` excludes `eret`/`wait` in a delay slot (UNDEFINED; pinned to Reserved Instruction,
`branch_in_delay_slot_reserved_instruction`). -/
theorem cp0_instruction_user_mode_unusable (s : State) (w : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr)
    (huses : usesCop0 instr = true)
    (hnb : isBranchLike instr = false ∨ s.pendingBranch = none)
    (hcu : cp0Usable s = false) (hexec : executesInstr s = true) :
    step s = timerTick (exceptionEntry s excCodeCpU 0#32) := by
  sorry

/-- **Coprocessor 0 is unusable exactly in User Mode with `Status.CU0 = 0`** (MD00090 Vol III
Rev 6.02 §3.5.3, p.23). -/
theorem cp0Usable_false_iff (s : State) :
    cp0Usable s = false ↔ (userMode s = true ∧ s.cp0Status &&& statusCu0Mask = 0#32) := by
  sorry

/-- **User Mode** is `Status.UM = 1`, `Status.EXL = 0`, `Status.ERL = 0` (MD00090 Vol III
Rev 6.02 §3.4, p.22; Supervisor Mode is not implemented, so `KSU = UM ‖ 0`, Table 9.47 p.195);
Kernel Mode is every other state (§3.2, p.21). -/
theorem userMode_iff (s : State) :
    userMode s = true ↔
      (s.cp0Status &&& statusUmMask ≠ 0#32 ∧ s.cp0Status &&& statusExlMask = 0#32 ∧
        s.cp0Status &&& statusErlMask = 0#32) := by
  sorry

/-- **An exception taken from User Mode enters Kernel Mode**, with `Status.EXL = 1` and
`Status.UM` still 1 (MD00090 Vol III Rev 6.02 §3.2, p.21; §6.2.3, p.86-88). -/
theorem exception_from_user_mode_enters_kernel_mode (s : State) (code ce : W32)
    (hu : userMode s = true) :
    kernelMode (exceptionEntry s code ce) = true ∧ userMode (exceptionEntry s code ce) = false ∧
      (exceptionEntry s code ce).cp0Status &&& statusUmMask ≠ 0#32 ∧
      (exceptionEntry s code ce).cp0Status &&& statusExlMask = statusExlMask := by
  sorry

/-- **Exception entry always enters Kernel Mode** (it sets `Status.EXL`). -/
theorem exceptionEntry_enters_kernel_mode (s : State) (code ce : W32) :
    kernelMode (exceptionEntry s code ce) = true := by
  sorry

/-- **`eret` returns to User Mode** at `EPC` when `Status.ERL = 0`, `Status.EXL = 1` and
`Status.UM = 1` (MD00086 Vol II-A Rev 6.06, ERET, p.177). -/
theorem eret_to_user_mode (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none)
    (herl : s.cp0Status &&& statusErlMask = 0#32) (hexl : s.cp0Status &&& statusExlMask ≠ 0#32)
    (hum : s.cp0Status &&& statusUmMask ≠ 0#32) (hexec : executesInstr s = true) :
    (step s).pc = s.cp0Epc ∧ userMode (step s) = true := by
  sorry

/-- **What the Reset exception defines** (MD00090 Vol III Rev 6.02 §6.2.5, p.89-90), from any
state: `PC ← 0xBFC0_0000`, `Status.BEV ← 1`, `Status.ERL ← 1` (Kernel Mode, bootstrap vectors),
`Cause.DC ← 0`, `EBase` reads `0x8000_0000`, `Config` reads `0xA400_8582` (`MT = 3` Fixed Mapping,
`K23 = KU = K0 = 2`),
`ErrorEPC ←` the restart PC, no branch pending. -/
theorem resetException_spec (s : State) :
    (resetException s).pc = 0xBFC00000#32 ∧
    (resetException s).cp0Status &&& statusBevMask = statusBevMask ∧
    (resetException s).cp0Status &&& statusErlMask = statusErlMask ∧
    (resetException s).cp0Cause &&& causeDcMask = 0#32 ∧
    ebaseValue (resetException s) = 0x80000000#32 ∧
    configValue (resetException s) = 0xA4008582#32 ∧
    (resetException s).cp0ErrorEpc = (if s.pendingBranch.isSome then s.pc - 4#32 else s.pc) ∧
    (resetException s).pendingBranch = none ∧
    kernelMode (resetException s) = true ∧
    exceptionVector (resetException s) = 0xBFC00380#32 := by
  sorry

/-- **The state after a cold reset** (`resetState = resetException powerOnState`; the registers
whose reset state is undefined are pinned to 0 by `powerOnState`). -/
theorem resetState_spec :
    resetState.pc = 0xBFC00000#32 ∧ resetState.cp0Status = 0x00400004#32 ∧
    resetState.cp0Cause = 0#32 ∧ resetState.cp0Epc = 0#32 ∧ resetState.cp0BadVAddr = 0#32 ∧
    resetState.cp0ErrorEpc = 0#32 ∧ ebaseValue resetState = 0x80000000#32 ∧
    configValue resetState = 0xA4008582#32 ∧ kernelMode resetState = true ∧
    exceptionVector resetState = 0xBFC00380#32 ∧ resetState.pendingBranch = none ∧
    resetState.llBit = false ∧ resetState.regs = Array.replicate 32 0#32 ∧
    resetState.hi = 0#32 ∧ resetState.lo = 0#32 ∧
    resetState.fpRegs = Array.replicate 32 0#32 ∧ resetState.fcsr = 0#32 ∧
    resetState.cp0Count = 0#32 ∧ resetState.cp0Compare = 0#32 ∧ resetState.cp0TimerInt = false ∧
    resetState.cp0HWREna = 0#32 := by
  sorry

/-- **The hosted start state is the reset state followed by the environment's boot convention**
(`Env.lean`, `bootConvention`: `Status ← CU1`, `$sp ← spInit`, `pc ← textBase`), and it equals
`initialState textBase`. -/
theorem hostedStart_is_reset_then_boot :
    hostedStart = bootConvention textBase resetState ∧ hostedStart = initialState textBase := by
  sorry

/-! ## Timer (Count / Compare / Cause.TI) and hardware registers (`rdhwr`, `HWREna`)

Proved in `Semantics/Specs/` — Timer.lean. -/

/-- **`Count` advances by one on every step** (pin of the implementation-dependent rate, MD00090
Vol III Rev 6.02 §9.27, p.183: "incrementing at a constant rate, whether or not an instruction is
executed"), when counting is enabled (`Cause.DC = 0`, Table 9.52, p.210) and the instruction at
`pc` does not itself write `Count`, `Compare` or `Cause`. Whatever else the step does — an ordinary
instruction, a branch, any exception, a fetch that fails — `Count` goes from `c` to `c + 1`
(modulo 2^32). -/
theorem step_count_advances (s : State) (hdc : countEnabled s = true)
    (hw : fetchesTimerWrite s = false) :
    (step s).cp0Count = s.cp0Count + 1#32 := by
  sorry

/-- **With `Cause.DC = 1`, `Count` does not move** ("Disable counting of Count register", MD00090
Vol III Rev 6.02 Table 9.52, p.210), unless the instruction writes `Count`, `Compare` or `Cause`. -/
theorem step_count_stopped (s : State) (hdc : countEnabled s = false)
    (hw : fetchesTimerWrite s = false) :
    (step s).cp0Count = s.cp0Count := by
  sorry

/-- **`Count = Compare` sets `Cause.TI`**, after every step, from every state: "When the value of
the Count register equals the value of the Compare register, an interrupt request is made" (MD00090
Vol III Rev 6.02 §9.30, p.187), visible in `Cause.TI` (Table 9.52, p.209). -/
theorem step_timer_match_sets_ti (s : State) (h : (step s).cp0Count = (step s).cp0Compare) :
    (step s).cp0TimerInt = true := by
  sorry

/-- **`Cause.TI` after a step** that does not write `Count`, `Compare` or `Cause`: it stays set
if it was set, and becomes set exactly when the new `Count` equals `Compare`; `Compare` does not
change ("maintains a stable value and does not change on its own", MD00090 Vol III Rev 6.02 §9.30,
p.187). -/
theorem step_timerInt (s : State) (hw : fetchesTimerWrite s = false) :
    (step s).cp0TimerInt = (s.cp0TimerInt || (step s).cp0Count == s.cp0Compare) ∧
      (step s).cp0Compare = s.cp0Compare := by
  sorry

/-- **`mtc0 $rt, $9` (`Count`)**: the written value is what the timer advances from ("The Count
register can be written for functional or diagnostic purposes", MD00090 Vol III Rev 6.02 §9.27,
p.183): after the step `Count` is `$rt + 1`, or `$rt` with `Cause.DC = 1`. -/
theorem mtc0_count_spec (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt 9#32 0#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    (step s).cp0Count =
      if countEnabled s then readReg s (regIdxSpec rt) + 1#32 else readReg s (regIdxSpec rt) := by
  sorry

/-- **A write to `Compare` clears the timer interrupt** ("Writing a value to the Compare register,
as a side effect, clears the timer interrupt", MD00090 Vol III Rev 6.02 §9.30, p.187): after
`mtc0 $rt, $11`, `Compare` holds `$rt` and `Cause.TI` is set only if the new `Count` equals it
(a new match in the same step); a pending timer interrupt from before is gone. -/
theorem mtc0_compare_clears_ti (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt 11#32 0#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    (step s).cp0Compare = readReg s (regIdxSpec rt) ∧
      (step s).cp0TimerInt = ((step s).cp0Count == readReg s (regIdxSpec rt)) ∧
      (step s).cp0Count = (if countEnabled s then s.cp0Count + 1#32 else s.cp0Count) := by
  sorry

/-- **`Cause` as `mfc0` reads it, with a timer interrupt pending**: `TI` (bit 30) and `IP7`
(bit 15) are set (MD00090 Vol III Rev 6.02 Table 9.52, p.209, 211; the timer request is merged into
`IP7`, Table 6.2, p.73, the `IntCtl.IPTI = 7` pin); every other bit is the stored `Cause` or a
hardware interrupt line (`hwIntBits`, `IP7..IP2`, Table 9.52, p.211). -/
theorem causeValue_timer (s : State) (h : s.cp0TimerInt = true) :
    causeValue s = s.cp0Cause ||| hwIntBits s ||| causeTiMask ||| causeIp7Mask := by
  sorry

/-- **`rdhwr $rt, $rd`** (MD00086 Vol II-A Rev 6.06, RDHWR, p.332-334): if hardware register `rd`
is implemented (`hwrValue s rd = some v`) and access is allowed (`rdhwrAllowed`: Coprocessor 0
enabled, or bit `rd` of `HWREna`), `$rt ← v` and `pc` advances; otherwise Reserved Instruction
("If access is not allowed or the register is not implemented, a Reserved Instruction Exception is
signaled", p.333). -/
theorem rdhwr_spec_raw (s : State) (w rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdhwr rt rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      match hwrValue s rd with
      | some v =>
        if rdhwrAllowed s rd then
          { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }
        else takeException s excCodeRI
      | none => takeException s excCodeRI) := by
  sorry

/-- `CPUNum` (`rdhwr` register 0) is `EBase.CPUNum`, which reads 0 (one processor). -/
theorem hwrValue_cpuNum (s : State) : hwrValue s 0#32 = some 0#32 := by
  sorry

/-- `SYNCI_Step` (`rdhwr` register 1) is 0: no caches need be synchronized. -/
theorem hwrValue_synciStep (s : State) : hwrValue s 1#32 = some 0#32 := by
  sorry

/-- `CC` (`rdhwr` register 2) is `Count`. -/
theorem hwrValue_cc (s : State) : hwrValue s 2#32 = some s.cp0Count := by
  sorry

/-- `CCRes` (`rdhwr` register 3) is 1: `Count` advances once per step. -/
theorem hwrValue_ccRes (s : State) : hwrValue s 3#32 = some 1#32 := by
  sorry

/-- Registers 4..31 are not implemented (`PerfCtr`, `XNP` are Release 6; 6..28 reserved; `ULR`
needs the optional UserLocal register; 30, 31 implementation-dependent, none). -/
theorem hwrValue_unimplemented (s : State) (rd : W32) (h : 4 ≤ rd.toNat) : hwrValue s rd = none := by
  sorry

/-- **`rdhwr` of an unimplemented register raises Reserved Instruction**, in every mode
(MD00086 Vol II-A Rev 6.06, RDHWR, Table 5.4 and Restrictions, p.333). -/
theorem rdhwr_reserved_unimplemented (s : State) (w rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdhwr rt rd))
    (hpb : s.pendingBranch = none) (hrd : 4 ≤ rd.toNat) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeRI) := by
  sorry

/-- **`rdhwr` outside Kernel Mode with `Status.CU0 = 0` and the `HWREna` bit clear raises Reserved
Instruction** (not Coprocessor Unusable): "Access to the specified hardware register is enabled if
Coprocessor 0 is enabled, or if the corresponding bit is set in the HWREna register. If access is
not allowed ... a Reserved Instruction Exception is signaled" (MD00086 Vol II-A Rev 6.06, RDHWR,
p.333). -/
theorem rdhwr_reserved_not_enabled (s : State) (w rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdhwr rt rd))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = false)
    (hen : (s.cp0HWREna >>> rd) &&& 1#32 = 0#32) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeRI) := by
  sorry

/-- **`rdhwr` of an implemented register with access allowed** writes the register's value to
`$rt` and advances `pc`. -/
theorem rdhwr_allowed (s : State) (w rt rd v : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdhwr rt rd))
    (hpb : s.pendingBranch = none) (hv : hwrValue s rd = some v)
    (hacc : cp0Usable s = true ∨ (s.cp0HWREna >>> rd) &&& 1#32 ≠ 0#32) (hexec : executesInstr s = true) :
    step s = timerTick
      { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  sorry

/-- **`mtc0 $rt, $7` (`HWREna`) keeps bits 3..0 only**: the bits of the registers the model
implements; "If RDHWR register ‘n’ is not implemented, bit ‘n’ of this field returns a zero and is
ignored on a write" (MD00090 Vol III Rev 6.02 Table 9.39, p.175). -/
theorem hwrena_write_masked (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt 7#32 0#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    (step s).cp0HWREna = readReg s (regIdxSpec rt) &&& 0x0000000F#32 := by
  sorry

/-- **The Reset exception clears `HWREna`** ("HWREna ← 0", MD00090 Vol III Rev 6.02 §6.2.5, p.89)
and leaves `Count`, `Compare` and `Cause.TI` (reset state "Undefined", Tables 9.44, 9.46, 9.52,
p.183, 187, 209) unchanged. -/
theorem resetException_timer (s : State) :
    (resetException s).cp0HWREna = 0#32 ∧ (resetException s).cp0Count = s.cp0Count ∧
      (resetException s).cp0Compare = s.cp0Compare ∧
      (resetException s).cp0TimerInt = s.cp0TimerInt := by
  sorry

/-! ## Floating point

Proved in `Semantics/Specs/` — FpuCommon.lean and the other Fpu*.lean files. -/

/-- **Coprocessor Unusable.** Any instruction that needs coprocessor 1
(`usesCop1`: every COP1/COP1X instruction, `lwc1`/`swc1`/`ldc1`/`sdc1`,
`movf`/`movt`) executed with `Status.CU1 = 0` raises Coprocessor Unusable and
does nothing else (MD00090 Vol III Rev 6.02 §6.2.22, p.100). -/
theorem fp_coprocessor_unusable (s : State) (w : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr)
    (huses : usesCop1 instr = true)
    (hnb : isBranchLike instr = false ∨ s.pendingBranch = none)
    (hcu : cu1Enabled s = false) (hexec : executesInstr s = true) :
    step s = timerTick (takeCoprocessorUnusable s) := by
  sorry

/-- **The FP trap.** If the operation raised an exception that is enabled in
FCSR, the instruction takes the Floating Point exception: `Cause.ExcCode =
15`, `pc` at the general exception vector, FCSR.Cause = this operation's
exceptions with FCSR.Flags untouched (`fcsrTrapped`) — and **no FP register is
written** (nor any general register or memory). -/
theorem fpCompletesS_trap (s s' : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags)
    (hen : Mips.Fp.fpeEnabled s.fcsr r.2 = true)
    (h : fpCompletesS s fd r = s') :
    causeExcCode s' = 15#32 ∧ s'.fpRegs = s.fpRegs ∧ s'.fcsr = fcsrTrapped s.fcsr r.2 ∧
      s'.regs = s.regs ∧ s'.physMem = s.physMem ∧ s'.pc = exceptionVector s := by
  sorry

/-- **No trap: result bits and FCSR.** When no enabled exception was raised,
the instruction completes: `FPR[fd]` holds exactly the result bits (given a
32-entry FP register file), FCSR is `raiseFlags` of the old FCSR (Cause =
this operation's exceptions, Flags accumulated), and `pc` advances. -/
theorem fpCompletesS_ok (s s' : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags)
    (hen : Mips.Fp.fpeEnabled s.fcsr r.2 = false) (hsize : s.fpRegs.size = 32)
    (h : fpCompletesS s fd r = s') :
    readFpReg s' (regIdx fd) = r.1 ∧ s'.fcsr = Mips.Fp.raiseFlags s.fcsr r.2 ∧
      s'.pc = s.pc + 4#32 ∧ s'.regs = s.regs := by
  sorry

/-- **`add.s`: `fd ← fs + ft`**, single precision: the result bits and exceptions are
`Mips.Fp.f32Add` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, ADD.fmt, p.34) -/
theorem addS_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd
        (Mips.Fp.f32Add (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  sorry

/-- **`add.d`: `fd ← fs + ft`**, double precision: the result bits and exceptions are
`Mips.Fp.f64Add` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, ADD.fmt, p.34) -/
theorem addD_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd
        (Mips.Fp.f64Add (Mips.Fp.envOf s.fcsr) (readFpD s fs) (readFpD s ft))) := by
  sorry

/-- **`cvt.w.s`** converts to a 32-bit word rounding **per FCSR.RM**
(MD00086 Vol II-A Rev 6.06, CVT.W.fmt, p.160): `Mips.Fp.f32ToW32 (getRM fcsr)` -/
theorem cvtWS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32ToW32 (Mips.Fp.getRM s.fcsr) (readFpReg s (regIdx fs)))) := by
  sorry

/-- **`c.cond.s`** writes `FCC[cc]` with predicate `cond` (its low four bits) of the two singles:
`Mips.Fp.f32Compare`, completing per `fpCompletesCmp` (MD00086 Vol II-A Rev 6.06,
C.cond.fmt, p.110-113). `fpCompletesCmp_ok` says only `FCC[cc]` changes -/
theorem cCondS_spec_raw (s : State) (w cond cc fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cCondS cond cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesCmp s cc
        (Mips.Fp.f32Compare (cond.setWidth 4) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  sorry

/-- **`c.lt.s` (cond = 12) sets `FCC[cc]` iff `fs < ft` and neither is a NaN.** -/
theorem c_lt_s_sets_cc (s s' : State) (w cc fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cCondS 12#32 cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hen : Mips.Fp.fpeEnabled s.fcsr (Mips.Fp.f32Compare Mips.Fp.Cond.lt
      (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))).2 = false)
    (hstep : step s = s') (hexec : executesInstr s = true) :
    Mips.Fp.getCC s'.fcsr (ccIdx cc) = true ↔
      Mips.Fp.F32Lt (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)) := by
  sorry

/-- **`movf`** (GPR): `if FCC[cc] = 0 then $rd ← $rs` (MD00086 Vol II-A Rev 6.06, MOVF, p.276) -/
theorem movf_spec_raw (s : State) (w rs cc rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movf rs cc rd))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readFcc s cc then { s with pc := s.pc + 4#32 }
      else
        { (writeReg s (regIdx rd) (readReg s (regIdx rs))) with
            pc := (writeReg s (regIdx rd) (readReg s (regIdx rs))).pc + 4#32 }) := by
  sorry

/-- **`mfc1`**: `$rt ← FPR[fs]`, raw bits -/
theorem mfc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdx rt) (readFpReg s (regIdx fs))) with pc := (writeReg s (regIdx rt) (readFpReg s (regIdx fs))).pc + 4#32 }) := by
  sorry

/-- **`lwc1`**: `FPR[ft] ← MEM32[$rs + sext(imm)]`; Address Error (AdEL) if not word-aligned -/
theorem lwc1_spec_raw (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lwc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdx rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v => { (writeFpReg s (regIdx ft) v) with pc := s.pc + 4#32 }) := by
  sorry

/-- **A misaligned `lwc1` raises Address Error (AdEL) on the effective address**; no FP register
is written (`exceptionEntry_always`). Same shape as `lw_misaligned_spec`. -/
theorem lwc1_misaligned_spec (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lwc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hmisaligned : (readReg s (regIdx rs) + signExt16 imm).toNat % 4 ≠ 0) (hexec : executesInstr s = true) :
    step s = timerTick (takeAddressException s excCodeAdEL (readReg s (regIdx rs) + signExt16 imm)) := by
  sorry

/-- **`cfc1`**: `$rt ←` FP control register `fs` — `Mips.Fp.readControl`: FIR (0), FCCR (25),
FEXR (26), FENR (28), FCSR (31); any other number reads 0 (pin for UNPREDICTABLE)
(MD00086 Vol II-A Rev 6.06, CFC1, p.129-130) -/
theorem cfc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cfc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdx rt) ((Mips.Fp.readControl s.fcsr fs.toNat).getD 0#32)) with pc := (writeReg s (regIdx rt) ((Mips.Fp.readControl s.fcsr fs.toNat).getD 0#32)).pc + 4#32 }) := by
  sorry

/-- **`ctc1`**: FP control register `fs ← $rt` through `Mips.Fp.writeControl`, then
`CheckFPException`: if the new FCSR has a Cause bit whose Enable is set, or Cause.E, the
Floating Point exception is taken **with the register already written**. A register
number the manual leaves UNPREDICTABLE is not written (pin), and the `CheckFPException()` that
follows the UNPREDICTABLE arm still runs on the unchanged FCSR
(MD00086 Vol II-A Rev 6.06, CTC1, p.149-151) -/
theorem ctc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ctc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      match Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt)) with
      | none =>
        if Mips.Fp.fcsrTrapPending s.fcsr then takeException s excCodeFPE
        else { s with pc := s.pc + 4#32 }
      | some f =>
        if Mips.Fp.fcsrTrapPending f then takeException { s with fcsr := f } excCodeFPE
        else { s with fcsr := f, pc := s.pc + 4#32 }) := by
  sorry

/-- **FCSR round trip through `ctc1 $rt, $31` / `cfc1 $rt, $31`.** Writing `v`
to control register 31 makes FCSR `v` with the reserved bits 22..18 cleared
(`Mips.Fp.fcsrWritableMask`), and reading register 31 of that FCSR returns
exactly that value. -/
theorem fcsr_ctc1_cfc1_roundtrip (fcsr v : W32) :
    ∃ f, Mips.Fp.writeControl fcsr 31 v = some f ∧ f = v &&& Mips.Fp.fcsrWritableMask ∧
      Mips.Fp.readControl f 31 = some (v &&& Mips.Fp.fcsrWritableMask) := by
  sorry

/-- **`bc1t`**: branch if `FCC[cc] = 1`, with the ordinary delay slot (MD00086 Vol II-A Rev 6.06,
BC1T, p.60) -/
theorem bc1t_spec_raw (s : State) (w cc imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bc1t cc imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readFcc s cc then
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 imm <<< 2)) }
      else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  sorry

/-! ## Address translation: the Fixed Mapping MMU, and the loader

Proved in `Semantics/Specs/` — Mmu.lean, Loader.lean. -/

/-- **useg/kuseg with `Status.ERL = 0`: physical = virtual + 1 GB** (MD00090 Vol III Rev 6.02 §A.1.1, p.313;
Table A.1, p.313: kuseg `0x0000_0000`-`0x7FFF_FFFF` → `0x4000_0000`-`0xBFFF_FFFF`). -/
theorem fixedMappingPA_kuseg_erl0 (va : W32) (h : va.toNat < 0x80000000) :
    fixedMappingPA false va = va + 0x40000000#32 ∧
      (fixedMappingPA false va).toNat = va.toNat + 0x40000000 := by
  sorry

/-- **useg/kuseg with `Status.ERL = 1`: identity** (§A.1.1, p.313; §4.7, p.31: "the kuseg Segment becomes
an unmapped, uncached Segment"). -/
theorem fixedMappingPA_kuseg_erl1 (va : W32) (h : va.toNat < 0x80000000) :
    fixedMappingPA true va = va := by
  sorry

/-- **kseg0 → the low 512 MB** (`0x8000_0000`-`0x9FFF_FFFF` → `0x0000_0000`-`0x1FFF_FFFF`; Table 4.3, p.31;
Table A.1, p.313), whatever `ERL` is. -/
theorem fixedMappingPA_kseg0 (erl : Bool) (va : W32) (h1 : 0x80000000 ≤ va.toNat)
    (h2 : va.toNat < 0xA0000000) : (fixedMappingPA erl va).toNat = va.toNat - 0x80000000 := by
  sorry

/-- **kseg1 → the same low 512 MB** (`0xA000_0000`-`0xBFFF_FFFF` → `0x0000_0000`-`0x1FFF_FFFF`; Table 4.3,
p.31; Table A.1, p.313), whatever `ERL` is. -/
theorem fixedMappingPA_kseg1 (erl : Bool) (va : W32) (h1 : 0xA0000000 ≤ va.toNat)
    (h2 : va.toNat < 0xC0000000) : (fixedMappingPA erl va).toNat = va.toNat - 0xA0000000 := by
  sorry

/-- **kseg2 (sseg/ksseg) and kseg3: identity** ("Sseg/Ksseg/Kseg2/Kseg3 addresses are mapped using an
identity mapping", §A.1.1, p.313; Table A.1, p.314). -/
theorem fixedMappingPA_kseg23 (erl : Bool) (va : W32) (h : 0xC0000000 ≤ va.toNat) :
    fixedMappingPA erl va = va := by
  sorry

/-- **kseg0 and kseg1 alias**: `0x8000_0000 + x` and `0xA000_0000 + x` are both physical `x`. -/
theorem fixedMappingPA_kseg0_kseg1_alias (erl : Bool) (x : W32) (hx : x.toNat < 0x20000000) :
    fixedMappingPA erl (0x80000000#32 + x) = x ∧ fixedMappingPA erl (0xA0000000#32 + x) = x := by
  sorry

/-- **From User Mode, every address outside useg is an Address Error**: kseg0, kseg1, kseg2 and kseg3 are
"Address Error" from User Mode (MD00090 Vol III Rev 6.02 Table 4.2, p.30; §6.2.9, p.92), checked
"before the translation process" (§A.1.1, p.313). -/
theorem translate_user_kernel_address (s : State) (va : W32) (hum : userMode s = true)
    (hk : isUseg va = false) : translate s va = none := by
  sorry

/-- **With `Status.ERL = 1` kuseg is the identity map** (§4.7, p.31; Table A.1, p.313). -/
theorem translate_erl1_kuseg_identity (s : State) (va : W32) (herl : erlSet s = true)
    (h : va.toNat < 0x80000000) : translate s va = some va := by
  sorry

/-- **An instruction fetch from a kernel address in User Mode raises Address Error (AdEL)** with
`BadVAddr = EPC = pc` (§6.2.9, p.92-93). -/
theorem step_fetch_user_kernel_address (s : State) (hum : userMode s = true)
    (hk : isUseg s.pc = false) (hexec : executesInstr s = true) : step s = timerTick (takeAddressException s excCodeAdEL s.pc) := by
  sorry

/-- **A User-Mode `lw` of a kernel address raises Address Error (AdEL)**, with `BadVAddr` = the
effective address, and changes no memory. -/
theorem lw_user_kernel_address (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none) (hum : userMode s = true)
    (hk : isUseg (readReg s (regIdxSpec rs) + signExt16 imm) = false) (hexec : executesInstr s = true) :
    step s = timerTick (takeAddressException s excCodeAdEL (readReg s (regIdxSpec rs) + signExt16 imm)) ∧
      (step s).physMem = s.physMem ∧
      (step s).cp0BadVAddr = readReg s (regIdxSpec rs) + signExt16 imm := by
  sorry

/-- **A User-Mode `sw` to a kernel address raises Address Error (AdES)**, with `BadVAddr` = the
effective address, and stores nothing. -/
theorem sw_user_kernel_address (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none) (hum : userMode s = true)
    (hk : isUseg (readReg s (regIdxSpec rs) + signExt16 imm) = false) (hexec : executesInstr s = true) :
    step s = timerTick (takeAddressException s excCodeAdES (readReg s (regIdxSpec rs) + signExt16 imm)) ∧
      (step s).physMem = s.physMem ∧
      (step s).cp0BadVAddr = readReg s (regIdxSpec rs) + signExt16 imm := by
  sorry

/-- **kseg0/kseg1 data aliasing**: in Kernel Mode, a word stored through kseg1 at `0xA000_0000 + x` is what
a load through kseg0 at `0x8000_0000 + x` returns. -/
theorem kseg1_store_visible_through_kseg0 (s s' : State) (x v : W32) (hk : kernelMode s = true)
    (hx : x.toNat < 0x20000000) (hal : x.toNat % 4 = 0)
    (h : writeMemWord s (0xA0000000#32 + x) v = some s') :
    readMemWord s' (0x80000000#32 + x) = some v := by
  sorry

/-- **Loader correctness (hosted start).** If the image `p` holds `w` at the virtual address `a`, all image
addresses are word-aligned and no other image address is loaded at the same physical address
(`Env.loadAddr`), then a word read (fetch or `lw`) of `a` in the loaded state returns `w`. -/
theorem load_readMemWord (p : Program) (a w : W32) (hw : p.get? a = some w)
    (halign : ∀ b v, p.get? b = some v → b.toNat % 4 = 0)
    (hdisj : ∀ b v, p.get? b = some v → b ≠ a → loadAddr b ≠ loadAddr a) :
    readMemWord (load p) a = some w := by
  sorry

/-- **The first step of a loaded program executes the image word at `textBase`.** -/
theorem load_step_fetches_image (p : Program) (w : W32) (instr : Instruction)
    (hw : p.get? textBase = some w) (hdecode : decode w = some instr)
    (halign : ∀ b v, p.get? b = some v → b.toNat % 4 = 0)
    (hdisj : ∀ b v, p.get? b = some v → b ≠ textBase → loadAddr b ≠ loadAddr textBase) :
    step (load p) = timerTick (execInstr (load p) instr) := by
  sorry

/-- **Loader correctness (reset start, `ERL = 1`)** for kernel-segment addresses (kseg0-kseg3, where
`ERL` does not change the mapping), e.g. the boot code at the reset vector `0xBFC0_0000`. -/
theorem loadAtReset_readMemWord_kseg (p : Program) (a w : W32) (hw : p.get? a = some w)
    (hk : 0x80000000 ≤ a.toNat)
    (halign : ∀ b v, p.get? b = some v → b.toNat % 4 = 0)
    (hdisj : ∀ b v, p.get? b = some v → b ≠ a → loadAddr b ≠ loadAddr a) :
    readMemWord (loadAtReset p) a = some w := by
  sorry

/-- **The observer's virtual name of a loaded word is its image address, outside kseg1.**
`Env.canonicalVAddr` (the virtual address `MipsRun`'s `memory` field reports a physical word under)
inverts the loader's `Env.loadAddr` on every virtual address not in kseg1. -/
theorem canonicalVAddr_loadAddr (va : VAddr) (h : isKseg1 va = false) :
    canonicalVAddr (loadAddr va) = va := by
  sorry

/-- **A kseg1 address comes back as its kseg0 alias**: kseg0 and kseg1 load to the same physical
address, so `loadAddr` is not injective and `canonicalVAddr` names the kseg0 alias. -/
theorem canonicalVAddr_loadAddr_kseg1 (va : VAddr) (h : isKseg1 va = true) :
    canonicalVAddr (loadAddr va) = va - 0x20000000#32 := by
  sorry

/-- **`canonicalVAddr` is a right inverse of `loadAddr` on the loader's range**: every physical
address outside `0x2000_0000`-`0x3FFF_FFFF` (the part only kuseg with `ERL = 1` reaches) is
`loadAddr` of its canonical virtual name. -/
theorem loadAddr_canonicalVAddr (pa : PAddr)
    (h : ¬ (0x20000000 ≤ pa.toNat ∧ pa.toNat < 0x40000000)) :
    loadAddr (canonicalVAddr pa) = pa := by
  sorry

/-! ## Self-modifying code and the hosted environment

Proved in `Semantics/Specs/` — SelfModifying.lean, Hosted.lean. The hosted run is NOT the
architecture (`Semantics/Env.lean`); these statements say exactly where it differs from `step`. -/

/-- **Self-modifying code: a store to the next instruction is what the next fetch returns.** If
the instruction at `pc` (not in a delay slot) is `sw $rt, imm($rs)` and its effective address is
`pc + 4`, and that address is accessible in the current mode (`hacc`: Kernel Mode, or a useg
address; otherwise the store is an Address Error), then after the step `pc = pc + 4` and the
fetch there returns `$rt`. -/
theorem sw_next_instruction_is_fetched (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none)
    (haddr : readReg s (regIdxSpec rs) + signExt16 imm = s.pc + 4#32)
    (hacc : accessAllowed s (s.pc + 4#32) = true) (hexec : executesInstr s = true) :
    (step s).pc = s.pc + 4#32 ∧
      readMemWord (step s) (step s).pc = some (readReg s (regIdxSpec rt)) := by
  sorry

/-- **A store to the address of the next instruction changes what is executed**: if the stored
value decodes to `instr'`, the next step executes `instr'`. -/
theorem store_changes_next_instruction (s : State) (w rs rt imm : W32) (instr' : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none)
    (haddr : readReg s (regIdxSpec rs) + signExt16 imm = s.pc + 4#32)
    (hacc : accessAllowed s (s.pc + 4#32) = true)
    (hnew : decode (readReg s (regIdxSpec rt)) = some instr') (hexec : executesInstr s = true)
    (hexec2 : executesInstr (step s) = true) :
    step (step s) = timerTick (execInstr (step s) instr') := by
  sorry

/-- **The hosted environment is `step` when it provides nothing.** If the stopping convention
does not apply and either services are off or the instruction at `pc` selects no hosted service,
a hosted step is a processor step and leaves the output alone. -/
theorem hostStep_eq_step (env : HostEnv) (h : Hosted)
    (hstop : stopReason env h.machine = none)
    (hsvc : env.services = false ∨ selectedService h.machine = none) :
    hostStep env h = .next { h with machine := step h.machine } := by
  sorry

/-- **The hosted run agrees with the bare run whenever no hosted service is selected** (and the
stopping convention never applies) along the bare run's first `n` states. -/
theorem runHosted_agrees_with_run (env : HostEnv) (out : String) (n : Nat) (s : State)
    (hquiet : ∀ j, j < n → stopReason env (run s j) = none ∧
      (env.services = false ∨ selectedService (run s j) = none)) :
    runHosted env n { machine := s, out := out } = .limitReached { machine := run s n, out := out } n := by
  sorry

/-- **Hosted service 1 (print int)** appends the signed decimal rendering of `$a0` and completes
the `syscall` (`pc + 4`); nothing else in the processor changes. (Formerly `syscall1_spec`.) -/
theorem hosted_print_int (env : HostEnv) (h : Hosted) (w code : W32)
    (hstop : stopReason env h.machine = none) (hon : env.services = true)
    (hfetch : readMemWord h.machine h.machine.pc = some w)
    (hdecode : decode w = some (.syscall code))
    (hv0 : readReg h.machine (regIdxSpec 2#32) = 1#32)
    (hpb : h.machine.pendingBranch = none) (hexec : executesInstr h.machine = true) :
    hostStep env h =
      .next { machine := { h.machine with pc := h.machine.pc + 4#32 },
              out := h.out ++ toString (asSigned (readReg h.machine (regIdxSpec 4#32))) } := by
  sorry

/-- **Hosted service 10 (exit)** stops the run with `exit`. (Formerly `syscall10_spec`.) -/
theorem hosted_exit (env : HostEnv) (h : Hosted) (w code : W32)
    (hstop : stopReason env h.machine = none) (hon : env.services = true)
    (hfetch : readMemWord h.machine h.machine.pc = some w)
    (hdecode : decode w = some (.syscall code))
    (hv0 : readReg h.machine (regIdxSpec 2#32) = 10#32) (hexec : executesInstr h.machine = true) :
    hostStep env h = .halt .exit := by
  sorry

/-- **`$zero` is unchanged by a hosted run**: the hosted services write no register. -/
theorem runHosted_preserves_zero_register (env : HostEnv) (n : Nat) (h : Hosted) :
    readReg (runHosted env n h).final.machine 0 = readReg h.machine 0 := by
  sorry

/-! ## Interrupts, standby, IntCtl and SRSCtl (wave 6) -/

/-- **An interrupt preempts the instruction at `pc`**: if an interrupt is requested and enabled,
the step is the Interrupt exception followed by the timer; the instruction at `pc` is not fetched
or executed (an interrupt is "the highest priority relative to the next instruction", MD00090
Vol III Rev 6.02 Table 6.7, p.84, above every fetch and instruction exception in Table 6.6, p.83). -/
theorem step_interrupt (s : State) (h : interruptTaken s = true) :
    step s = timerTick (takeInterrupt s) := by
  sorry

/-- **The condition** (MD00090 Vol III Rev 6.02 §6.1, p.72: a request is made, "The IE bit in the
Status register is a one", "The EXL and ERL bits in the Status register are both zero"; Table 6.2,
p.73: request `i` is "CauseIPi and StatusIMi"). -/
theorem interruptTaken_iff (s : State) :
    interruptTaken s = true ↔
      s.cp0Status &&& statusIeMask ≠ 0#32 ∧ s.cp0Status &&& statusExlMask = 0#32 ∧
      s.cp0Status &&& statusErlMask = 0#32 ∧
      causeValue s &&& s.cp0Status &&& statusImMask ≠ 0#32 := by
  sorry

/-- **No interrupt with `Status.IE = 0`.** -/
theorem no_interrupt_ie0 (s : State) (h : s.cp0Status &&& statusIeMask = 0#32) :
    interruptTaken s = false := by
  sorry

/-- **No interrupt with `Status.EXL = 1`** (inside an exception handler). -/
theorem no_interrupt_exl (s : State) (h : s.cp0Status &&& statusExlMask ≠ 0#32) :
    interruptTaken s = false := by
  sorry

/-- **No interrupt with `Status.ERL = 1`** (after Reset, until software clears it). -/
theorem no_interrupt_erl (s : State) (h : s.cp0Status &&& statusErlMask ≠ 0#32) :
    interruptTaken s = false := by
  sorry

/-- **No interrupt when every request is masked** (`Cause.IP & Status.IM = 0`). -/
theorem no_interrupt_masked (s : State) (h : interruptRequests s = 0#32) :
    interruptTaken s = false := by
  sorry

/-- **Interrupt entry, not in a delay slot** (MD00090 Vol III Rev 6.02 §6.2.3, p.86-88; §6.2.26,
p.102): `EPC ←` the address of the instruction that was not executed, `Cause.BD ← 0`, `ExcCode ←
Int` (0), `CE ← 0`, `Status.EXL ← 1`, `PC ←` the interrupt vector, and the processor leaves standby.
`EXL = 0` holds whenever an interrupt is taken. -/
theorem takeInterrupt_not_in_delay_slot (s : State) (hexl : s.cp0Status &&& statusExlMask = 0#32)
    (hpb : s.pendingBranch = none) :
    (takeInterrupt s).cp0Epc = s.pc ∧
      (takeInterrupt s).cp0Cause =
        (s.cp0Cause &&& ~~~causeBdMask) &&& ~~~(causeExcCodeMask ||| causeCeMask) ∧
      causeExcCode (takeInterrupt s) = excCodeInt ∧
      (takeInterrupt s).cp0Status = s.cp0Status ||| statusExlMask ∧
      (takeInterrupt s).pc = interruptVector s ∧
      (takeInterrupt s).standby = false := by
  sorry

/-- **Interrupt entry in a branch delay slot** (`pendingBranch = some t`): `EPC ←` the branch
(`pc - 4`), `Cause.BD ← 1` ("Address of the branch or jump instruction (PC-4)", MD00090 Vol III
Rev 6.02 Table 6.11, p.87); the pending branch is abandoned, so `eret` re-executes the branch. -/
theorem takeInterrupt_in_delay_slot (s : State) (t : W32)
    (hexl : s.cp0Status &&& statusExlMask = 0#32) (hpb : s.pendingBranch = some t) :
    (takeInterrupt s).cp0Epc = s.pc - 4#32 ∧
      (takeInterrupt s).cp0Cause =
        (s.cp0Cause ||| causeBdMask) &&& ~~~(causeExcCodeMask ||| causeCeMask) ∧
      causeExcCode (takeInterrupt s) = excCodeInt ∧
      (takeInterrupt s).pendingBranch = none ∧
      (takeInterrupt s).pc = interruptVector s := by
  sorry

/-- **`Cause.IV = 0`: the general exception vector** (offset `0x180`; MD00090 Vol III Rev 6.02
§6.2.26, p.102: "General exception vector (offset 0x180) if the IV bit in the Cause register is
zero"). -/
theorem interruptVector_iv0 (s : State) (h : s.cp0Cause &&& causeIvMask = 0#32) :
    interruptVector s = exceptionVector s := by
  sorry

/-- **`Cause.IV = 1`, `Status.BEV = 0`: `EBase` + `0x200`** ("Interrupt vector (offset 0x200) if the
IV bit in the Cause register is one", §6.2.26, p.102; `IntCtl.VS = 0`, so the vectored-interrupt
offsets of Table 6.4 do not apply, §6.2.3 Operation, p.88). `0x8000_0200` with `EBase` at its reset
value (Table 6.10, p.86). -/
theorem interruptVector_iv1_bev0 (s : State) (h : s.cp0Cause &&& causeIvMask ≠ 0#32)
    (hbev : s.cp0Status &&& statusBevMask = 0#32) :
    interruptVector s = ((s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32) ||| 0x200#32 := by
  sorry

/-- **`Cause.IV = 1`, `Status.BEV = 1`: `0xBFC0_0400`** (Table 6.10, p.86: "Interrupt 1 0 1 ...
0xBFC0.0400"; base `0xBFC0_0200`, Table 6.8, p.85, plus `0x200`). -/
theorem interruptVector_iv1_bev1 (s : State) (h : s.cp0Cause &&& causeIvMask ≠ 0#32)
    (hbev : s.cp0Status &&& statusBevMask ≠ 0#32) :
    interruptVector s = 0xBFC00400#32 := by
  sorry

/-- **A software interrupt requested with `mtc0`** (MD00090 Vol III Rev 6.02 Table 9.52, p.212:
`IP1..IP0` "Controls the request for software interrupts", R/W; Table 6.2, p.73: SW0/SW1 are
"CauseIP0 and StatusIM0" / "CauseIP1 and StatusIM1"): if `mtc0 $rt, $13` writes a 1 into `IP0`
(bit 8) or `IP1` (bit 9) and `Status.IMi` is 1, a request is pending after the step; with `IE = 1`
and `EXL = ERL = 0` the next step takes the interrupt (`step_interrupt`), so its `EPC` is the
instruction after the `mtc0` (the hazard of Table 6.5, p.82, is cleared at once: pin). -/
theorem mtc0_cause_requests_software_interrupt (s : State) (w rt : W32) (i : Nat)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt 13#32 0#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true)
    (hi : i = 8 ∨ i = 9) (hip : (readReg s (regIdxSpec rt)).getLsbD i = true)
    (him : s.cp0Status.getLsbD i = true) (hen : interruptsEnabled s = true) :
    interruptRequests (step s) ≠ 0#32 ∧ interruptTaken (step s) = true := by
  sorry

/-- **The timer requests an interrupt on `IP7`** (MD00090 Vol III Rev 6.02 §9.30, p.187: "When the
value of the Count register equals the value of the Compare register, an interrupt request is
made"; Table 6.2, p.73: HW5, "CauseIP7 and StatusIM7"; `IntCtl.IPTI = 7`): with `Cause.TI` set and
`Status.IM7 = 1` a request is pending, so with `IE = 1`, `EXL = ERL = 0` the step takes the
interrupt. -/
theorem timer_requests_interrupt (s : State) (hti : s.cp0TimerInt = true)
    (him : s.cp0Status.getLsbD 15 = true) :
    interruptRequests s ≠ 0#32 := by
  sorry

/-- **The hardware interrupt lines are inputs**: no step changes them (MD00090 Vol III Rev 6.02
Table 9.52, p.211: `IP7..IP2` are Read-only, "Hardware interrupt 5 ... 0"). Whatever drives them is
the system around the processor (`Semantics/Env.lean`). -/
theorem step_hwInt (s : State) : (step s).hwInt = s.hwInt := by
  sorry

/-- **`wait` completes and enters standby** (MD00086 Vol II-A Rev 6.06, WAIT, p.442: "The WAIT
instruction is implemented by stalling the pipeline at the completion of the instruction and
entering a lower power mode"): `pc` moves to the next instruction, which "execution continues with"
once the pipeline restarts, and `State.standby` is set (`Step.lean`'s `wait` arm). The standby
steps themselves: `Specs/Interrupt.lean` (`step_standby_stays`, `step_standby_restarts`,
`step_standby_interrupt`). -/
theorem wait_spec_raw (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.wait code))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick ({ s with standby := true, pc := s.pc + 4#32 }) := by
  sorry

/-- **In standby with no request, the processor stays stopped**: only the timer advances (MD00086
Vol II-A Rev 6.06, WAIT, p.442: "stalling the pipeline ... The pipeline is restarted when an
external event, such as an interrupt or external request occurs"). -/
theorem step_standby_stays (s : State) (hsb : s.standby = true)
    (hreq : interruptRequests s = 0#32) :
    step s = timerTick s := by
  sorry

/-- **A request that is not enabled restarts the pipeline** (pin: WAIT, p.442, "It is
implementation-dependent whether the pipeline restarts when a non-enabled interrupt is requested";
the model restarts, as Release 6 requires, p.443): the step leaves standby, and the next step
executes the instruction after the `wait` (`pc` already holds it). -/
theorem step_standby_restarts (s : State) (hsb : s.standby = true)
    (hreq : interruptRequests s ≠ 0#32) (hen : interruptsEnabled s = false) :
    step s = timerTick { s with standby := false } := by
  sorry

/-- **An enabled interrupt in standby is taken with `EPC` = the instruction after the `wait`**
("If the pipeline restarts as the result of an enabled interrupt, that interrupt is taken between
the WAIT instruction and the following instruction (EPC for the interrupt points at the instruction
following the WAIT instruction)", MD00086 Vol II-A Rev 6.06, WAIT, p.442). After `wait`,
`pc` is that instruction (`wait_spec_raw`) and no branch is pending. -/
theorem step_standby_interrupt (s : State) (_hsb : s.standby = true) (h : interruptTaken s = true)
    (hpb : s.pendingBranch = none) :
    step s = timerTick (takeInterrupt s) ∧ (step s).cp0Epc = s.pc ∧ (step s).standby = false := by
  sorry

/-- **`IntCtl` reads `IPTI = 7`, every other field 0** (MD00090 Vol III Rev 6.02 Table 9.48,
p.199-201): `IPTI` (31..29) = 7; `IPPCI` (28..26) = 0 ("If performance counters are not implemented
(Config1PC = 0), this field returns zero on read"); `IPFDC` (25..23) = 0; `VS` (9..5) = 0 ("If
neither EIC interrupt mode nor VI mode are implemented ... this field is ignored on write and reads
as zero"). -/
theorem intCtlValue_fields :
    intCtlValue >>> 29 = 7#32 ∧ (intCtlValue >>> 26) &&& 7#32 = 0#32 ∧
      (intCtlValue >>> 23) &&& 7#32 = 0#32 ∧ (intCtlValue >>> 5) &&& 31#32 = 0#32 := by
  sorry

/-- **`SRSCtl` reads 0**: `HSS` (29..26) = 0, only the normal GPRs ("A value of zero in this field
indicates that only the normal GPRs are implemented", MD00090 Vol III Rev 6.02 Table 9.49, p.203),
and `ESS` (15..12), `PSS` (9..6), `CSS` (3..0) = 0 in every state, so the shadow-set update of
exception entry ("SRSCtlPSS ← SRSCtlCSS; SRSCtlCSS ← NewShadowSet", guarded by "SRSCtlHSS ≠ 0",
§6.2.3, p.88) and of `eret` ("SRSCtlCSS ← SRSCtlPSS", MD00086 Vol II-A Rev 6.06, ERET, p.177) never
applies, and would change nothing if it did. -/
theorem srsCtlValue_fields :
    (srsCtlValue >>> 26) &&& 15#32 = 0#32 ∧ (srsCtlValue >>> 12) &&& 15#32 = 0#32 ∧
      (srsCtlValue >>> 6) &&& 15#32 = 0#32 ∧ srsCtlValue &&& 15#32 = 0#32 := by
  sorry

/-- **`mfc0 $rt, $12, 2` reads `SRSCtl` = 0 in every state** (`HSS = ESS = PSS = CSS = 0`): no
exception entry or `eret` ever makes `CSS` or `PSS` nonzero. -/
theorem mfc0_srsctl_spec (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc0 rt 12#32 2#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick
      { (writeReg s (regIdxSpec rt) 0#32) with pc := (writeReg s (regIdxSpec rt) 0#32).pc + 4#32 } := by
  sorry

/-- **`rdpgpr $rd, $rt`** (MD00086 Vol II-A Rev 6.06, RDPGPR, p.335: "GPR[rd] ← SGPR[SRSCtlPSS,
rt]"): with only the normal GPRs (`SRSCtl.HSS = 0`, `PSS = 0`, MD00090 Vol III Rev 6.02 Table 9.49,
p.203-204; "The normal GPRs are logically considered shadow set zero", §7, p.103), `$rd ← $rt`. -/
theorem rdpgpr_spec_raw (s : State) (w rd rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdpgpr rd rt))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt))) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt))).pc + 4#32 }) := by
  sorry

/-- **`wrpgpr $rd, $rt`** (MD00086 Vol II-A Rev 6.06, WRPGPR, p.444: "SGPR[SRSCtlPSS, rd] ←
GPR[rt]"): with only the normal GPRs (`PSS = 0`), `$rd ← $rt`. -/
theorem wrpgpr_spec_raw (s : State) (w rd rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.wrpgpr rd rt))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt))) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt))).pc + 4#32 }) := by
  sorry

/-! ## The refinement of the manual specification (Wave 7D)

The statements below relate the model to the independent manual specification `Semantics/Manual/*`
through the projection `Refine.abs` and the invariant `Refine.Inv` (`Semantics/Refine/Defs.lean`).
Their meaning therefore rests on those definitions too: the `Manual` definitions (the transcribed
pseudocode, `Manual.InstructionTime`, `Manual.Step`, `Manual.ChoiceFree`, `Manual.Oracle.Valid`, …),
the model's choices `Manual.modelImpl`/`Manual.modelOracle`, and `Refine.abs`/`Refine.Inv`. Their
proofs (`Semantics/Refine/*`) are not trusted. See `docs/MANUAL-SPEC.md` I.5 and the README,
"What is proved, what is tested, what is trusted".
-/

/-- **`step` refines the manual (the independent correctness theorem).** From every state `s` of the
invariant `Refine.Inv` (register files of 32 entries, `$zero` reads 0, FCSR bits 22..18 read 0,
`Status` holds only implemented bits), one `step` of the model is exactly one instruction time of the
manual specification `Manual.InstructionTime` (`Semantics/Manual/`, transcribed from the manuals'
pseudocode independently of the model; `docs/MANUAL-SPEC.md`), seen through the projection
`Refine.abs`. The manual's implementation constants and its UNDEFINED/UNPREDICTABLE choices are
resolved as the model resolves them (`Manual.modelImpl`, `Manual.modelOracle`, each a pin documented in
`docs/spec/SPEC-NOTES.md`), and the manual's decoder is the model's `decode` (sound:
`decoderSound_decode`). It covers every path of the instruction time: interrupt, low-power (WAIT)
standby, nullified delay slot of a branch-likely, fetch errors, undecodable words (Reserved
Instruction / Coprocessor Unusable), all 183 instructions, the delay-slot `I+1` effects, and the timer
tick. `docs/MANUAL-SPEC.md` I.5. -/
theorem step_eq_manual (s : State) (hs : Refine.Inv s) :
    Manual.InstructionTime Manual.modelImpl Manual.modelOracle decode (Refine.abs s) =
      some (Refine.abs (step s)) := by
  sorry

/-- **`step` is a behaviour the manual allows**: some valid resolution of the manual's choices
(`Manual.Step`: an oracle within the limits `Manual.Oracle.Valid`) takes `abs s` to `abs (step s)`.
`step_eq_manual` with `modelOracle_valid`. -/
theorem step_refines_manual (s : State) (hs : Refine.Inv s) :
    Manual.Step Manual.modelImpl decode (Refine.abs s) (Refine.abs (step s)) := by
  sorry

/-- **`run s n` is `n` instruction times of the manual** (from a state of the invariant; the
invariant is preserved, `step_preserves_inv`). -/
theorem run_refines_manual (s : State) (hs : Refine.Inv s) (n : Nat) :
    Manual.InstructionTimes Manual.modelImpl Manual.modelOracle decode n (Refine.abs s) =
      some (Refine.abs (run s n)) := by
  sorry

/-- **Where the manual makes no choice, `step` is the only behaviour it allows**: from a state of
the invariant at which `Manual.ChoiceFree` holds (no interrupt, no exception other than Coprocessor
Unusable, no UNPREDICTABLE encoding past the coprocessor-usability check, no CTI in a delay slot, and
an Operation that reaches no oracle choice whose value can change the result, `Manual.ConsultsOracle`:
e.g. a load or store while `LLbit = 0`, `DIV` by a nonzero divisor, a double FP operation on even
registers and no quiet-NaN operand of `ABS`/`NEG`/`CVT`), every next state the manual allows is
`abs (step s)`. -/
theorem step_unique_of_choiceFree (s : State) (hs : Refine.Inv s)
    (h : Manual.ChoiceFree Manual.modelImpl decode (Refine.abs s) = true) (a' : Manual.Arch)
    (h' : Manual.Step Manual.modelImpl decode (Refine.abs s) a') : a' = Refine.abs (step s) := by
  sorry

/-- **The model's choices are within the manual's limits**: `Manual.modelOracle` satisfies
`Manual.Oracle.Valid`, which formalizes the three restrictions on UNPREDICTABLE operations of MD00086
Vol II-A Rev 6.06 §1.2.1 (p.3-4): every UNPREDICTABLE outcome is an exception, `proceed`, or a state
within `Manual.UnpredictableLimits` (no change to the state inaccessible in the current mode, no entry
into the lower power mode, no change to the hardware interrupt inputs `HW`: a model-side
strengthening, MD00090 Vol III Rev 6.02 Table 6.2, p.73; Table 9.52, p.211), and in User Mode every UNPREDICTABLE outcome and value is
non-interfering (`Manual.NIOutcome`, `Manual.NIValue`: it does not depend on the state inaccessible in
that mode); the UNDEFINED outcomes do not hang the processor (§1.2.2, p.4) and leave `HW` unchanged
(the same strengthening); the QNaN choices of
`CVT.D.S`/`CVT.S.D` are quiet NaNs (MD00082 Vol I-A Rev 6.01 §6.3.1.5, p.82); a Reset changes
registers only. This makes `Manual.Step` in `step_refines_manual` meaningful. -/
theorem modelOracle_valid : Manual.modelOracle.Valid := by
  sorry

/-- **The manual is deterministic at a choice-free state**: for every implementation and decoder,
all valid resolutions of the choices give the same next state when `Manual.ChoiceFree` holds. A
statement about the specification alone. -/
theorem manual_step_deterministic (i : Manual.Impl) (dec : W32 → Option Instruction)
    (a a₁ a₂ : Manual.Arch) (h : Manual.ChoiceFree i dec a = true) (h₁ : Manual.Step i dec a a₁)
    (h₂ : Manual.Step i dec a a₂) : a₁ = a₂ := by
  sorry

/-- **An interrupt is a real choice of the manual** (the other direction of `ChoiceFree`, for the
interrupt case): when an interrupt is taken, two valid resolutions of the manual's choices give
different instruction times (`Cause.CE` "is loaded, but not defined", MD00090 Vol III Rev 6.02 §6.2.3,
p.87). -/
theorem interrupt_choice_exists (i : Manual.Impl) (dec : W32 → Option Instruction) (a : Manual.Arch)
    (h : Manual.InterruptTaken i a = true) :
    ∃ o₁ o₂ : Manual.Oracle, o₁.Valid ∧ o₂.Valid ∧
      Manual.InstructionTime i o₁ dec a ≠ Manual.InstructionTime i o₂ dec a := by
  sorry

/-- **`ChoiceFree` is exact** (wave 9; the other direction of `manual_step_deterministic`): with the
model's implementation constants and any decoder, at every state where `Manual.ChoiceFree` is
`false`, two valid resolutions of the manual's choices give different instruction times. Together
with `manual_step_deterministic`, `ChoiceFree` holds exactly where the manual's instruction time is
determined. -/
theorem choiceFree_exact (dec : W32 → Option Instruction) (a : Manual.Arch)
    (h : Manual.ChoiceFree Manual.modelImpl dec a = false) :
    ∃ o₁ o₂ : Manual.Oracle, o₁.Valid ∧ o₂.Valid ∧
      Manual.InstructionTime Manual.modelImpl o₁ dec a ≠ Manual.InstructionTime Manual.modelImpl o₂ dec a := by
  sorry

/-- **The model's implementation constants are valid**: of this profile (`Manual.Impl.WF`), with
`RECIP.fmt` within 1 ULP of the IEEE-mandated representation of `1.0 / fs` (MD00086 Vol II-A Rev
6.06, RECIP.fmt, p.336; `Manual.Impl.RecipAccurate`) and of the exact `1/fs`
(`Manual.Impl.RecipExact`), and `RSQRT.fmt` within 2 ULP of the exact `1/√fs` (RSQRT.fmt, p.343;
`Manual.Impl.RsqrtAccurate`), the last two without flushing (`Manual/Accuracy.lean`, wave 10); and
both signal Invalid Operation and Division by Zero as `Manual.Impl.RecipFlags` requires (MD00082 Vol
I-A Rev 6.01 §6.3.1.4-5, p.81-82; §6.7.2.1-2, p.100; Overflow, Underflow, Inexact left free). -/
theorem modelImpl_valid : Manual.modelImpl.Valid := by
  sorry

/-- **The model's decoder is sound for the manual's encodings**: whatever `decode` returns for a
word has that word as its instruction diagram (`Manual.enc`, transcribed from the manual's format
diagrams). So passing `decode` as the manual's decoder in `step_eq_manual` adds no behaviour the
manual's diagrams do not have. -/
theorem decoderSound_decode : Manual.DecoderSound decode := by
  sorry

/-- **The model's Reset exception is the manual's** (`Manual.ResetException`, MD00090 Vol III
Rev 6.02 §6.2.5, p.89-90) under the model's choice of the undefined registers, from every state whose
`Status` holds only implemented bits. -/
theorem resetException_refines_manual (s : State) (h : Refine.StatusImplemented s) :
    Refine.abs (resetException s) = Manual.ResetException Manual.modelOracle (Refine.abs s) := by
  sorry

/-- **The state after a cold reset** is the manual's Reset exception applied to the power-on
state. -/
theorem resetState_refines_manual :
    Refine.abs resetState = Manual.ResetException Manual.modelOracle (Refine.abs powerOnState) := by
  sorry

/-- **`step` preserves the invariant** under which `step_eq_manual` is stated. -/
theorem step_preserves_inv (s : State) (h : Refine.Inv s) : Refine.Inv (step s) := by
  sorry

/-- **The reset state satisfies the invariant.** -/
theorem inv_resetState : Refine.Inv resetState := by
  sorry

/-- **The hosted start state satisfies the invariant.** -/
theorem inv_hostedStart : Refine.Inv hostedStart := by
  sorry

/-- **Every loaded program starts in a state of the invariant**, so `run_refines_manual` applies to
`run (load p) n` for every `n`. -/
theorem inv_load (p : Program) : Refine.Inv (load p) := by
  sorry

/-! ## Wave 10: the IEEE rounding core is proved correct

`Mips.Fp.Format.RoundSpec` (`Semantics/FpOpsSpec.lean`) is the IEEE 754 definition the manual
references, written from the manual and not from the core: the values of the encodings
(`Format.value`, Table 6.2), correct rounding to the representable values in each direction
(`CorrectlyRounded`, Table 6.10, ties to even), overflow and its result (§6.7.2.5, Table 6.14),
inexact (§6.7.2.6), tininess after rounding (§6.7.2.3). The exact result is a `Cut` (its order
relation with the rationals) so that `√x` can be stated. -/

/-- **The value of a finite encoding is the core's exact value**: `Mips.Fp.Format.value` (the
manual's Table 6.2, MD00082 Vol I-A Rev 6.01 p.80-81: `(-1)^s × 2^E × 1.f`, `(-1)^s × 2^E_min × 0.f`)
of every `width`-bit pattern that is not ±∞/NaN is the rational value of `toExact`, the exact value
the arithmetic of the core starts from. -/
theorem value_eq_toExact (f : Mips.Fp.Format) (n : Nat) (hn : n < 2 ^ f.width)
    (he : f.expField n ≠ f.expMax) : f.value n = some (f.toExact n).toRat := by
  sorry

/-- **The rounding core is correct for binary32** (Wave 10; FCSR.FS = 0): for every nonzero exact
value, `roundCore` delivers what `Mips.Fp.Format.RoundSpec` requires: the value correctly rounded in
direction `rm` (MD00082 Vol I-A Rev 6.01 Table 6.10, p.95; ties to even), overflow per §6.7.2.5 with
the Table 6.14 result (p.100-102), the sign of the exact value, inexact iff the rounded value is not
the exact one (§6.7.2.6), tininess after rounding (§6.7.2.3, p.101). -/
theorem roundCore_correct_binary32 (rm : Mips.Fp.RoundingMode) (w : Mips.Fp.Exact) (hw : w.sig ≠ 0) :
    Mips.Fp.binary32.RoundSpec rm (Mips.Fp.Cut.ofRat w.toRat) (Mips.Fp.binary32.roundCore rm false w) := by
  sorry

/-- **The rounding core is correct for binary64** (as `roundCore_correct_binary32`). -/
theorem roundCore_correct_binary64 (rm : Mips.Fp.RoundingMode) (w : Mips.Fp.Exact) (hw : w.sig ≠ 0) :
    Mips.Fp.binary64.RoundSpec rm (Mips.Fp.Cut.ofRat w.toRat) (Mips.Fp.binary64.roundCore rm false w) := by
  sorry

/-- **Without overflow the delivered value is correctly rounded to the format's finite values**
(`Mips.Fp.Format.Representable`, the values of the encodings), with the same ties-to-even rule. -/
theorem roundSpec_representable (f : Mips.Fp.Format) {rm : Mips.Fp.RoundingMode} {c : Mips.Fp.Cut}
    {R : Mips.Fp.Format.Rounded} (h : f.RoundSpec rm c R) (hov : R.overflow = false) :
    ∃ r, f.value R.bits = some r ∧ Mips.Fp.CorrectlyRounded f.Representable f.UnboundedEven rm c r := by
  sorry

/-- **Flush to zero (FCSR.FS = 1), tiny case**: a nonzero exact value strictly between `±2^E_min`
(tininess before rounding, MD00082 Vol I-A Rev 6.01 §6.7.2.4, p.102) becomes the zero of its sign,
reported tiny and inexact ("Flushing of tiny non-zero results causes Inexact and Underflow exceptions
to be signaled"). -/
theorem roundCore_flush_tiny (f : Mips.Fp.Format) (rm : Mips.Fp.RoundingMode) (w : Mips.Fp.Exact)
    (hw : w.sig ≠ 0) (ht : w.toRat.abs < (2 : Rat) ^ f.emin) :
    f.roundCore rm true w = ⟨f.zero w.sign, false, true, true⟩ := by
  sorry

/-- **Flush to zero (FCSR.FS = 1), other values**: rounded as with FS = 0. -/
theorem roundCore_flush_normal (f : Mips.Fp.Format) (rm : Mips.Fp.RoundingMode) (w : Mips.Fp.Exact)
    (hw : w.sig ≠ 0) (ht : ¬ w.toRat.abs < (2 : Rat) ^ f.emin) :
    f.roundCore rm true w = f.roundCore rm false w := by
  sorry

/-- **`ADD.S` is correctly rounded** (Wave 10; FCSR.FS = 0): for finite operands whose exact
sum is nonzero, the result and the flags are those of a rounding record meeting
`Mips.Fp.Format.RoundSpec` for the exact sum. -/
theorem f32Add_correct (e : Mips.Fp.Env) (he : e.flush = false) {a b : BitVec 32} {x y : Rat}
    (ha : Mips.Fp.binary32.value a.toNat = some x) (hb : Mips.Fp.binary32.value b.toNat = some y) (hxy : x + y ≠ 0) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary32.RoundSpec e.rm (Mips.Fp.Cut.ofRat (x + y)) R ∧
      Mips.Fp.f32Add e a b = (BitVec.ofNat 32 R.bits, R.flags e.enables) := by
  sorry

/-- **`SUB.S` is correctly rounded** (Wave 10; FCSR.FS = 0): for finite operands whose exact
difference is nonzero, the result and the flags are those of a rounding record meeting
`Mips.Fp.Format.RoundSpec` for the exact difference. -/
theorem f32Sub_correct (e : Mips.Fp.Env) (he : e.flush = false) {a b : BitVec 32} {x y : Rat}
    (ha : Mips.Fp.binary32.value a.toNat = some x) (hb : Mips.Fp.binary32.value b.toNat = some y) (hxy : x - y ≠ 0) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary32.RoundSpec e.rm (Mips.Fp.Cut.ofRat (x - y)) R ∧
      Mips.Fp.f32Sub e a b = (BitVec.ofNat 32 R.bits, R.flags e.enables) := by
  sorry

/-- **`MUL.S` is correctly rounded** (Wave 10; FCSR.FS = 0): for finite operands whose exact
product is nonzero, the result and the flags are those of a rounding record meeting
`Mips.Fp.Format.RoundSpec` for the exact product. -/
theorem f32Mul_correct (e : Mips.Fp.Env) (he : e.flush = false) {a b : BitVec 32} {x y : Rat}
    (ha : Mips.Fp.binary32.value a.toNat = some x) (hb : Mips.Fp.binary32.value b.toNat = some y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary32.RoundSpec e.rm (Mips.Fp.Cut.ofRat (x * y)) R ∧
      Mips.Fp.f32Mul e a b = (BitVec.ofNat 32 R.bits, R.flags e.enables) := by
  sorry

/-- **`DIV.S` is correctly rounded** (Wave 10; FCSR.FS = 0): for finite operands whose exact
quotient is nonzero, the result and the flags are those of a rounding record meeting
`Mips.Fp.Format.RoundSpec` for the exact quotient. -/
theorem f32Div_correct (e : Mips.Fp.Env) (he : e.flush = false) {a b : BitVec 32} {x y : Rat}
    (ha : Mips.Fp.binary32.value a.toNat = some x) (hb : Mips.Fp.binary32.value b.toNat = some y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary32.RoundSpec e.rm (Mips.Fp.Cut.ofRat (x / y)) R ∧
      Mips.Fp.f32Div e a b = (BitVec.ofNat 32 R.bits, R.flags e.enables) := by
  sorry

/-- **`SQRT.S` is correctly rounded** (Wave 10; FCSR.FS = 0): for finite operands whose exact
square root is nonzero, the result and the flags are those of a rounding record meeting
`Mips.Fp.Format.RoundSpec` for the exact square root `√x` (`Mips.Fp.Cut.sqrt`). -/
theorem f32Sqrt_correct (e : Mips.Fp.Env) (he : e.flush = false) {a : BitVec 32} {x : Rat}
    (ha : Mips.Fp.binary32.value a.toNat = some x) (hx : 0 < x) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary32.RoundSpec e.rm (Mips.Fp.Cut.sqrt x) R ∧
      Mips.Fp.f32Sqrt e a = (BitVec.ofNat 32 R.bits, R.flags e.enables) := by
  sorry

/-- **`ADD.D` is correctly rounded** (Wave 10; FCSR.FS = 0): for finite operands whose exact
sum is nonzero, the result and the flags are those of a rounding record meeting
`Mips.Fp.Format.RoundSpec` for the exact sum. -/
theorem f64Add_correct (e : Mips.Fp.Env) (he : e.flush = false) {a b : BitVec 64} {x y : Rat}
    (ha : Mips.Fp.binary64.value a.toNat = some x) (hb : Mips.Fp.binary64.value b.toNat = some y) (hxy : x + y ≠ 0) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary64.RoundSpec e.rm (Mips.Fp.Cut.ofRat (x + y)) R ∧
      Mips.Fp.f64Add e a b = (BitVec.ofNat 64 R.bits, R.flags e.enables) := by
  sorry

/-- **`SUB.D` is correctly rounded** (Wave 10; FCSR.FS = 0): for finite operands whose exact
difference is nonzero, the result and the flags are those of a rounding record meeting
`Mips.Fp.Format.RoundSpec` for the exact difference. -/
theorem f64Sub_correct (e : Mips.Fp.Env) (he : e.flush = false) {a b : BitVec 64} {x y : Rat}
    (ha : Mips.Fp.binary64.value a.toNat = some x) (hb : Mips.Fp.binary64.value b.toNat = some y) (hxy : x - y ≠ 0) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary64.RoundSpec e.rm (Mips.Fp.Cut.ofRat (x - y)) R ∧
      Mips.Fp.f64Sub e a b = (BitVec.ofNat 64 R.bits, R.flags e.enables) := by
  sorry

/-- **`MUL.D` is correctly rounded** (Wave 10; FCSR.FS = 0): for finite operands whose exact
product is nonzero, the result and the flags are those of a rounding record meeting
`Mips.Fp.Format.RoundSpec` for the exact product. -/
theorem f64Mul_correct (e : Mips.Fp.Env) (he : e.flush = false) {a b : BitVec 64} {x y : Rat}
    (ha : Mips.Fp.binary64.value a.toNat = some x) (hb : Mips.Fp.binary64.value b.toNat = some y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary64.RoundSpec e.rm (Mips.Fp.Cut.ofRat (x * y)) R ∧
      Mips.Fp.f64Mul e a b = (BitVec.ofNat 64 R.bits, R.flags e.enables) := by
  sorry

/-- **`DIV.D` is correctly rounded** (Wave 10; FCSR.FS = 0): for finite operands whose exact
quotient is nonzero, the result and the flags are those of a rounding record meeting
`Mips.Fp.Format.RoundSpec` for the exact quotient. -/
theorem f64Div_correct (e : Mips.Fp.Env) (he : e.flush = false) {a b : BitVec 64} {x y : Rat}
    (ha : Mips.Fp.binary64.value a.toNat = some x) (hb : Mips.Fp.binary64.value b.toNat = some y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary64.RoundSpec e.rm (Mips.Fp.Cut.ofRat (x / y)) R ∧
      Mips.Fp.f64Div e a b = (BitVec.ofNat 64 R.bits, R.flags e.enables) := by
  sorry

/-- **`SQRT.D` is correctly rounded** (Wave 10; FCSR.FS = 0): for finite operands whose exact
square root is nonzero, the result and the flags are those of a rounding record meeting
`Mips.Fp.Format.RoundSpec` for the exact square root `√x` (`Mips.Fp.Cut.sqrt`). -/
theorem f64Sqrt_correct (e : Mips.Fp.Env) (he : e.flush = false) {a : BitVec 64} {x : Rat}
    (ha : Mips.Fp.binary64.value a.toNat = some x) (hx : 0 < x) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary64.RoundSpec e.rm (Mips.Fp.Cut.sqrt x) R ∧
      Mips.Fp.f64Sqrt e a = (BitVec.ofNat 64 R.bits, R.flags e.enables) := by
  sorry

/-! ## Wave 11: every FP operand, the conversions, the compares, the FCSR

The reference definitions extend `Semantics/FpOpsSpec.lean` (definitions only, written from MD00082
Vol I-A Rev 6.01 ch.6 with `FIR.Has2008 = 0` and the MD00086 Vol II-A Rev 6.06 instruction pages):
the classes of an encoding (`Format.datum`, `IsSNaN`/`IsQNaN`, Table 6.2), the new QNaN (Table 6.3),
the NaN rule (`NaNResult`, §6.3.1.4-5), the signaled exceptions (`Signaled`, §6.7.2.3/5/6), rounding
under the whole FCSR including flush to zero (`RoundEnvSpec`, §6.7.2.4), each operation on every
operand (`AddSpec`, `MulSpec`, `DivSpec`, `SqrtSpec`, `SignOpSpec`, `ConvertSpec`, `WidenSpec`,
`FromIntSpec`, `ExactSpec`, `ToWordSpec`, `CompareSpec` with the 16-row `condTable`), the FCSR
update (`FcsrSpec`, §6.7.1, CheckFPException) and the multiply-add family as separate operations
(`MaddSpec`). -/

/-- **Table 6.3 (MD00082 Vol I-A Rev 6.01 p.82), single**: the reference `Format.newQNaN` is `0x7fbf ffff`. -/
theorem newQNaN_binary32 : Mips.Fp.binary32.newQNaN = 0x7FBFFFFF := by
  sorry

/-- **Table 6.3, double**: the reference `Format.newQNaN` is `0x7ff7 ffff ffff ffff`. -/
theorem newQNaN_binary64 : Mips.Fp.binary64.newQNaN = 0x7FF7FFFFFFFFFFFF := by
  sorry

/-- **The NaN pin** (SPEC-NOTES §9 item 13): with a quiet NaN among the operands the model returns the
first one in operand order. `NaNResult` allows any operand QNaN; this names the model's choice. -/
theorem nanResult_first (f : Mips.Fp.Format) (ops : List Nat) (q : Nat)
    (h : ops.find? (fun x => f.isQNaN x) = some q) : f.nanResult ops = q := by
  sorry

/-- **`ADD.S` on every operand** (Wave 11; MD00086 Vol II-A Rev 6.06, ADD.fmt p.34): for all
encodings (NaN, ±∞, ±0, finite) and every FCSR environment `e` (rounding mode, Enables, FS), the
result encoding and the signaled exceptions meet `Mips.Fp.Format.AddSpec` (`Semantics/FpOpsSpec.lean`). -/
theorem f32Add_spec (e : Mips.Fp.Env) (a b : BitVec 32) :
    Mips.Fp.binary32.AddSpec e false a.toNat b.toNat
      ((Mips.Fp.f32Add e a b).1.toNat, (Mips.Fp.f32Add e a b).2) := by
  sorry

/-- **`SUB.S` on every operand** (Wave 11; MD00086 Vol II-A Rev 6.06, SUB.fmt p.389): for all
encodings (NaN, ±∞, ±0, finite) and every FCSR environment `e` (rounding mode, Enables, FS), the
result encoding and the signaled exceptions meet `Mips.Fp.Format.AddSpec` (`Semantics/FpOpsSpec.lean`). -/
theorem f32Sub_spec (e : Mips.Fp.Env) (a b : BitVec 32) :
    Mips.Fp.binary32.AddSpec e true a.toNat b.toNat
      ((Mips.Fp.f32Sub e a b).1.toNat, (Mips.Fp.f32Sub e a b).2) := by
  sorry

/-- **`MUL.S` on every operand** (Wave 11; MD00086 Vol II-A Rev 6.06, MUL.fmt p.302): for all
encodings (NaN, ±∞, ±0, finite) and every FCSR environment `e` (rounding mode, Enables, FS), the
result encoding and the signaled exceptions meet `Mips.Fp.Format.MulSpec` (`Semantics/FpOpsSpec.lean`). -/
theorem f32Mul_spec (e : Mips.Fp.Env) (a b : BitVec 32) :
    Mips.Fp.binary32.MulSpec e a.toNat b.toNat
      ((Mips.Fp.f32Mul e a b).1.toNat, (Mips.Fp.f32Mul e a b).2) := by
  sorry

/-- **`DIV.S` on every operand** (Wave 11; MD00086 Vol II-A Rev 6.06, DIV.fmt p.170): for all
encodings (NaN, ±∞, ±0, finite) and every FCSR environment `e` (rounding mode, Enables, FS), the
result encoding and the signaled exceptions meet `Mips.Fp.Format.DivSpec` (`Semantics/FpOpsSpec.lean`). -/
theorem f32Div_spec (e : Mips.Fp.Env) (a b : BitVec 32) :
    Mips.Fp.binary32.DivSpec e a.toNat b.toNat
      ((Mips.Fp.f32Div e a b).1.toNat, (Mips.Fp.f32Div e a b).2) := by
  sorry

/-- **`SQRT.S` on every operand** (Wave 11; MD00086 Vol II-A Rev 6.06, SQRT.fmt p.382): for all
encodings (NaN, ±∞, ±0, finite) and every FCSR environment `e` (rounding mode, Enables, FS), the
result encoding and the signaled exceptions meet `Mips.Fp.Format.SqrtSpec` (`Semantics/FpOpsSpec.lean`). -/
theorem f32Sqrt_spec (e : Mips.Fp.Env) (a : BitVec 32) :
    Mips.Fp.binary32.SqrtSpec e a.toNat
      ((Mips.Fp.f32Sqrt e a).1.toNat, (Mips.Fp.f32Sqrt e a).2) := by
  sorry

/-- **`ADD.D` on every operand** (Wave 11; MD00086 Vol II-A Rev 6.06, ADD.fmt p.34): for all
encodings (NaN, ±∞, ±0, finite) and every FCSR environment `e` (rounding mode, Enables, FS), the
result encoding and the signaled exceptions meet `Mips.Fp.Format.AddSpec` (`Semantics/FpOpsSpec.lean`). -/
theorem f64Add_spec (e : Mips.Fp.Env) (a b : BitVec 64) :
    Mips.Fp.binary64.AddSpec e false a.toNat b.toNat
      ((Mips.Fp.f64Add e a b).1.toNat, (Mips.Fp.f64Add e a b).2) := by
  sorry

/-- **`SUB.D` on every operand** (Wave 11; MD00086 Vol II-A Rev 6.06, SUB.fmt p.389): for all
encodings (NaN, ±∞, ±0, finite) and every FCSR environment `e` (rounding mode, Enables, FS), the
result encoding and the signaled exceptions meet `Mips.Fp.Format.AddSpec` (`Semantics/FpOpsSpec.lean`). -/
theorem f64Sub_spec (e : Mips.Fp.Env) (a b : BitVec 64) :
    Mips.Fp.binary64.AddSpec e true a.toNat b.toNat
      ((Mips.Fp.f64Sub e a b).1.toNat, (Mips.Fp.f64Sub e a b).2) := by
  sorry

/-- **`MUL.D` on every operand** (Wave 11; MD00086 Vol II-A Rev 6.06, MUL.fmt p.302): for all
encodings (NaN, ±∞, ±0, finite) and every FCSR environment `e` (rounding mode, Enables, FS), the
result encoding and the signaled exceptions meet `Mips.Fp.Format.MulSpec` (`Semantics/FpOpsSpec.lean`). -/
theorem f64Mul_spec (e : Mips.Fp.Env) (a b : BitVec 64) :
    Mips.Fp.binary64.MulSpec e a.toNat b.toNat
      ((Mips.Fp.f64Mul e a b).1.toNat, (Mips.Fp.f64Mul e a b).2) := by
  sorry

/-- **`DIV.D` on every operand** (Wave 11; MD00086 Vol II-A Rev 6.06, DIV.fmt p.170): for all
encodings (NaN, ±∞, ±0, finite) and every FCSR environment `e` (rounding mode, Enables, FS), the
result encoding and the signaled exceptions meet `Mips.Fp.Format.DivSpec` (`Semantics/FpOpsSpec.lean`). -/
theorem f64Div_spec (e : Mips.Fp.Env) (a b : BitVec 64) :
    Mips.Fp.binary64.DivSpec e a.toNat b.toNat
      ((Mips.Fp.f64Div e a b).1.toNat, (Mips.Fp.f64Div e a b).2) := by
  sorry

/-- **`SQRT.D` on every operand** (Wave 11; MD00086 Vol II-A Rev 6.06, SQRT.fmt p.382): for all
encodings (NaN, ±∞, ±0, finite) and every FCSR environment `e` (rounding mode, Enables, FS), the
result encoding and the signaled exceptions meet `Mips.Fp.Format.SqrtSpec` (`Semantics/FpOpsSpec.lean`). -/
theorem f64Sqrt_spec (e : Mips.Fp.Env) (a : BitVec 64) :
    Mips.Fp.binary64.SqrtSpec e a.toNat
      ((Mips.Fp.f64Sqrt e a).1.toNat, (Mips.Fp.f64Sqrt e a).2) := by
  sorry

/-- **`CVT.S.D` on every operand** (MD00086 p.159): `Mips.Fp.Format.ConvertSpec` (SNaN: Invalid and the
new QNaN; QNaN: a QNaN, no exception; ±∞, ±0 kept; otherwise rounded under FCSR.RM/Enables/FS). -/
theorem f64ToF32_spec (e : Mips.Fp.Env) (x : BitVec 64) :
    Mips.Fp.Format.ConvertSpec Mips.Fp.binary64 Mips.Fp.binary32 e x.toNat
      ((Mips.Fp.f64ToF32 e x).1.toNat, (Mips.Fp.f64ToF32 e x).2) := by
  sorry

/-- **`CVT.D.S` on every operand** (MD00086 p.153, "always exact"): `Mips.Fp.Format.WidenSpec` — a
finite operand gives the double of the same value and sign, no exception. -/
theorem f32ToF64_spec (x : BitVec 32) :
    Mips.Fp.Format.WidenSpec Mips.Fp.binary32 Mips.Fp.binary64 x.toNat
      ((Mips.Fp.f32ToF64 x).1.toNat, (Mips.Fp.f32ToF64 x).2) := by
  sorry

/-- **`CVT.S.W` on every word** (MD00086 p.159): `0 ↦ +0`, otherwise the integer rounded under the FCSR
environment (`Mips.Fp.Format.FromIntSpec`). -/
theorem w32ToF32_spec (e : Mips.Fp.Env) (x : BitVec 32) :
    Mips.Fp.binary32.FromIntSpec e x.toInt ((Mips.Fp.w32ToF32 e x).1.toNat, (Mips.Fp.w32ToF32 e x).2) := by
  sorry

/-- **`CVT.D.W` on every word** (MD00086 p.153, "always exact"): the double of value `x.toInt`, sign
bit set iff negative (`+0` for 0), no exception. -/
theorem w32ToF64_spec (x : BitVec 32) :
    Mips.Fp.binary64.ExactSpec (decide (x.toInt < 0)) x.toInt
      ((Mips.Fp.w32ToF64F x).1.toNat, (Mips.Fp.w32ToF64F x).2) := by
  sorry

/-- **`CVT.W.S`, `ROUND/TRUNC/CEIL/FLOOR.W.S`** in every direction `rm`, on every operand (MD00086
p.160, p.342, p.441, p.128, p.186): `Mips.Fp.Format.ToWordSpec` — NaN, ±∞ and values rounding
outside `[-2^31, 2^31-1]` give `2^31-1` with Invalid only; otherwise the value correctly rounded to
an integer in direction `rm` (ties to even), Inexact iff not exact. -/
theorem f32ToW32_spec (rm : Mips.Fp.RoundingMode) (x : BitVec 32) :
    Mips.Fp.binary32.ToWordSpec rm x.toNat (Mips.Fp.f32ToW32 rm x) := by
  sorry

/-- **`CVT.W.D`, `ROUND/TRUNC/CEIL/FLOOR.W.D`** in every direction `rm`, on every operand (MD00086
p.160, p.342, p.441, p.128, p.186): `Mips.Fp.Format.ToWordSpec` — NaN, ±∞ and values rounding
outside `[-2^31, 2^31-1]` give `2^31-1` with Invalid only; otherwise the value correctly rounded to
an integer in direction `rm` (ties to even), Inexact iff not exact. -/
theorem f64ToW32_spec (rm : Mips.Fp.RoundingMode) (x : BitVec 64) :
    Mips.Fp.binary64.ToWordSpec rm x.toNat (Mips.Fp.f64ToW32 rm x) := by
  sorry

/-- **Tables 3.1/3.2 are the Operation's predicate** (MD00086 C.cond.fmt p.111-113): for every
condition field and relation, `(cond2 and less) or (cond1 and equal) or (cond0 and unordered)` is the
table entry, and the "Inv Op Excp. if QNaN?" column is `cond3`. -/
theorem condTable_formula : ∀ (cond : BitVec 4) (r : Mips.Fp.Format.Relation),
    Mips.Fp.fpCompare cond (decide (r = .un)) (decide (r = .lt)) (decide (r = .eq)) =
      Mips.Fp.condHolds cond.toNat r ∧
    (Mips.Fp.condTable cond.toNat).2.2.2.2 = cond.getLsbD 3 := by
  sorry

/-- **`C.cond.S` for all 16 conditions and all operands** (MD00086 p.110-113):
`Mips.Fp.Format.CompareSpec` — the condition bit is the table entry of the operands' relation in
the extended reals (`+0 = -0`, NaN unordered); Invalid iff an SNaN, or `cond3` and a QNaN. -/
theorem f32Compare_spec (cond : BitVec 4) (a b : BitVec 32) :
    Mips.Fp.binary32.CompareSpec cond a.toNat b.toNat (Mips.Fp.f32Compare cond a b) := by
  sorry

/-- **`C.cond.D` for all 16 conditions and all operands** (MD00086 p.110-113):
`Mips.Fp.Format.CompareSpec` — the condition bit is the table entry of the operands' relation in
the extended reals (`+0 = -0`, NaN unordered); Invalid iff an SNaN, or `cond3` and a QNaN. -/
theorem f64Compare_spec (cond : BitVec 4) (a b : BitVec 64) :
    Mips.Fp.binary64.CompareSpec cond a.toNat b.toNat (Mips.Fp.f64Compare cond a b) := by
  sorry

/-- **`ABS.S`** (MD00086 ABS.fmt p.32, `FIR.Has2008 = 0`, arithmetic): `Mips.Fp.Format.SignOpSpec` —
SNaN: Invalid, the new QNaN; QNaN: Invalid, the operand with its sign bit changed (reading A′,
SPEC-NOTES §9 item 21); otherwise the sign bit changed, no exception. -/
theorem f32Abs_spec (x : BitVec 32) :
    Mips.Fp.binary32.SignOpSpec true x.toNat ((Mips.Fp.f32Abs x).1.toNat, (Mips.Fp.f32Abs x).2) := by
  sorry

/-- **`NEG.S`** (MD00086 NEG.fmt p.307, `FIR.Has2008 = 0`, arithmetic): `Mips.Fp.Format.SignOpSpec` —
SNaN: Invalid, the new QNaN; QNaN: Invalid, the operand with its sign bit changed (reading A′,
SPEC-NOTES §9 item 21); otherwise the sign bit changed, no exception. -/
theorem f32Neg_spec (x : BitVec 32) :
    Mips.Fp.binary32.SignOpSpec false x.toNat ((Mips.Fp.f32Neg x).1.toNat, (Mips.Fp.f32Neg x).2) := by
  sorry

/-- **`ABS.D`** (MD00086 ABS.fmt p.32, `FIR.Has2008 = 0`, arithmetic): `Mips.Fp.Format.SignOpSpec` —
SNaN: Invalid, the new QNaN; QNaN: Invalid, the operand with its sign bit changed (reading A′,
SPEC-NOTES §9 item 21); otherwise the sign bit changed, no exception. -/
theorem f64Abs_spec (x : BitVec 64) :
    Mips.Fp.binary64.SignOpSpec true x.toNat ((Mips.Fp.f64Abs x).1.toNat, (Mips.Fp.f64Abs x).2) := by
  sorry

/-- **`NEG.D`** (MD00086 NEG.fmt p.307, `FIR.Has2008 = 0`, arithmetic): `Mips.Fp.Format.SignOpSpec` —
SNaN: Invalid, the new QNaN; QNaN: Invalid, the operand with its sign bit changed (reading A′,
SPEC-NOTES §9 item 21); otherwise the sign bit changed, no exception. -/
theorem f64Neg_spec (x : BitVec 64) :
    Mips.Fp.binary64.SignOpSpec false x.toNat ((Mips.Fp.f64Neg x).1.toNat, (Mips.Fp.f64Neg x).2) := by
  sorry

/-- **The FCSR update of an FP operation** (MD00082 Vol I-A Rev 6.01 §6.7.1 p.99; CheckFPException,
MD00086 §2.2.2.3.3 Figure 2.24 p.23): `Mips.Fp.fpUpdate`, which `step` uses for every FP
arithmetic instruction (`fpFinishS`/`fpFinishD`/`fpFinishCmp`/`fpThen`; the multiply-add family's
completion with the union of its operations' conditions), meets `Mips.Fp.FcsrSpec`:
Cause ← the exceptions (E = 0), trap iff CheckFPException on the new FCSR, Flags |= the exceptions
unless trapping, every other bit unchanged. -/
theorem fpUpdate_spec (fcsr : BitVec 32) (fl : Mips.Fp.Flags) :
    Mips.Fp.FcsrSpec fcsr fl (Mips.Fp.fpUpdate fcsr fl).1 (Mips.Fp.fpUpdate fcsr fl).2 := by
  sorry

/-- **`FcsrSpec` is a complete description**: it determines the new FCSR and the trap decision. -/
theorem fcsrSpec_unique {old : BitVec 32} {fl : Mips.Fp.Flags} {n1 n2 : BitVec 32} {t1 t2 : Bool}
    (h1 : Mips.Fp.FcsrSpec old fl n1 t1) (h2 : Mips.Fp.FcsrSpec old fl n2 t2) : n1 = n2 ∧ t1 = t2 := by
  sorry

/-- **`MADD.S` is "as if separate floating-point" operations "were executed"** (MD00086 MADD.fmt p.256):
`step` yields the state of an outcome allowed by `Mips.Fp.MaddSpec` (kind 0): each step
(multiply, add/subtract, [negate]) meets its own reference; the FCSR is per instruction (Wave 12a,
`Mips.Fp.OpAcc`): after each step Cause is the union of the steps' exception conditions so far (MD00082
Vol I-A Rev 6.01 Table 6.8 `Cause`, p.94) and the trap check is made; a trapping step takes the
Floating-Point exception with that FCSR and the Flags unchanged, else `fd` gets the final value and the
Flags |= the union ("The Cause bits are ORed into the Flag bits if no exception is taken"). -/
theorem maddS_separate (s : State) (w fd fr fs ft : W32) (hfetch : readMemWord s s.pc = some w)
    (hdecode : decode w = some (.maddS fd fr fs ft)) (hpb : s.pendingBranch = none)
    (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    ∃ out : Mips.Fp.FpOutcome Nat, Mips.Fp.MaddSpec Mips.Fp.binary32 (Mips.Fp.envOf s.fcsr) 0 s.fcsr
        (readFpReg s (regIdx fr)).toNat (readFpReg s (regIdx fs)).toNat (readFpReg s (regIdx ft)).toNat out ∧
      step s = timerTick (match out with
        | .trap c => takeException { s with fcsr := c } excCodeFPE
        | .done c v => mkNext s (writeFpReg { s with fcsr := c } (regIdx fd) (BitVec.ofNat 32 v))) := by
  sorry

/-- **`MSUB.S` is "as if separate floating-point" operations "were executed"** (MD00086 MSUB.fmt p.287):
`step` yields the state of an outcome allowed by `Mips.Fp.MaddSpec` (kind 1): each step
(multiply, add/subtract, [negate]) meets its own reference; the FCSR is per instruction (Wave 12a,
`Mips.Fp.OpAcc`): after each step Cause is the union of the steps' exception conditions so far (MD00082
Vol I-A Rev 6.01 Table 6.8 `Cause`, p.94) and the trap check is made; a trapping step takes the
Floating-Point exception with that FCSR and the Flags unchanged, else `fd` gets the final value and the
Flags |= the union ("The Cause bits are ORed into the Flag bits if no exception is taken"). -/
theorem msubS_separate (s : State) (w fd fr fs ft : W32) (hfetch : readMemWord s s.pc = some w)
    (hdecode : decode w = some (.msubS fd fr fs ft)) (hpb : s.pendingBranch = none)
    (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    ∃ out : Mips.Fp.FpOutcome Nat, Mips.Fp.MaddSpec Mips.Fp.binary32 (Mips.Fp.envOf s.fcsr) 1 s.fcsr
        (readFpReg s (regIdx fr)).toNat (readFpReg s (regIdx fs)).toNat (readFpReg s (regIdx ft)).toNat out ∧
      step s = timerTick (match out with
        | .trap c => takeException { s with fcsr := c } excCodeFPE
        | .done c v => mkNext s (writeFpReg { s with fcsr := c } (regIdx fd) (BitVec.ofNat 32 v))) := by
  sorry

/-- **`NMADD.S` is "as if separate floating-point" operations "were executed"** (MD00086 NMADD.fmt p.308):
`step` yields the state of an outcome allowed by `Mips.Fp.MaddSpec` (kind 2): each step
(multiply, add/subtract, [negate]) meets its own reference; the FCSR is per instruction (Wave 12a,
`Mips.Fp.OpAcc`): after each step Cause is the union of the steps' exception conditions so far (MD00082
Vol I-A Rev 6.01 Table 6.8 `Cause`, p.94) and the trap check is made; a trapping step takes the
Floating-Point exception with that FCSR and the Flags unchanged, else `fd` gets the final value and the
Flags |= the union ("The Cause bits are ORed into the Flag bits if no exception is taken"). -/
theorem nmaddS_separate (s : State) (w fd fr fs ft : W32) (hfetch : readMemWord s s.pc = some w)
    (hdecode : decode w = some (.nmaddS fd fr fs ft)) (hpb : s.pendingBranch = none)
    (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    ∃ out : Mips.Fp.FpOutcome Nat, Mips.Fp.MaddSpec Mips.Fp.binary32 (Mips.Fp.envOf s.fcsr) 2 s.fcsr
        (readFpReg s (regIdx fr)).toNat (readFpReg s (regIdx fs)).toNat (readFpReg s (regIdx ft)).toNat out ∧
      step s = timerTick (match out with
        | .trap c => takeException { s with fcsr := c } excCodeFPE
        | .done c v => mkNext s (writeFpReg { s with fcsr := c } (regIdx fd) (BitVec.ofNat 32 v))) := by
  sorry

/-- **`NMSUB.S` is "as if separate floating-point" operations "were executed"** (MD00086 NMSUB.fmt p.310):
`step` yields the state of an outcome allowed by `Mips.Fp.MaddSpec` (kind 3): each step
(multiply, add/subtract, [negate]) meets its own reference; the FCSR is per instruction (Wave 12a,
`Mips.Fp.OpAcc`): after each step Cause is the union of the steps' exception conditions so far (MD00082
Vol I-A Rev 6.01 Table 6.8 `Cause`, p.94) and the trap check is made; a trapping step takes the
Floating-Point exception with that FCSR and the Flags unchanged, else `fd` gets the final value and the
Flags |= the union ("The Cause bits are ORed into the Flag bits if no exception is taken"). -/
theorem nmsubS_separate (s : State) (w fd fr fs ft : W32) (hfetch : readMemWord s s.pc = some w)
    (hdecode : decode w = some (.nmsubS fd fr fs ft)) (hpb : s.pendingBranch = none)
    (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    ∃ out : Mips.Fp.FpOutcome Nat, Mips.Fp.MaddSpec Mips.Fp.binary32 (Mips.Fp.envOf s.fcsr) 3 s.fcsr
        (readFpReg s (regIdx fr)).toNat (readFpReg s (regIdx fs)).toNat (readFpReg s (regIdx ft)).toNat out ∧
      step s = timerTick (match out with
        | .trap c => takeException { s with fcsr := c } excCodeFPE
        | .done c v => mkNext s (writeFpReg { s with fcsr := c } (regIdx fd) (BitVec.ofNat 32 v))) := by
  sorry

/-- **`MADD.D` is "as if separate floating-point" operations "were executed"** (MD00086 MADD.fmt p.256):
`step` yields the state of an outcome allowed by `Mips.Fp.MaddSpec` (kind 0): each step
(multiply, add/subtract, [negate]) meets its own reference; the FCSR is per instruction (Wave 12a,
`Mips.Fp.OpAcc`): after each step Cause is the union of the steps' exception conditions so far (MD00082
Vol I-A Rev 6.01 Table 6.8 `Cause`, p.94) and the trap check is made; a trapping step takes the
Floating-Point exception with that FCSR and the Flags unchanged, else `fd` gets the final value and the
Flags |= the union ("The Cause bits are ORed into the Flag bits if no exception is taken"). -/
theorem maddD_separate (s : State) (w fd fr fs ft : W32) (hfetch : readMemWord s s.pc = some w)
    (hdecode : decode w = some (.maddD fd fr fs ft)) (hpb : s.pendingBranch = none)
    (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    ∃ out : Mips.Fp.FpOutcome Nat, Mips.Fp.MaddSpec Mips.Fp.binary64 (Mips.Fp.envOf s.fcsr) 0 s.fcsr
        (readFpD s fr).toNat (readFpD s fs).toNat (readFpD s ft).toNat out ∧
      step s = timerTick (match out with
        | .trap c => takeException { s with fcsr := c } excCodeFPE
        | .done c v => mkNext s (writeFpD { s with fcsr := c } fd (BitVec.ofNat 64 v))) := by
  sorry

/-- **`MSUB.D` is "as if separate floating-point" operations "were executed"** (MD00086 MSUB.fmt p.287):
`step` yields the state of an outcome allowed by `Mips.Fp.MaddSpec` (kind 1): each step
(multiply, add/subtract, [negate]) meets its own reference; the FCSR is per instruction (Wave 12a,
`Mips.Fp.OpAcc`): after each step Cause is the union of the steps' exception conditions so far (MD00082
Vol I-A Rev 6.01 Table 6.8 `Cause`, p.94) and the trap check is made; a trapping step takes the
Floating-Point exception with that FCSR and the Flags unchanged, else `fd` gets the final value and the
Flags |= the union ("The Cause bits are ORed into the Flag bits if no exception is taken"). -/
theorem msubD_separate (s : State) (w fd fr fs ft : W32) (hfetch : readMemWord s s.pc = some w)
    (hdecode : decode w = some (.msubD fd fr fs ft)) (hpb : s.pendingBranch = none)
    (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    ∃ out : Mips.Fp.FpOutcome Nat, Mips.Fp.MaddSpec Mips.Fp.binary64 (Mips.Fp.envOf s.fcsr) 1 s.fcsr
        (readFpD s fr).toNat (readFpD s fs).toNat (readFpD s ft).toNat out ∧
      step s = timerTick (match out with
        | .trap c => takeException { s with fcsr := c } excCodeFPE
        | .done c v => mkNext s (writeFpD { s with fcsr := c } fd (BitVec.ofNat 64 v))) := by
  sorry

/-- **`NMADD.D` is "as if separate floating-point" operations "were executed"** (MD00086 NMADD.fmt p.308):
`step` yields the state of an outcome allowed by `Mips.Fp.MaddSpec` (kind 2): each step
(multiply, add/subtract, [negate]) meets its own reference; the FCSR is per instruction (Wave 12a,
`Mips.Fp.OpAcc`): after each step Cause is the union of the steps' exception conditions so far (MD00082
Vol I-A Rev 6.01 Table 6.8 `Cause`, p.94) and the trap check is made; a trapping step takes the
Floating-Point exception with that FCSR and the Flags unchanged, else `fd` gets the final value and the
Flags |= the union ("The Cause bits are ORed into the Flag bits if no exception is taken"). -/
theorem nmaddD_separate (s : State) (w fd fr fs ft : W32) (hfetch : readMemWord s s.pc = some w)
    (hdecode : decode w = some (.nmaddD fd fr fs ft)) (hpb : s.pendingBranch = none)
    (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    ∃ out : Mips.Fp.FpOutcome Nat, Mips.Fp.MaddSpec Mips.Fp.binary64 (Mips.Fp.envOf s.fcsr) 2 s.fcsr
        (readFpD s fr).toNat (readFpD s fs).toNat (readFpD s ft).toNat out ∧
      step s = timerTick (match out with
        | .trap c => takeException { s with fcsr := c } excCodeFPE
        | .done c v => mkNext s (writeFpD { s with fcsr := c } fd (BitVec.ofNat 64 v))) := by
  sorry

/-- **`NMSUB.D` is "as if separate floating-point" operations "were executed"** (MD00086 NMSUB.fmt p.310):
`step` yields the state of an outcome allowed by `Mips.Fp.MaddSpec` (kind 3): each step
(multiply, add/subtract, [negate]) meets its own reference; the FCSR is per instruction (Wave 12a,
`Mips.Fp.OpAcc`): after each step Cause is the union of the steps' exception conditions so far (MD00082
Vol I-A Rev 6.01 Table 6.8 `Cause`, p.94) and the trap check is made; a trapping step takes the
Floating-Point exception with that FCSR and the Flags unchanged, else `fd` gets the final value and the
Flags |= the union ("The Cause bits are ORed into the Flag bits if no exception is taken"). -/
theorem nmsubD_separate (s : State) (w fd fr fs ft : W32) (hfetch : readMemWord s s.pc = some w)
    (hdecode : decode w = some (.nmsubD fd fr fs ft)) (hpb : s.pendingBranch = none)
    (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    ∃ out : Mips.Fp.FpOutcome Nat, Mips.Fp.MaddSpec Mips.Fp.binary64 (Mips.Fp.envOf s.fcsr) 3 s.fcsr
        (readFpD s fr).toNat (readFpD s fs).toNat (readFpD s ft).toNat out ∧
      step s = timerTick (match out with
        | .trap c => takeException { s with fcsr := c } excCodeFPE
        | .done c v => mkNext s (writeFpD { s with fcsr := c } fd (BitVec.ofNat 64 v))) := by
  sorry

end Trusted
