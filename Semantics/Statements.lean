import Semantics.Specs.Defs

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
(`Word`, `Types`, `State`, `Instruction`, `FpOps`, `Step`) plus the statement vocabulary of
`Semantics/Specs/Defs.lean` and `Semantics/Specs/WellFormed.lean`. It imports no proof file.

**This is the only Lean file in the project that contains `sorry`.** It is deliberately *not*
imported by `Semantics.lean` or `Checked.lean`, so neither `lake build` of the libraries nor
`lake check` ever sees a `sorry`; `scripts/gate-allow.txt` allow-lists `sorry` for this one path in
the gate's forbidden-construct scan. See `docs/PROOF-NOTES.md`, "The comparator arrangement"
(which also explains why the theorems live in `namespace Trusted` and why a bridging solution
module is needed).

The surface is a deliberate selection: every global theorem (round trip, invariants, exception
entry, fetch/decode failure, delay slots, Coprocessor Unusable, FP trap) and at least one
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

/-- **Global invariant: `$zero` is never changed by a step.** If `step`
produces a next state, register `0` reads the same thing after the step as
before — for **every** instruction, with no side conditions (INSTRUCTION-REF
Global rule 2, "writes to `$zero` are a no-op"). Proof: `step` is
fetch/decode followed by `execInstr`; see `execInstr_zeroKept`. -/
theorem step_preserves_zero_register (p : Program) (s s' : State)
    (hstep : step p s = StepResult.next s') : readReg s' 0 = readReg s 0 := by
  sorry

/-- **Whole-run invariant: `$zero` is the same at the end of any run as at
its start**, for any program, any start state, any step budget. -/
theorem run_preserves_zero_register (p : Program) (s₀ : State) (maxSteps : Nat) :
    readReg (run p s₀ maxSteps).finalState 0 = readReg s₀ 0 := by
  sorry

/-- **`$zero` reads `0` at the end of every run started from
`initialState`.** -/
theorem run_initialState_zero_register (p : Program) (pc : W32) (maxSteps : Nat) :
    readReg (run p (initialState pc) maxSteps).finalState 0 = 0#32 := by
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
theorem step_preserves_wellFormed (p : Program) (s s' : State) (hwf : s.RegFilesWF)
    (hstep : step p s = StepResult.next s') : s'.RegFilesWF := by
  sorry

/-- **Every state reached by `run` from `initialState` is well-formed.** -/
theorem run_initialState_wellFormed (p : Program) (pc : W32) (maxSteps : Nat) :
    (run p (initialState pc) maxSteps).finalState.RegFilesWF := by
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
`hi`/`lo`, memory, output, FP register, `FCSR`, `BadVAddr`, `ErrorEPC`,
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
      (exceptionEntry s code ce).mem = s.mem ∧ (exceptionEntry s code ce).out = s.out ∧
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
theorem step_misaligned_pc (p : Program) (s : State) (h : s.pc.toNat % 4 ≠ 0) :
    step p s = takeAddressException s excCodeAdEL s.pc := by
  sorry

/-- **Running off the program** (model boundary): an aligned `pc` holding
no instruction, when not at the exception vector with `EXL = 1`, halts with
`noInstruction pc`. -/
theorem step_no_instruction (p : Program) (s : State)
    (hfetch : fetchWord p s.pc = none) (haligned : s.pc.toNat % 4 = 0)
    (hvec : atUnhandledVector s = false) :
    step p s = StepResult.halt (.noInstruction s.pc) := by
  sorry

/-- **A word that does not decode** raises Reserved Instruction (ExcCode
10) — unless it lies in a coprocessor's encoding space and that coprocessor
is unusable, in which case Coprocessor Unusable takes precedence (MD00090
Vol III Rev 6.02 §6.2.21, p.99): coprocessor 1 (`isCop1Word`) when
`Status.CU1 = 0`, with `Cause.CE = 1`; coprocessor 2 (`isCop2Word`), which
the model does not have, always, with `Cause.CE = 2`. -/
theorem step_undecodable (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = none) :
    step p s =
      if isCop1Word w && !cu1Enabled s then StepResult.next (exceptionEntry s excCodeCpU 1#32)
      else if isCop2Word w then StepResult.next (exceptionEntry s excCodeCpU 2#32)
      else takeException s excCodeRI := by
  sorry

/-- **A word that does not decode and is in no coprocessor's encoding space
raises Reserved Instruction** (ExcCode 10). -/
theorem step_reserved_instruction (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = none)
    (hc1 : isCop1Word w = false) (hc2 : isCop2Word w = false) :
    step p s = takeException s excCodeRI := by
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
theorem delay_slot_commits_target (p : Program) (s : State) (t w : W32) (instr : Instruction)
    (s' : State)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some instr)
    (hnb : isBranchLike instr = false) (hvec : s.pc + 4#32 ≠ exceptionVector s)
    (h0 : step p { s with pendingBranch := none } = StepResult.next s')
    (hnormal : s'.pc = s.pc + 4#32) :
    step p { s with pendingBranch := some t } = StepResult.next { s' with pc := t } := by
  sorry

/-- **A branch, jump or `eret` in a branch delay slot halts.** The
architecture makes this UNPREDICTABLE; rather than pick a behavior, `step`
reports `HaltReason.branchInDelaySlot` whenever the instruction about to
execute is in a delay slot (`s.pendingBranch = some _` — set by *every*
branch/jump, taken or not) and is itself one of the 24
instructions of `isBranchLike` (`isBranchLikeSpec` is that same
definition): the 12 branches/jumps, the 8 branch-likelies, `bc1t`/`bc1f`,
`eret` and `wait` (SPEC-NOTES §9 item 1; INSTRUCTION-REF Global rule 3). -/
theorem branch_in_delay_slot_halts (p : Program) (s : State) (w : W32) (instr : Instruction)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some instr)
    (hpb : s.pendingBranch.isSome = true) (hbr : isBranchLikeSpec instr = true) :
    step p s = StepResult.halt .branchInDelaySlot := by
  sorry

/-! ## R-type arithmetic

Proved in `Semantics/Specs/` — Arith.lean. -/

/-- **`add` computes the exact sum, or traps exactly on signed overflow.**
This is `step`'s own code, restated with public names: the raw sum is
formed, `addOverflowsSpec` is INSTRUCTION-REF's Java-derived overflow test
("add" section), and the instruction either raises
Integer Overflow (`takeException s excCodeOv`) or writes the sum and advances the program counter by
4. Every other `add`-related theorem is a corollary of this one. -/
theorem add_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.add rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let av := readReg s (regIdxSpec rs)
      let bv := readReg s (regIdxSpec rt)
      let sumBV := av + bv
      if addOverflowsSpec (asSigned av) (asSigned bv) (asSigned sumBV) then
        takeException s excCodeOv
      else
        StepResult.next
          { (writeReg s (regIdxSpec rd) sumBV) with
            pc := (writeReg s (regIdxSpec rd) sumBV).pc + 4#32 } := by
  sorry

/-- **`sub` computes the exact difference, or traps exactly on signed
overflow.** Mirrors `add_spec_raw`; `subOverflowsSpec` is INSTRUCTION-REF's
"sub" overflow test. -/
theorem sub_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sub rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let av := readReg s (regIdxSpec rs)
      let bv := readReg s (regIdxSpec rt)
      let diffBV := av - bv
      if subOverflowsSpec (asSigned av) (asSigned bv) (asSigned diffBV) then
        takeException s excCodeOv
      else
        StepResult.next
          { (writeReg s (regIdxSpec rd) diffBV) with
            pc := (writeReg s (regIdxSpec rd) diffBV).pc + 4#32 } := by
  sorry

/-- **`add` overflow raises Integer Overflow (ExcCode 12), in or out of a
delay slot** — no `pendingBranch` hypothesis. `$rd` is not written
(`exceptionEntry_always`: exception entry changes no general register);
`EPC`/`Cause.BD` follow `exceptionEntry_*`. -/
theorem add_overflow_raises_ov (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.add rs rt rd))
    (hov : addOverflowsSpec (asSigned (readReg s (regIdxSpec rs))) (asSigned (readReg s (regIdxSpec rt)))
      (asSigned (readReg s (regIdxSpec rs) + readReg s (regIdxSpec rt))) = true) :
    step p s = takeException s excCodeOv := by
  sorry

/-- **Overflow does not silently wrap.** A buggy `add` might wrap
`0x7fffffff + 1` to `0x80000000`, write it to `$10` and continue; the real
`add` raises the Integer Overflow exception (ExcCode 12) instead: the step
is exactly exception entry, and exception entry changes no general
register — in particular the destination `$10` is not written. -/
theorem add_overflow_not_wrapped (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.add 8#32 9#32 10#32))
    (hpb : s.pendingBranch = none)
    (ha : readReg s (regIdxSpec 8#32) = 0x7fffffff#32)
    (hb : readReg s (regIdxSpec 9#32) = 1#32) :
    step p s = StepResult.next (exceptionEntry s excCodeOv) ∧
      (exceptionEntry s excCodeOv).regs = s.regs := by
  sorry

/-! ## Immediates

Proved in `Semantics/Specs/` — Immediate.lean. -/

/-- **`addi` computes `$rs + sext16(imm)` exactly, or traps exactly on
signed overflow.** The immediate is sign-extended first (INSTRUCTION-REF
"addi" section), then the same overflow test as `add` applies. -/
theorem addi_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.addi rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let av := readReg s (regIdxSpec rs)
      let bv := signExt16 imm
      let sumBV := av + bv
      if addOverflowsSpec (asSigned av) (asSigned bv) (asSigned sumBV) then
        takeException s excCodeOv
      else
        StepResult.next
          { (writeReg s (regIdxSpec rt) sumBV) with
            pc := (writeReg s (regIdxSpec rt) sumBV).pc + 4#32 } := by
  sorry

/-- **`addi` overflow raises Integer Overflow**, in or out of a delay slot. -/
theorem addi_overflow_raises_ov (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.addi rs rt imm))
    (hov : addOverflowsSpec (asSigned (readReg s (regIdxSpec rs))) (asSigned (signExt16 imm))
      (asSigned (readReg s (regIdxSpec rs) + signExt16 imm)) = true) :
    step p s = takeException s excCodeOv := by
  sorry

/-! ## Shifts

Proved in `Semantics/Specs/` — Shift.lean. -/

/-- **`sll` shifts `$rt` left by the fixed `shamt` field, zero-filling the
vacated low bits.** `shamt` comes straight from the instruction encoding
(INSTRUCTION-REF "sll"), not a register. -/
theorem sll_spec_raw (p : Program) (s : State) (w rd rt shamt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sll rd rt shamt))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< shamt.toNat)) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< shamt.toNat)).pc + 4#32 } := by
  sorry

/-! ## Multiply / divide

Proved in `Semantics/Specs/` — MulDiv.lean. -/

/-- **`mult` forms the exact signed 64-bit product of `$rs` and `$rt`,
splitting it into `hi`/`lo`.** No GPR is written, and `mult` never halts
(INSTRUCTION-REF "mult" section: MARS never traps on multiply overflow —
the full 64-bit result always fits in `hi:lo`). -/
theorem mult_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mult rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
      StepResult.next
        { s with lo := prod64.extractLsb 31 0, hi := prod64.extractLsb 63 32, pc := s.pc + 4#32 } := by
  sorry

/-- **`div` by a nonzero divisor truncates toward zero; the remainder takes
the dividend's sign** (Lean's `Int.tdiv`/`Int.tmod`, matching Java's `/`/`%`
used by MARS — INSTRUCTION-REF "div" section). **`div` by zero leaves `hi`
and `lo` untouched and does not halt** (SPEC-NOTES §9.2 / INSTRUCTION-REF
"div" MARS-note: this is a deliberate MIPS32-spec reading, not a MARS bug).
Both cases always advance the program counter by 4. -/
theorem div_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.div rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      if b == 0 then
        StepResult.next { s with pc := s.pc + 4#32 }
      else
        StepResult.next { s with lo := ofInt32 (a.tdiv b), hi := ofInt32 (a.tmod b), pc := s.pc + 4#32 } := by
  sorry

/-- Corollary of `div_spec_raw`: dividing by `0` leaves `hi`/`lo` exactly as
they were and does not halt — INSTRUCTION-REF "div" MARS-note, SPEC-NOTES
§9.2. -/
theorem div_by_zero_spec (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.div rs rt))
    (hpb : s.pendingBranch = none)
    (hzero : readReg s (regIdxSpec rt) = 0#32) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  sorry

/-! ## Bit operations

Proved in `Semantics/Specs/` — BitOps.lean. -/

/-- **`ext` extracts a `size`-bit field of `$rs` starting at bit `pos`,
zero-extended, into `$rt`** (SPECIAL3 opcode 0x1f, funct 0x00;
INSTRUCTION-REF "ext"). `pos`/`size` are already the semantic values here —
`decode` did the raw-field +-1 arithmetic — so this is pure bit masking,
with no special case for the real `pos + size <= 32` hardware constraint
(matching `Step.lean`'s own documented choice). -/
theorem ext_spec_raw (p : Program) (s : State) (w rt rs pos size : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ext rt rs pos size))
    (hpb : s.pendingBranch = none) :
    step p s =
      let field := (readReg s (regIdxSpec rs) >>> pos.toNat) &&& lowBitsMaskSpec size.toNat
      StepResult.next
        { (writeReg s (regIdxSpec rt) field) with
          pc := (writeReg s (regIdxSpec rt) field).pc + 4#32 } := by
  sorry

/-! ## Loads and stores

Proved in `Semantics/Specs/` — Memory.lean, Atomic.lean, Unaligned.lean. -/

/-- **`lw` composes a big-endian word from memory at `$rs + sext16(offset)`,
or raises Address Error on a misaligned effective address**
(INSTRUCTION-REF "lw" section; SPEC-NOTES §9.3 — the offset is
sign-extended, unlike MARS's own latent zero-extension bug for raw-decoded
binaries). -/
theorem lw_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) v) with
            pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  sorry

/-- Corollary of `lw_spec_raw`: a misaligned effective address raises Address
Error, naming that exact address. -/
theorem lw_misaligned_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none)
    (hmisaligned : (readReg s (regIdxSpec rs) + signExt16 imm).toNat % 4 ≠ 0) :
    step p s = takeAddressException s excCodeAdEL (readReg s (regIdxSpec rs) + signExt16 imm) := by
  sorry

/-- **`sw` stores `$rt` as a big-endian word at `$rs + sext16(offset)` and
clears `llBit`** (any store invalidates a pending `ll`/`sc` pair, so a
subsequent `sc` correctly fails if memory changed underneath it), or raises
Address Error on a misaligned effective address (INSTRUCTION-REF "sw"
section). -/
theorem sw_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemWord s addr (readReg s (regIdxSpec rt)) with
      | none => takeAddressException s excCodeAdES addr
      | some s' =>
        StepResult.next
          { ({ s' with llBit := false }) with
            pc := ({ s' with llBit := false }).pc + 4#32 } := by
  sorry

/-- **`sb` stores the low byte of `$rt` at `$rs + sext16(offset)` and
clears `llBit`** (MD00086 "SB": `StoreMemory(BYTE, GPR[rt] 7..0)`). There is
no alignment requirement, so `sb` never raises an Address Error; exactly
one memory byte changes. Clearing `llBit` is the model's pinned choice for
every store (see `State.llBit`). -/
theorem sb_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sb rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { s with
            mem := s.mem.insert (readReg s (regIdxSpec rs) + signExt16 imm)
              (readReg s (regIdxSpec rt) &&& 0xff#32).toNat.toUInt8
            llBit := false
            pc := s.pc + 4#32 } := by
  sorry

/-- **`ll` loads a word exactly like `lw`, and additionally sets `llBit`
and records its effective address in `llAddr`** — the link state that a
later `sc` checks (INSTRUCTION-REF "ll" section; MD00086 Vol II-A Rev 6.06,
LL, p.223-224). It raises Address Error on a word-misaligned effective
address, exactly like `lw`. -/
theorem ll_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ll rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v =>
        StepResult.next
          { ({ (writeReg s (regIdxSpec rt) v) with llBit := true, llAddr := addr }) with
            pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  sorry

/-- **`sc` is conditional on `llBit` and on its address matching the
preceding `ll`'s, checked before `llBit` is cleared.** The effective address
is computed and alignment-checked unconditionally, just like `sw` (so a
misaligned `sc` raises Address Error regardless of `llBit`). Once the
address is valid: if `s.llBit` was `true` **and** the address equals
`s.llAddr` ("An SC will fail if the aligned address of the SC does not match
that of the preceding LL" — MD00086 Vol II-A Rev 6.06, SC, p.347), the store
commits (`$rt`'s old value is written to memory) and `$rt` is overwritten
with `1` (success); otherwise the store does **not** commit and `$rt` is
overwritten with `0` (failure). Either way `llBit`
ends up `false`. This single theorem states both outcomes together
(mirroring how `beq_spec_raw` states taken/not-taken as one `if`), because
the whole point of `ll`/`sc` is this exact atomic-primitive contract, not
just "some memory operation happened" (INSTRUCTION-REF "sc" section). -/
theorem sc_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sc rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemWord s addr (readReg s (regIdxSpec rt)) with
      | none => takeAddressException s excCodeAdES addr
      | some stored =>
        if s.llBit && s.llAddr == addr then
          StepResult.next
            { ({ (writeReg stored (regIdxSpec rt) 1#32) with llBit := false }) with
              pc := ({ (writeReg stored (regIdxSpec rt) 1#32) with llBit := false }).pc + 4#32 }
        else
          StepResult.next
            { ({ (writeReg s (regIdxSpec rt) 0#32) with llBit := false }) with
              pc := ({ (writeReg s (regIdxSpec rt) 0#32) with llBit := false }).pc + 4#32 } := by
  sorry

/-- **`lwl` ("load word left") merges 1–4 most-significant bytes starting at
`$rs + sext16(offset)` into the most-significant end of `$rt`, leaving
`$rt`'s existing least-significant bytes untouched** — exactly how many
bytes merge depends on `addr.toNat % 4` (4 at `off = 0`, behaving exactly
like a plain `lw`; down to 1 at `off = 3`). Never halts on a misaligned
address, unlike `lw` (INSTRUCTION-REF `lwl` section). -/
theorem lwl_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lwl rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      let off := addr.toNat % 4
      let old := readReg s (regIdxSpec rt)
      let b0 := (readMemByte s addr).getD 0
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
      StepResult.next
        { (writeReg s (regIdxSpec rt) v) with
          pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
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
another pending delay slot; see `branch_in_delay_slot_halts` for that other
case. -/
theorem beq_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  sorry

/-- **`beq`, taken**: when `$rs = $rt`, `beq` schedules
`PC_next + (offset << 2)` as the pending delay-slot transfer and itself
falls through to `PC_next` — it does **not** jump immediately
(INSTRUCTION-REF Global rule 3: real MIPS32 always executes one delay-slot
instruction first). -/
theorem beq_taken_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rs) = readReg s (regIdxSpec rt)) :
    step p s = StepResult.next
      { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  sorry

/-- **`beql`/`bnel` step-level shape**: identical field layout and taken
condition to `beq` (`$rs == $rt`), but the not-taken case skips the delay
slot (`pc := pc + 8`, no pending branch) instead of executing it
(INSTRUCTION-REF "beql / bnel" section). -/
theorem beql_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beql rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 8#32 } := by
  sorry

/-- **A not-taken `beql` skips its delay slot in one `step`**, whatever the
program holds there; `run` for one step lands in the same state. -/
theorem beql_not_taken_squashes_delay_slot (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beql rs rt imm))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt)) :
    step p s = StepResult.next { s with pc := s.pc + 8#32 } ∧
      run p s 1 = RunResult.limitReached { s with pc := s.pc + 8#32 } 1 := by
  sorry

/-- **`j` unconditionally schedules a jump whose top 4 bits come from
`PC_next`, not from `j`'s own address** — the same pseudo-direct target
composition as `jal`, minus the link-register write (INSTRUCTION-REF "j"
section). Like every other jump/branch here, `j` itself falls through to
`PC_next` and never jumps in the same step; the delay-slot instruction
always executes first. -/
theorem j_spec_raw (p : Program) (s : State) (w target : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.j target))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      StepResult.next
        { s with pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) } := by
  sorry

/-- **`jal` links `$ra` to `pc + 8` — past the delay slot, not `PC_next`
(`pc + 4`) — and schedules a jump to a target whose top 4 bits come from
`PC_next`, not from `jal`'s own address** (INSTRUCTION-REF Global rule 3:
real MIPS32's `jal` link value is the address of the instruction *after*
the delay slot, since the delay-slot instruction itself still executes
before control can return to `$ra`). Like `beq`/`bne`, `jal` schedules the
jump via `pendingBranch` and itself falls through to `PC_next`; it never
jumps in the same step. -/
theorem jal_spec_raw (p : Program) (s : State) (w target : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jal target))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      StepResult.next
        { (writeReg s 31 (pcNext + 4#32)) with
          pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) } := by
  sorry

/-- Corollary of `jal_spec_raw`: `$ra` (register 31) reads back exactly
`pc + 8`, i.e. the address of the instruction *after* the delay slot
(`jal`'s own address plus 8), not `pc + 4`. -/
theorem jal_sets_ra (p : Program) (s : State) (w target : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jal target))
    (hpb : s.pendingBranch = none)
    (hsize32 : s.regs.size = 32) :
    ∃ s', step p s = StepResult.next s' ∧ readReg s' (regIdxSpec 31#32) = s.pc + 8#32 := by
  sorry

/-- **`jalr` links `$rd` to `pc + 8` (the same `jal`/`jalr` link-value
convention — past the delay slot) and schedules a jump to the raw value
held in `$rs`, read *before* `$rd` is overwritten** — so `rd == rs`
aliasing is always safe (INSTRUCTION-REF "jalr" section). This is `step`'s
own code restated: the target expression reads `$rs` from the original `s`,
not from the just-written state, exactly matching the "If `rd == rs`..."
paragraph in the spec. -/
theorem jalr_spec_raw (p : Program) (s : State) (w rs rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jalr rs rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      StepResult.next
        { (writeReg s (regIdxSpec rd) (pcNext + 4#32)) with
          pc := pcNext, pendingBranch := some (readReg s (regIdxSpec rs)) } := by
  sorry

/-! ## Traps, `break`, `syscall`

Proved in `Semantics/Specs/` — Trap.lean, Syscall.lean. -/

/-- **`teq` traps iff `$rs == $rt`**, taking the shared coprocessor-0
exception with `excCode = excCodeTr`; otherwise it is a complete no-op
beyond the ordinary fallthrough to `pc + 4#32` — no CP0 state touched at
all (INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu" section). -/
theorem teq_spec_raw (p : Program) (s : State) (w rs rt code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.teq rs rt code))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  sorry

/-- **`break` unconditionally raises the Breakpoint exception** (ExcCode
9) — in any state, in or out of a delay slot. What `takeException` does to
`EPC`/`Cause`/`Status`/`pc`/`pendingBranch` is stated once, in `Exception.lean`
(`exceptionEntry_*`) (INSTRUCTION-REF "break" section). -/
theorem break_spec_raw (p : Program) (s : State) (w code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.break code)) :
    step p s = takeException s excCodeBp := by
  sorry

/-- **`syscall` dispatches on `$v0` (register 2) and implements exactly
four services** (INSTRUCTION-REF syscall section), every other service
number raising the architectural Syscall exception (ExcCode 8) — the
four services are the model's environment-call convention (SPEC-NOTES §9):

* `1` (`PrintInt`): append the signed decimal rendering of `$a0` to `out`;
* `4` (`PrintString`): append the NUL-terminated string at address `$a0`
  (scan bounded by `printStringFuelSpec` bytes) to `out`;
* `10` (`Exit`): halt with `HaltReason.exit`;
* `11` (`PrintChar`): append the character whose code is the low byte of
  `$a0` to `out`.

The three printing services change nothing but `out` and advance `pc` by 4
(given no delay-slot transfer is pending, as in every other `_spec_raw`
theorem). -/
theorem syscall_spec_raw (p : Program) (s : State) (w code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.syscall code))
    (hpb : s.pendingBranch = none) :
    step p s =
      match (readReg s (regIdxSpec 2#32)).toNat with
      | 1 =>
        StepResult.next
          { s with out := s.out ++ toString (asSigned (readReg s (regIdxSpec 4#32))),
                   pc := s.pc + 4#32 }
      | 4 =>
        StepResult.next
          { s with out := s.out ++ readCStringSpec s (readReg s (regIdxSpec 4#32)) printStringFuelSpec,
                   pc := s.pc + 4#32 }
      | 10 => StepResult.halt .exit
      | 11 =>
        StepResult.next
          { s with out := s.out ++ String.singleton
                     (Char.ofNat ((readReg s (regIdxSpec 4#32) &&& 0xff#32).toNat)),
                   pc := s.pc + 4#32 }
      | _ => takeException s excCodeSys := by
  sorry

/-! ## Coprocessor 0

Proved in `Semantics/Specs/` — Cp0.lean. -/

/-- **`mfc0` reads a modeled CP0 register `(rd, sel)` into GPR `$rt`**:
`(8,0)` BadVAddr, `(12,0)` Status, `(13,0)` Cause, `(14,0)` EPC, `(15,0)`
PRId, `(15,1)` EBase, `(16,0)` Config, `(16,1)` Config1, `(30,0)` ErrorEPC.
`decode` produces `mfc0` only for these; for any other pair (reachable only
through a hand-built `Instruction`) the step raises Reserved Instruction,
which is also what the undecodable word does. User mode is not modeled, so
Coprocessor Unusable is never raised. -/
theorem mfc0_spec_raw (p : Program) (s : State) (w rt rd sel : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mfc0 rt rd sel))
    (hpb : s.pendingBranch = none) :
    step p s =
      let read (v : W32) : StepResult :=
        StepResult.next
          { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }
      match rd.toNat, sel.toNat with
      | 8, 0 => read s.cp0BadVAddr
      | 12, 0 => read s.cp0Status
      | 13, 0 => read s.cp0Cause
      | 14, 0 => read s.cp0Epc
      | 15, 0 => read 0x00010000#32
      | 15, 1 => read ((s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32)
      | 16, 0 => read 0x80008402#32
      | 16, 1 => read 0x00000001#32
      | 30, 0 => read s.cp0ErrorEpc
      | _, _ => takeException s excCodeRI := by
  sorry

/-- **`mtc0` writes GPR `$rt` into a modeled CP0 register, through that
register's write mask.** `Status` (12,0) keeps only `statusWriteMask` (IE,
EXL, ERL, IM7..0, BEV, CU1; every other bit reads as zero). `Cause` (13,0)
changes only `causeWriteMask` (DC, IV, IP1..0) and keeps `BD`, `CE`,
`ExcCode` and everything else. `EPC` (14,0) and `ErrorEPC` (30,0) are fully
writable. `EBase` (15,1) takes bits 29..12 of the written value under the
fixed bits 31..30 = `10`. `BadVAddr` (8,0), `PRId` (15,0), `Config` (16,0)
and `Config1` (16,1) are read-only: the write is ignored. Any other pair
raises Reserved Instruction, as for `mfc0_spec_raw`. -/
theorem mtc0_spec_raw (p : Program) (s : State) (w rt rd sel : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mtc0 rt rd sel))
    (hpb : s.pendingBranch = none) :
    step p s =
      match rd.toNat, sel.toNat with
      | 8, 0 => StepResult.next { s with pc := s.pc + 4#32 }
      | 12, 0 =>
        StepResult.next
          { s with cp0Status := readReg s (regIdxSpec rt) &&& statusWriteMask, pc := s.pc + 4#32 }
      | 13, 0 =>
        StepResult.next
          { s with
              cp0Cause := (s.cp0Cause &&& ~~~causeWriteMask) |||
                (readReg s (regIdxSpec rt) &&& causeWriteMask)
              pc := s.pc + 4#32 }
      | 14, 0 => StepResult.next { s with cp0Epc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | 15, 0 => StepResult.next { s with pc := s.pc + 4#32 }
      | 15, 1 =>
        StepResult.next
          { s with
              cp0EBase := (readReg s (regIdxSpec rt) &&& 0x3ffff000#32) ||| 0x80000000#32
              pc := s.pc + 4#32 }
      | 16, 0 => StepResult.next { s with pc := s.pc + 4#32 }
      | 16, 1 => StepResult.next { s with pc := s.pc + 4#32 }
      | 30, 0 =>
        StepResult.next { s with cp0ErrorEpc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | _, _ => takeException s excCodeRI := by
  sorry

/-- **`eret`** (MD00086 "ERET"), executed outside a delay slot:
`if Status.ERL = 1 then PC ← ErrorEPC, ERL ← 0 else PC ← EPC, EXL ← 0`,
and **always `LLbit ← 0`**. It has no delay slot of its own: `pc` is set in
this very step. -/
theorem eret_spec_raw (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none) :
    step p s =
      if s.cp0Status &&& statusErlMask != 0#32 then
        StepResult.next
          { s with pc := s.cp0ErrorEpc, cp0Status := s.cp0Status &&& ~~~statusErlMask, llBit := false }
      else
        StepResult.next
          { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask, llBit := false } := by
  sorry

/-! ## Floating point

Proved in `Semantics/Specs/` — FpuCommon.lean and the other Fpu*.lean files. -/

/-- **Coprocessor Unusable.** Any instruction that needs coprocessor 1
(`usesCop1`: every COP1/COP1X instruction, `lwc1`/`swc1`/`ldc1`/`sdc1`,
`movf`/`movt`) executed with `Status.CU1 = 0` raises Coprocessor Unusable and
does nothing else (MD00090 Vol III Rev 6.02 §6.2.22, p.100). -/
theorem fp_coprocessor_unusable (p : Program) (s : State) (w : W32) (instr : Instruction)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some instr)
    (huses : usesCop1 instr = true)
    (hnb : isBranchLike instr = false ∨ s.pendingBranch = none)
    (hcu : cu1Enabled s = false) :
    step p s = takeCoprocessorUnusable s := by
  sorry

/-- **The FP trap.** If the operation raised an exception that is enabled in
FCSR, the instruction takes the Floating Point exception: `Cause.ExcCode =
15`, `pc` at the general exception vector, FCSR.Cause = this operation's
exceptions with FCSR.Flags untouched (`fcsrTrapped`) — and **no FP register is
written** (nor any general register or memory). -/
theorem fpCompletesS_trap (s s' : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags)
    (hen : Mips.Fp.fpeEnabled s.fcsr r.2 = true)
    (h : fpCompletesS s fd r = StepResult.next s') :
    causeExcCode s' = 15#32 ∧ s'.fpRegs = s.fpRegs ∧ s'.fcsr = fcsrTrapped s.fcsr r.2 ∧
      s'.regs = s.regs ∧ s'.mem = s.mem ∧ s'.pc = exceptionVector s := by
  sorry

/-- **No trap: result bits and FCSR.** When no enabled exception was raised,
the instruction completes: `FPR[fd]` holds exactly the result bits (given a
32-entry FP register file), FCSR is `raiseFlags` of the old FCSR (Cause =
this operation's exceptions, Flags accumulated), and `pc` advances. -/
theorem fpCompletesS_ok (s s' : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags)
    (hen : Mips.Fp.fpeEnabled s.fcsr r.2 = false) (hsize : s.fpRegs.size = 32)
    (h : fpCompletesS s fd r = StepResult.next s') :
    readFpReg s' (regIdx fd) = r.1 ∧ s'.fcsr = Mips.Fp.raiseFlags s.fcsr r.2 ∧
      s'.pc = s.pc + 4#32 ∧ s'.regs = s.regs := by
  sorry

/-- **`add.s`: `fd ← fs + ft`**, single precision: the result bits and exceptions are
`Mips.Fp.f32Add` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, ADD.fmt, p.34) -/
theorem addS_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.addS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd
        (Mips.Fp.f32Add (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) := by
  sorry

/-- **`add.d`: `fd ← fs + ft`**, double precision: the result bits and exceptions are
`Mips.Fp.f64Add` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, ADD.fmt, p.34) -/
theorem addD_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.addD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesD s fd
        (Mips.Fp.f64Add (Mips.Fp.envOf s.fcsr) (readFpD s fs) (readFpD s ft)) := by
  sorry

/-- **`cvt.w.s`** converts to a 32-bit word rounding **per FCSR.RM**
(MD00086 Vol II-A Rev 6.06, CVT.W.fmt, p.160): `Mips.Fp.f32ToW32 (getRM fcsr)` -/
theorem cvtWS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cvtWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesS s fd (Mips.Fp.f32ToW32 (Mips.Fp.getRM s.fcsr) (readFpReg s (regIdx fs))) := by
  sorry

/-- **`c.cond.s`** writes `FCC[cc]` with predicate `cond` (its low four bits) of the two singles:
`Mips.Fp.f32Compare`, completing per `fpCompletesCmp` (MD00086 Vol II-A Rev 6.06,
C.cond.fmt, p.110-113). `fpCompletesCmp_ok` says only `FCC[cc]` changes -/
theorem cCondS_spec_raw (p : Program) (s : State) (w cond cc fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cCondS cond cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      fpCompletesCmp s cc
        (Mips.Fp.f32Compare (cond.setWidth 4) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) := by
  sorry

/-- **`c.lt.s` (cond = 12) sets `FCC[cc]` iff `fs < ft` and neither is a NaN.** -/
theorem c_lt_s_sets_cc (p : Program) (s s' : State) (w cc fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cCondS 12#32 cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hen : Mips.Fp.fpeEnabled s.fcsr (Mips.Fp.f32Compare Mips.Fp.Cond.lt
      (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))).2 = false)
    (hstep : step p s = StepResult.next s') :
    Mips.Fp.getCC s'.fcsr (ccIdx cc) = true ↔
      Mips.Fp.F32Lt (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)) := by
  sorry

/-- **`movf`** (GPR): `if FCC[cc] = 0 then $rd ← $rs` (MD00086 Vol II-A Rev 6.06, MOVF, p.276) -/
theorem movf_spec_raw (p : Program) (s : State) (w rs cc rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movf rs cc rd))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      if readFcc s cc then StepResult.next { s with pc := s.pc + 4#32 }
      else
        StepResult.next
          { (writeReg s (regIdx rd) (readReg s (regIdx rs))) with
            pc := (writeReg s (regIdx rd) (readReg s (regIdx rs))).pc + 4#32 } := by
  sorry

/-- **`mfc1`**: `$rt ← FPR[fs]`, raw bits -/
theorem mfc1_spec_raw (p : Program) (s : State) (w rt fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mfc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      StepResult.next { (writeReg s (regIdx rt) (readFpReg s (regIdx fs))) with pc := (writeReg s (regIdx rt) (readFpReg s (regIdx fs))).pc + 4#32 } := by
  sorry

/-- **`lwc1`**: `FPR[ft] ← MEM32[$rs + sext(imm)]`; Address Error (AdEL) if not word-aligned -/
theorem lwc1_spec_raw (p : Program) (s : State) (w rs ft imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lwc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      let addr := readReg s (regIdx rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v => StepResult.next { (writeFpReg s (regIdx ft) v) with pc := s.pc + 4#32 } := by
  sorry

/-- **A misaligned `lwc1` raises Address Error (AdEL) on the effective address**; no FP register
is written (`exceptionEntry_always`). Same shape as `lw_misaligned_spec`. -/
theorem lwc1_misaligned_spec (p : Program) (s : State) (w rs ft imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lwc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hmisaligned : (readReg s (regIdx rs) + signExt16 imm).toNat % 4 ≠ 0) :
    step p s = takeAddressException s excCodeAdEL (readReg s (regIdx rs) + signExt16 imm) := by
  sorry

/-- **`cfc1`**: `$rt ←` FP control register `fs` — `Mips.Fp.readControl`: FIR (0), FCCR (25),
FEXR (26), FENR (28), FCSR (31); any other number reads 0 (pin for UNPREDICTABLE)
(MD00086 Vol II-A Rev 6.06, CFC1, p.129-130) -/
theorem cfc1_spec_raw (p : Program) (s : State) (w rt fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cfc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      StepResult.next { (writeReg s (regIdx rt) ((Mips.Fp.readControl s.fcsr fs.toNat).getD 0#32)) with pc := (writeReg s (regIdx rt) ((Mips.Fp.readControl s.fcsr fs.toNat).getD 0#32)).pc + 4#32 } := by
  sorry

/-- **`ctc1`**: FP control register `fs ← $rt` through `Mips.Fp.writeControl`, then
`CheckFPException`: if the new FCSR has a Cause bit whose Enable is set, or Cause.E, the
Floating Point exception is taken **with the register already written**. A register
number the manual leaves UNPREDICTABLE is a no-op (pin)
(MD00086 Vol II-A Rev 6.06, CTC1, p.149-151) -/
theorem ctc1_spec_raw (p : Program) (s : State) (w rt fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ctc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      match Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt)) with
      | none => StepResult.next { s with pc := s.pc + 4#32 }
      | some f =>
        if Mips.Fp.fcsrTrapPending f then takeException { s with fcsr := f } excCodeFPE
        else StepResult.next { s with fcsr := f, pc := s.pc + 4#32 } := by
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
theorem bc1t_spec_raw (p : Program) (s : State) (w cc imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bc1t cc imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step p s =
      if readFcc s cc then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 imm <<< 2)) }
      else StepResult.next { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  sorry

end Trusted
