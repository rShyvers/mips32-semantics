import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# Syscall — the `syscall` instruction (MARS-compatible services 1, 4, 10, 11; otherwise the Syscall exception)

Constructors: `syscall`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  SYSCALL p.415.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Syscalls (modeled services: 1, 4, 10, 11)".

## Theorems in this file (4)

  `readCStringSpec_eq` `syscall_spec_raw` `syscall1_spec` `syscall10_spec`
-/

set_option maxRecDepth 4000

/-- `readCStringSpec` is `Step.lean`'s `readCString` (definitionally: it is
an abbreviation, not a copy). -/
theorem readCStringSpec_eq (s : State) (addr : W32) (fuel : Nat) :
    readCStringSpec s addr fuel = readCString s addr fuel := rfl

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
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  unfold execInstr execBody
  have h2 : regIdxSpec 2#32 = 2 := by decide
  rw [h2]
  simp only [show isBranchLike (Instruction.syscall code) = false from rfl,
    show usesCop1 (Instruction.syscall code) = false from rfl, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte]
  -- both sides are now a `match` on the same `$v0` value; name it and
  -- compare the two dispatch tables case by case
  generalize (readReg _ 2).toNat = n
  split <;> first | rfl | (split <;> first | rfl | (exfalso; simp_all))

/-- **syscall 1 (`PrintInt`) appends the signed decimal rendering of `$a0`
to `out`, with no trailing newline**, and advances the program counter by 4
(INSTRUCTION-REF "syscall 1 — PrintInt": `Integer.toString`, decimal,
signed; no other state changes). The `hpb` hypothesis (no delay-slot
transfer pending) is required, as for every other `mkNext`-based theorem:
with `s.pendingBranch = some t` the next `pc` is `t`, not `s.pc + 4`. -/
theorem syscall1_spec (p : Program) (s : State) (w code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.syscall code))
    (hv0 : readReg s (regIdxSpec 2#32) = 1#32) (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next { s with out := s.out ++ toString (asSigned (readReg s (regIdxSpec 4#32))), pc := s.pc + 4#32 } := by
  rw [syscall_spec_raw p s w code hfetch hdecode hpb, hv0]; rfl

/-- **syscall 10 (`Exit`) halts the program cleanly**, ignoring every
register — modeled as `HaltReason.exit`, distinct from every error halt
(INSTRUCTION-REF "syscall 10 — Exit"). Holds whether or not a delay-slot
transfer is pending (no `hpb` hypothesis). -/
theorem syscall10_spec (p : Program) (s : State) (w code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.syscall code))
    (hv0 : readReg s (regIdxSpec 2#32) = 10#32) :
    step p s = StepResult.halt .exit := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  unfold execInstr execBody
  have h2 : regIdxSpec 2#32 = 2 := by decide
  rw [h2] at hv0
  simp only [show isBranchLike (Instruction.syscall code) = false from rfl,
    show usesCop1 (Instruction.syscall code) = false from rfl, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte]
  rw [hv0]
  rfl

/-! The syscall proofs unfold `execInstr`, rewrite with the `$v0` hypothesis and compare the two
dispatch tables. (Why `hpb` is a hypothesis: `docs/PROOF-NOTES.md`, "syscall1_spec".) -/

-- Closed weaker version of `syscall1_spec`: a concrete syscall-1 call
-- appends the decimal rendering of `$a0`, with no trailing newline.
#guard (match step (prog1Spec (.syscall 0#32)) (setRegsSpec (initialState textBase) [(2, 1#32), (4, 5#32)]) with
        | .next s => s.out
        | .halt _ => "unreachable") = "5"

-- Closed weaker version of `syscall10_spec`: a concrete syscall-10 call
-- halts with `.exit`.
#guard (match step (prog1Spec (.syscall 0#32)) (setRegsSpec (initialState textBase) [(2, 10#32)]) with
        | .next _ => false
        | .halt r => r == .exit) = true

/-! ### Satisfiable examples -/

-- `syscall1_concrete_example`/`syscall10`: already given above as the
-- closed weaker versions of `syscall1_spec`/`syscall10_spec`.
