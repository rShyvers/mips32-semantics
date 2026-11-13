import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# Syscall — the `syscall` instruction: the System Call exception, always

Constructors: `syscall`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  SYSCALL p.415.

"A system call exception occurs, immediately and unconditionally transferring control to the
exception handler"; Operation: `SignalException(SystemCall)`. The MARS-style print/exit services
are not part of the processor: they are the hosted environment's (`Semantics/Env.lean`), and their
theorems are in `Hosted.lean`.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "syscall".

## Theorems in this file (1)

  `syscall_spec_raw`
-/

set_option maxRecDepth 4000

/-- **`syscall` raises the System Call exception (ExcCode 8)**, whatever `$v0` holds, in or out
of a delay slot (`exceptionEntry_*` say what entry does in each case; in a delay slot `EPC` is
the branch and `Cause.BD = 1`). -/
theorem syscall_spec_raw (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.syscall code)) :
    step s = takeException s excCodeSys := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  unfold execInstr execBody
  simp only [show isBranchLike (Instruction.syscall code) = false from rfl,
    show usesCop1 (Instruction.syscall code) = false from rfl,
    show usesCop0 (Instruction.syscall code) = false from rfl, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte]

/-! ### Satisfiable examples -/

-- Whatever `$v0` holds (here the MARS print-int number 1), the processor takes the System Call
-- exception: `Cause.ExcCode = 8`, `EPC` = the `syscall`, `pc` = the general vector.
#guard (let s := stepIn (prog1Spec (.syscall 0#32))
          (setRegsSpec (initialState textBase) [(2, 1#32), (4, 5#32)])
        causeExcCode s == excCodeSys && s.cp0Epc == textBase && s.pc == exceptionVectorAddr) = true
