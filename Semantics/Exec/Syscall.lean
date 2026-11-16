import Semantics.Exec.Base

/-!
# Exec.Syscall — SYSCALL

The execution of SYSCALL (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of SYSCALL; `none` for every other instruction. -/
def execSyscall (s : State) : Instruction → Option State
  -- `syscall`: "A system call exception occurs, immediately and
  -- unconditionally transferring control to the exception handler";
  -- Operation: `SignalException(SystemCall)` (MD00086 Vol II-A Rev 6.06,
  -- SYSCALL, p.415). The MARS-style print/exit services are not the
  -- processor's: the hosted run (`Semantics/Env.lean`) performs them *instead
  -- of* stepping when it sees a `syscall` selecting one.
  | .syscall _ => some <| takeException s excCodeSys
  | _ => none
