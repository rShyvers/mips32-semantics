import Semantics.Manual.Pseudocode

/-!
# Manual.Ops.Syscall — SYSCALL (MD00086 Vol II-A Rev 6.06)

Sub-wave 7B S2. The hosted system-call services of `Env.lean` are the environment, not the
architecture: the architecture's SYSCALL is the System Call exception.
-/

namespace Manual.Ops

open Manual

/-- **SYSCALL** — MD00086 Vol II-A Rev 6.06, SYSCALL, p.415.
```
SignalException(SystemCall)
```
"A system call exception occurs, immediately and unconditionally transferring control to the exception
handler." The `code` field is not used by the Operation. -/
def SYSCALL (_code : W32) : Pseudo Unit := do
  -- SignalException(SystemCall)
  SignalException .SystemCall

end Manual.Ops
