import Semantics.Manual.Pseudocode

/-!
# Manual.Ops.Trap — conditional traps, BREAK and SIGRIE (MD00086 Vol II-A Rev 6.06)

Sub-wave 7B S2. The `code` field of the register forms is not used by the Operation ("the code field
is available for use as software parameters", e.g. TEQ, p.416).
-/

namespace Manual.Ops

open Manual

/-- **TEQ rs, rt** — MD00086 Vol II-A Rev 6.06, TEQ, p.416.
```
if GPR[rs] = GPR[rt] then
   SignalException(Trap)
endif
``` -/
def TEQ (rs rt _code : W32) : Pseudo Unit := do
  -- if GPR[rs] = GPR[rt] then SignalException(Trap) endif
  if (← GPR (reg rs)) == (← GPR (reg rt)) then SignalException .Trap else pure ()

/-- **TNE rs, rt** — MD00086 Vol II-A Rev 6.06, TNE, p.438.
```
if GPR[rs] ≠ GPR[rt] then
   SignalException(Trap)
endif
``` -/
def TNE (rs rt _code : W32) : Pseudo Unit := do
  -- if GPR[rs] ≠ GPR[rt] then SignalException(Trap) endif
  if (← GPR (reg rs)) != (← GPR (reg rt)) then SignalException .Trap else pure ()

/-- **TGE rs, rt** — MD00086 Vol II-A Rev 6.06, TGE, p.418 (signed comparison).
```
if GPR[rs] ≥ GPR[rt] then
   SignalException(Trap)
endif
``` -/
def TGE (rs rt _code : W32) : Pseudo Unit := do
  -- if GPR[rs] ≥ GPR[rt] then SignalException(Trap) endif
  if (← GPR (reg rt)).sle (← GPR (reg rs)) then SignalException .Trap else pure ()

/-- **TGEU rs, rt** — MD00086 Vol II-A Rev 6.06, TGEU, p.421 (unsigned comparison).
```
if (0 || GPR[rs]) ≥ (0 || GPR[rt]) then
   SignalException(Trap)
endif
``` -/
def TGEU (rs rt _code : W32) : Pseudo Unit := do
  -- if (0 || GPR[rs]) ≥ (0 || GPR[rt]) then SignalException(Trap) endif
  if (0#1 ++ (← GPR (reg rt))).ule (0#1 ++ (← GPR (reg rs))) then SignalException .Trap else pure ()

/-- **TLT rs, rt** — MD00086 Vol II-A Rev 6.06, TLT, p.434 (signed comparison).
```
if GPR[rs] < GPR[rt] then
   SignalException(Trap)
endif
``` -/
def TLT (rs rt _code : W32) : Pseudo Unit := do
  -- if GPR[rs] < GPR[rt] then SignalException(Trap) endif
  if (← GPR (reg rs)).slt (← GPR (reg rt)) then SignalException .Trap else pure ()

/-- **TLTU rs, rt** — MD00086 Vol II-A Rev 6.06, TLTU, p.437 (unsigned comparison).
```
if (0 || GPR[rs]) < (0 || GPR[rt]) then
   SignalException(Trap)
endif
``` -/
def TLTU (rs rt _code : W32) : Pseudo Unit := do
  -- if (0 || GPR[rs]) < (0 || GPR[rt]) then SignalException(Trap) endif
  if (0#1 ++ (← GPR (reg rs))).ult (0#1 ++ (← GPR (reg rt))) then SignalException .Trap else pure ()

/-- **BREAK** — MD00086 Vol II-A Rev 6.06, BREAK, p.109.
```
SignalException(Breakpoint)
```
"A breakpoint exception occurs, immediately and unconditionally transferring control to the exception
handler. The code field is available for use as software parameters". -/
def BREAK (_code : W32) : Pseudo Unit := do
  -- SignalException(Breakpoint)
  SignalException .Breakpoint

-- BEGIN R6-2
/-- **SIGRIE code** — MD00086 Vol II-A Rev 6.06, SIGRIE, p.375 ("MIPS32 Release 6").
```
SignalException(ReservedInstruction)
```
"The 16-bit code field is available for software use" (Restrictions, p.375): the Operation does not
read it. -/
def SIGRIE (_code : W32) : Pseudo Unit :=
  -- SignalException(ReservedInstruction)
  SignalException .ReservedInstruction
-- END R6-2

end Manual.Ops
