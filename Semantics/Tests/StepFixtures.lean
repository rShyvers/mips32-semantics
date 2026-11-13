import Semantics.Step
import Semantics.Env

/-!
# Fixtures shared by the `step` tests (`Semantics/Tests/Step*Tests.lean`)

Formerly `section TestHelpers` of `Semantics/Step.lean` (there `private`; here in
`namespace StepTest`, opened by each test file).


Per DESIGN.md §5 / CLAUDE.md §5: pure arithmetic helpers (no `Program` or
`State.mem` HashMap access) are checked with `by decide`/`by rfl`. Anything
that steps touches `State.mem` (`Std.HashMap`), which is `cbv_opaque` and not
kernel-reducible, so *every* stepping check uses `#guard` (compiled evaluation).

**What the tests step.** The tests were written as "program `p`, state `s`, one step". Since
`step` fetches from memory, `hstep p s` is one *hosted* step (`Semantics/Env.lean`'s `hostStep`,
services on, image `p`) of `s` with `p` written into its memory (`loadImage`): the next processor
state, or a stop of the hosted run (`exit`, `unhandledException`, `noInstruction`). That is
exactly the old `step p s` behaviour for every test that does not store into the program's own
words. `trun` is the hosted run in the same way.
-/

namespace StepTest


def regs0 : State := initialState textBase

def setRegs (s : State) (kvs : List (Fin 32 × W32)) : State :=
  kvs.foldl (fun acc kv => writeReg acc kv.1 kv.2) s

def setFpRegs (s : State) (kvs : List (Fin 32 × W32)) : State :=
  kvs.foldl (fun acc kv => writeFpReg acc kv.1 kv.2) s

def prog1 (instr : Instruction) : Program :=
  (∅ : Program).insert textBase (encode instr)

def progAt (addr : W32) (instr : Instruction) : Program :=
  (∅ : Program).insert addr (encode instr)

def buildProg (base : W32) (instrs : List Instruction) : Program :=
  instrs.zipIdx.foldl (fun acc (instr, i) => acc.insert (base + BitVec.ofNat 32 (4 * i)) (encode instr))
    (∅ : Program)

/-- The two outcomes the tests distinguish: the next processor state, or a stop of the hosted run. -/
inductive Outcome where
  | next (s : State)
  | halt (r : HaltReason)

/-- One hosted step of `s` with `p` loaded (see the module docstring). -/
def hstep (p : Program) (s : State) : Outcome :=
  match hostStep { image := p } { machine := loadImage p s } with
  | .next h => .next h.machine
  | .halt r => .halt r

/-- The output a single hosted step appends (`none` if the run stopped). -/
def hstepOut (p : Program) (s : State) : Option String :=
  match hostStep { image := p } { machine := loadImage p s } with
  | .next h => some h.out
  | .halt _ => none

/-- The hosted run of `p` loaded into `s`, for at most `n` steps. -/
def trun (p : Program) (s : State) (n : Nat) : HostedResult :=
  runHosted { image := p } n { machine := loadImage p s }

def stepState (p : Program) (s : State) : Option State :=
  match hstep p s with
  | .next s' => some s'
  | .halt _ => none

def nextRegEq (r : Outcome) (i : Fin 32) (v : W32) : Bool :=
  match r with
  | .next s => readReg s i == v
  | .halt _ => false

def nextPcEq (r : Outcome) (pc : W32) : Bool :=
  match r with
  | .next s => s.pc == pc
  | .halt _ => false

def nextHiLoEq (r : Outcome) (hi lo : W32) : Bool :=
  match r with
  | .next s => s.hi == hi && s.lo == lo
  | .halt _ => false

def nextFpRegEq (r : Outcome) (i : Fin 32) (v : W32) : Bool :=
  match r with
  | .next s => readFpReg s i == v
  | .halt _ => false

def isNext (r : Outcome) : Bool :=
  match r with
  | .next _ => true
  | .halt _ => false

/-- `r` is exception entry (from a state with `EXL = 0`, `BEV = 0`) with
`Cause.ExcCode = code`: at the general vector, `EXL` set, no pending branch. -/
def raises (r : Outcome) (code : W32) : Bool :=
  match r with
  | .next s' => causeExcCode s' == code && s'.pc == exceptionVectorAddr
      && (s'.cp0Status &&& statusExlMask) == statusExlMask && s'.pendingBranch.isNone
  | .halt _ => false

/-- `r` is an Address Error exception entry with the given code (AdEL/AdES)
and `BadVAddr = a`. -/
def raisesAddr (r : Outcome) (code a : W32) : Bool :=
  raises r code && (match r with | .next s' => s'.cp0BadVAddr == a | .halt _ => false)

/-- `r` is a halt with `unhandledException code epc badVAddr`. -/
def isHaltUnhandled (r : Outcome) (code epc badVAddr : W32) : Bool :=
  match r with
  | .halt (.unhandledException c e b) => c == code && e == epc && b == badVAddr
  | _ => false

def isHaltNoInstr (r : Outcome) (pc : W32) : Bool :=
  match r with
  | .halt (.noInstruction pc') => pc' == pc
  | _ => false

def isHaltExit (r : Outcome) : Bool :=
  match r with
  | .halt .exit => true
  | _ => false

/-- `r` is Reserved Instruction taken in a delay slot (from `EXL = 0`): `ExcCode = 10`, `BD = 1`,
`EPC` = the branch at `pc - 4`, at the general vector. -/
def isRiInDelaySlot (r : Outcome) : Bool :=
  match r with
  | .next s' => causeExcCode s' == excCodeRI && s'.pc == exceptionVectorAddr &&
      (s'.cp0Cause &&& causeBdMask) == causeBdMask
  | .halt _ => false

def nextPendingEq (r : Outcome) (pb : Option W32) : Bool :=
  match r with
  | .next s => s.pendingBranch == pb
  | .halt _ => false

def nextLlBitEq (r : Outcome) (b : Bool) : Bool :=
  match r with
  | .next s => s.llBit == b
  | .halt _ => false

/-- Every `State` field except `pc` is unchanged between `s` and `s'`. Used
to confirm a genuinely-no-op instruction (`sync`/`synci`) touches *no*
state at all, not just the few fields any individual existing test happens
to check. -/
def sameStateExceptPc (s s' : State) : Bool :=
  s'.regs == s.regs && s'.hi == s.hi && s'.lo == s.lo && s'.fpRegs == s.fpRegs &&
    s'.fcsr == s.fcsr && s'.mem == s.mem &&
    s'.pendingBranch == s.pendingBranch && s'.llBit == s.llBit &&
    s'.cp0Status == s.cp0Status && s'.cp0Cause == s.cp0Cause && s'.cp0Epc == s.cp0Epc &&
    s'.cp0EBase == s.cp0EBase && s'.llAddr == s.llAddr && s'.cp0BadVAddr == s.cp0BadVAddr

-- `sll $zero, $zero, 0` — the canonical MIPS encoding of `nop` (word
-- `0x00000000`) — used as an inert delay-slot filler instruction below.
def nopInstr : Instruction := .sll 0#32 0#32 0#32

/-- Step once through `instr` placed at `base` (with `nopInstr` as its delay
slot at `base + 4`) from `s`, then step once more through the delay slot:
returns the landing `pc` after both steps, or `none` if either step halts.
Used to exercise the full two-step delay-slot behavior of a taken
branch/jump (SPEC-NOTES §9 item 1). -/
def stepThroughDelaySlot (base : W32) (instr : Instruction) (s : State) : Option W32 :=
  let p := buildProg base [instr, nopInstr]
  match stepState p s with
  | some s1 => match hstep p s1 with
    | .next s2 => some s2.pc
    | .halt _ => none
  | none => none


/-- A state whose `pc` is not word-aligned (the fetch raises Address Error). -/
def misalignedState : State := { (initialState textBase) with pc := textBase + 1#32 }

/-- Step through `p` from `s` exactly `n` times, threading the state;
`none` if any intermediate step halts. Used below to exercise `ll`/`sc`
multi-instruction sequences (ordinary fallthrough, no delay slot involved). -/
def stepN (p : Program) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => (stepState p s).bind (stepN p n)

/-- Data address used by the `ll`/`sc` tests. -/
def llscAddr : W32 := 0x10010000#32

end StepTest
