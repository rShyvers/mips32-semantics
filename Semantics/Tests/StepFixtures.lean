import Semantics.Step

/-!
# Fixtures shared by the `step` tests (`Semantics/Tests/Step*Tests.lean`)

Formerly `section TestHelpers` of `Semantics/Step.lean` (there `private`; here in
`namespace StepTest`, opened by each test file).


Per DESIGN.md §5 / CLAUDE.md §5: pure arithmetic helpers (no `Program` or
`State.mem` HashMap access) are checked with `by decide`/`by rfl`. Anything
that calls `step`/`run` touches `Program` (`Std.HashMap W32 W32`), which is
`cbv_opaque` and not kernel-reducible, so *every* `step`/`run` check below
uses `#guard` (compiled evaluation), because `step` always fetches from
`Program` first. The one exception is the misaligned-fetch case, which
short-circuits before touching the map and so is provable by `decide`.
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

def stepState (p : Program) (s : State) : Option State :=
  match step p s with
  | .next s' => some s'
  | .halt _ => none

def nextRegEq (r : StepResult) (i : Fin 32) (v : W32) : Bool :=
  match r with
  | .next s => readReg s i == v
  | .halt _ => false

def nextPcEq (r : StepResult) (pc : W32) : Bool :=
  match r with
  | .next s => s.pc == pc
  | .halt _ => false

def nextHiLoEq (r : StepResult) (hi lo : W32) : Bool :=
  match r with
  | .next s => s.hi == hi && s.lo == lo
  | .halt _ => false

def nextFpRegEq (r : StepResult) (i : Fin 32) (v : W32) : Bool :=
  match r with
  | .next s => readFpReg s i == v
  | .halt _ => false

def isNext (r : StepResult) : Bool :=
  match r with
  | .next _ => true
  | .halt _ => false

/-- `r` is exception entry (from a state with `EXL = 0`, `BEV = 0`) with
`Cause.ExcCode = code`: at the general vector, `EXL` set, no pending branch. -/
def raises (r : StepResult) (code : W32) : Bool :=
  match r with
  | .next s' => causeExcCode s' == code && s'.pc == exceptionVectorAddr
      && (s'.cp0Status &&& statusExlMask) == statusExlMask && s'.pendingBranch.isNone
  | .halt _ => false

/-- `r` is an Address Error exception entry with the given code (AdEL/AdES)
and `BadVAddr = a`. -/
def raisesAddr (r : StepResult) (code a : W32) : Bool :=
  raises r code && (match r with | .next s' => s'.cp0BadVAddr == a | .halt _ => false)

/-- `r` is a halt with `unhandledException code epc badVAddr`. -/
def isHaltUnhandled (r : StepResult) (code epc badVAddr : W32) : Bool :=
  match r with
  | .halt (.unhandledException c e b) => c == code && e == epc && b == badVAddr
  | _ => false

def isHaltNoInstr (r : StepResult) (pc : W32) : Bool :=
  match r with
  | .halt (.noInstruction pc') => pc' == pc
  | _ => false

def isHaltExit (r : StepResult) : Bool :=
  match r with
  | .halt .exit => true
  | _ => false

def isHaltBranchInDelaySlot (r : StepResult) : Bool :=
  match r with
  | .halt .branchInDelaySlot => true
  | _ => false

def nextPendingEq (r : StepResult) (pb : Option W32) : Bool :=
  match r with
  | .next s => s.pendingBranch == pb
  | .halt _ => false

def nextLlBitEq (r : StepResult) (b : Bool) : Bool :=
  match r with
  | .next s => s.llBit == b
  | .halt _ => false

/-- Every `State` field except `pc` is unchanged between `s` and `s'`. Used
to confirm a genuinely-no-op instruction (`sync`/`synci`) touches *no*
state at all, not just the few fields any individual existing test happens
to check. -/
def sameStateExceptPc (s s' : State) : Bool :=
  s'.regs == s.regs && s'.hi == s.hi && s'.lo == s.lo && s'.fpRegs == s.fpRegs &&
    s'.fcsr == s.fcsr && s'.mem == s.mem && s'.out == s.out &&
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
  | some s1 => match step p s1 with
    | .next s2 => some s2.pc
    | .halt _ => none
  | none => none


/-- A state whose `pc` is not word-aligned (fetch fails before touching the program). -/
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
