import Semantics.Manual.Choices

/-!
# Manual.Pseudocode — the language the Operation sections are written in

MD00086 Vol II-A Rev 6.06 §1.3 (Table 1.1, p.5-6: the symbols) and §2.2 (p.16-26: the functions).
An Operation is a value of `Pseudo α`: it reads and writes the architectural state (`Arch`) in the
order its statements are written ("Each of the high-level language statements in the Operations
section are executed sequentially", §2.2.1, p.16), may signal an exception, which "aborts the
instruction. The instruction operation pseudocode never sees a return from this function call"
(§2.2.2.5.1, p.26), and may schedule `I+1:` effects (`I1`).

`Pseudo` is written out as a plain state-and-error function (not a stack of library monad
transformers) so that running an Operation on a concrete state unfolds by definition. The state at
the point of a `SignalException` is kept: the general exception processing starts from it (an FP
operation writes `FCSR.Cause` and then signals, MD00082 Vol I-A Rev 6.01 §6.7.1, p.99).
-/

namespace Manual

/-- The context of one instruction time: the implementation and the resolution of the manual's
choices. -/
structure Ctx where
  impl : Impl
  oracle : Oracle

/-- The state an Operation runs on: the architectural state, plus what the Operation said about
`PC`: an assignment at time `I` (`pcSet`, e.g. `ERET`), or `I+1:` statements to happen in the
next instruction time (`delay`, branches and jumps). -/
structure Frame where
  arch : Arch
  pcSet : Option W32 := none
  delay : Option Delay := none

/-- How an Operation ended: normally with a value, or by `SignalException`. -/
inductive Result (α : Type) where
  | ok (v : α)
  | signal (e : Exception)

/-- An Operation (or a pseudocode function) returning `α`. -/
abbrev Pseudo (α : Type) : Type := Ctx → Frame → Result α × Frame

instance : Monad Pseudo where
  pure a := fun _ f => (.ok a, f)
  bind m k := fun c f =>
    match m c f with
    | (.ok a, f') => k a c f'
    | (.signal e, f') => (.signal e, f')

namespace Pseudo

/-- Run an Operation. -/
def run {α} (m : Pseudo α) (c : Ctx) (f : Frame) : Result α × Frame := m c f

@[simp] theorem run_pure {α} (a : α) (c : Ctx) (f : Frame) :
    (pure a : Pseudo α).run c f = (.ok a, f) := rfl

/-- The architectural state. -/
def get : Pseudo Arch := fun _ f => (.ok f.arch, f)

/-- Replace the architectural state. -/
def modify (g : Arch → Arch) : Pseudo Unit := fun _ f => (.ok (), { f with arch := g f.arch })

/-- The implementation constants. -/
def impl : Pseudo Impl := fun c f => (.ok c.impl, f)

/-- The oracle. -/
def oracle : Pseudo Oracle := fun c f => (.ok c.oracle, f)

end Pseudo

/-! ## Exceptions (§2.2.2.5, p.26) -/

/-- `SignalException(Exception, argument)` (MD00086 Vol II-A Rev 6.06 §2.2.2.5.1, Figure 2.31, p.26):
"This action results in an exception that aborts the instruction. The instruction operation
pseudocode never sees a return from this function call." -/
def SignalException {α} (e : Exception) : Pseudo α := fun _ f => (.signal e, f)

/-- `I+1:` statements of a branch or jump (§1.3, Table 1.1, p.6): their effect `d` happens in the
next instruction time (`Manual.Cycle`). (Release 6 has no branch-likely instruction, so no `I+1:`
statement calls `NullifyCurrentInstruction()`, §2.2.2.5.4, p.26.) -/
def I1 (d : Delay) : Pseudo Unit := fun _ f => (.ok (), { f with delay := some d })

/-- **Carry out an UNPREDICTABLE or UNDEFINED operation** as the oracle resolved it (`Outcome`):
signal an exception, go on as if nothing were unusual, or replace the architectural state. -/
def resolve (out : Outcome) : Pseudo Unit := fun _ f =>
  match out with
  | .signal e => (.signal e, f)
  | .proceed => (.ok (), f)
  | .arbitrary a => (.ok (), { f with arch := a })

/-- **UNPREDICTABLE with a result the oracle may leave as the ordinary one**: if the oracle resolves
the operation as `.proceed`, the Operation goes on as written (`normal`); otherwise the resolution
(a signalled exception or another architectural state) replaces it. -/
def unpredictableOr (out : Outcome) (normal : Pseudo Unit) : Pseudo Unit :=
  match out with
  | .proceed => normal
  | o => resolve o

/-- `PC ← v` at time `I` (an instruction without a delay slot, e.g. `ERET`). -/
def setPC (v : W32) : Pseudo Unit := fun _ f => (.ok (), { f with pcSet := some v })

/-! ## Registers (Table 1.1, p.5-6) -/

/-- `PC` (Table 1.1, p.6): "During the instruction time of an instruction, this is the address of
the instruction word." -/
def PC : Pseudo W32 := fun _ f => (.ok f.arch.PC, f)

/-- The value of `GPR[x]`: register 0 reads 0 (MD00082 Vol I-A Rev 6.01 §2.8.4: "r0 is hard-wired to a
value of zero"). -/
def readGPR (a : Arch) (x : Fin 32) : W32 := if x = 0 then 0#32 else a.GPR x

/-- `GPR[x]` as an operand (Table 1.1, p.5). -/
def GPR (x : Fin 32) : Pseudo W32 := fun _ f => (.ok (readGPR f.arch x), f)

/-- The state after `GPR[x] ← v`: a write to register 0 has no effect (r0 is hard-wired to zero). -/
def writeGPR (a : Arch) (x : Fin 32) (v : W32) : Arch :=
  if x = 0 then a else { a with GPR := update a.GPR x v }

/-- `GPR[x] ← v`. -/
def setGPR (x : Fin 32) (v : W32) : Pseudo Unit :=
  fun _ f => (.ok (), { f with arch := writeGPR f.arch x v })

/-- A register field of an instruction word (5 bits, raw `W32` in `Instruction`) as a register
number. -/
def reg (w : W32) : Fin 32 := ⟨w.toNat % 32, Nat.mod_lt _ (by decide)⟩

/-! ## Bit strings (Table 1.1, p.5)

`x_{y..z}` is `bits x y z`; `x || y` is `BitVec.append` (`++`); `x^y` (replication) is
`BitVec.replicate`. -/

/-- `x_{hi..lo}`: bits `hi` down to `lo` of `x` (Table 1.1, p.5: "Selection of bits y through z of
bit string x"). -/
def bits {n} (x : BitVec n) (hi lo : Nat) : BitVec (hi + 1 - lo) := x.extractLsb' lo (hi + 1 - lo)

/-- `x_y`: bit `y` of `x`, as a Boolean. -/
def bit {n} (x : BitVec n) (y : Nat) : Bool := x.getLsbD y

/-- `x_{n-1..0}`: the low `n` bits of `x` (`n` may be 0: the empty string). -/
def low {m} (x : BitVec m) (n : Nat) : BitVec n := x.extractLsb' 0 n

/-- `sign_extend(val)` to 32 bits, `nbits` being the width of `val` (MD00086 Vol II-A Rev 6.06
§2.2.2.4.1, Figure 2.27, p.24: "return (val_{nbits-1})^{GPRLEN-nbits} || val_{nbits-1..0}");
`GPRLEN = 32`. -/
def sign_extend {n} (val : BitVec n) : W32 := val.signExtend 32

/-- `zero_extend(val)` to 32 bits (§2.2.2.4.1, p.25: "Similarly for zero_extension"). -/
def zero_extend {n} (val : BitVec n) : W32 := val.setWidth 32

/-- The 16-bit `offset`/`immediate` field of an I-format instruction. -/
def imm16 (w : W32) : BitVec 16 := w.extractLsb' 0 16

/-- The 9-bit `offset` field of the Release 6 SPECIAL3 `LL`/`SC`/`PREF` (bits 15..7 of the word; the
`Instruction` holds the raw field value; LL p.223: "Release 6 implements a 9-bit offset", p.224). -/
def imm9 (w : W32) : BitVec 9 := w.extractLsb' 0 9

/-- `memory_address(ea)` (§2.2.2.4.2, Figure 2.28, p.25): "On a 32-bit CPU, memory_address returns
its 32-bit effective address argument unaffected." -/
def memory_address (ea : W32) : W32 := ea

end Manual
