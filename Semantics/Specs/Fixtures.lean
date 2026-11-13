import Semantics.Step
import Semantics.Env

/-!
# Fixtures — concrete programs and states for the satisfiable examples

`#guard`s in the family files instantiate the theorems on concrete programs/states built with these
(showing the hypotheses are satisfiable and that known-wrong outputs are rejected). A program is
placed in the state's memory with the loader's `loadImage` (`Semantics/Env.lean`), since `step`
fetches from memory.
-/

set_option maxRecDepth 4000

/-- One-instruction program containing `instr` at `textBase`, for building
concrete examples below. -/
def prog1Spec (instr : Instruction) : Program := (∅ : Program).insert textBase (encode instr)

/-- Apply a list of register writes to a state, for building concrete
examples below. -/
def setRegsSpec (s : State) (kvs : List (Fin 32 × W32)) : State :=
  kvs.foldl (fun acc kv => writeReg acc kv.1 kv.2) s

/-- A sequential program starting at `base`, for building concrete
delay-slot examples below (mirrors `Step.lean`'s test-only `buildProg`). -/
def buildProgSpec (base : W32) (instrs : List Instruction) : Program :=
  instrs.zipIdx.foldl (fun acc (instr, i) => acc.insert (base + BitVec.ofNat 32 (4 * i)) (encode instr))
    (∅ : Program)

/-- One step of `s` with the program `p` written into its memory (`loadImage`): the fixture
counterpart of "the instruction at `pc` is …". -/
def stepIn (p : Program) (s : State) : State := step (loadImage p s)
