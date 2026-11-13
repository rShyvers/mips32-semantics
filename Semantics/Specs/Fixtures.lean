import Semantics.Step

/-!
# Fixtures — concrete programs and states for the satisfiable examples

`#guard`s in the family files instantiate the theorems on concrete programs/states built with these
(showing the hypotheses are satisfiable and that known-wrong outputs are rejected).
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
