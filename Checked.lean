-- Root of the `Checked` library: the code `lake check` kernel-replays.
-- This is `lake check`'s default target (see `lakefile.toml`), so `lake
-- check` re-checks exactly this code in the kernel and fails on any axiom
-- other than `propext`, `Classical.choice`, `Quot.sound`.
--
-- Everything is included: the model, every spec file (through the index
-- `Semantics.Specs.StepSpec`), the comparator solution module and the tests.
-- The one module NOT imported -- here or in `Semantics.lean` -- is
-- `Semantics.Statements`, the statements-only challenge of `lake comparator`
-- (`comparator.json`), which contains `sorry` by design.
import Semantics.Word
import Semantics.Types
import Semantics.State
import Semantics.Instruction
import Semantics.Asm
import Semantics.FpOps
import Semantics.FpOpsFacts
import Semantics.FpCompareFacts
-- The IEEE rounding core proved against the IEEE 754 definition (FpOpsSpec).
import Semantics.FpOpsSpec
import Semantics.FpOpsCorrectNat
import Semantics.FpOpsCorrectGrid
import Semantics.FpOpsCorrectValue
import Semantics.FpOpsCorrectShape
import Semantics.FpOpsCorrectScale
import Semantics.FpOpsCorrectPack
import Semantics.FpOpsCorrectCore
import Semantics.FpOpsCorrectMain
import Semantics.FpOpsCorrectExact
import Semantics.FpOpsCorrectDivSqrt
import Semantics.FpOpsCorrectOps
import Semantics.FpOpsCorrectApi
import Semantics.FpOpsCorrectAcc
import Semantics.FpOpsCorrectRecip
import Semantics.FpOpsCorrectRsqrtAux
import Semantics.FpOpsCorrectRsqrt
-- Every FP operand, conversions, compares and the FCSR proved against FpOpsSpec.
import Semantics.FpOpsCorrectSpecial
import Semantics.FpOpsCorrectEnv
import Semantics.FpOpsCorrectArith
import Semantics.FpOpsCorrectWord
import Semantics.FpOpsCorrectConv
import Semantics.FpOpsCorrectCompare
import Semantics.FpOpsCorrectFcsr
import Semantics.FpOpsCorrectIEEE
import Semantics.FpOpsCorrectFma
import Semantics.FpOpsCorrectR6
import Semantics.Step
-- The environment layer (loader, hosted run): not part of the architecture.
import Semantics.Env
-- All spec files (the index imports every `Semantics/Specs/*.lean`, including `DecodeSpec`).
import Semantics.Specs.StepSpec
-- The `lake comparator` solution module (one-line proofs of the statements in `Semantics/Statements.lean`).
import Semantics.StatementsProofs
-- The independent manual specification (docs/MANUAL-SPEC.md) and the refinement proofs.
import Semantics.Manual.Arch
import Semantics.Manual.Choices
import Semantics.Manual.Accuracy
import Semantics.Manual.Pseudocode
import Semantics.Manual.CP0
import Semantics.Manual.Memory
import Semantics.Manual.FPU
import Semantics.Manual.Exceptions
import Semantics.Manual.Interrupts
import Semantics.Manual.Timer
import Semantics.Manual.Reset
import Semantics.Manual.Encoding
import Semantics.Manual.Operation
import Semantics.Manual.Cycle
-- The specification's own decoder and its bridge to `decode`
import Semantics.Manual.Decode
import Semantics.Refine.DecodeDiagram
import Semantics.Refine.DecodeBridge
import Semantics.Tests.DecodeDiagramTests
import Semantics.Refine.Abs
import Semantics.Refine.Bridge
import Semantics.Refine.Fetch
import Semantics.Refine.BridgeBits
import Semantics.Refine.IntArith
import Semantics.Refine.Memory
import Semantics.Refine.Branch
import Semantics.Refine.FpuArith
import Semantics.Refine.BridgeFpu
import Semantics.Refine.FpuConvert
import Semantics.Refine.Cp0
-- control + system
import Semantics.Refine.BridgeControl
import Semantics.Refine.Jump
import Semantics.Refine.System
-- integer ALU
import Semantics.Refine.BridgeIntAlu
import Semantics.Refine.Shift
import Semantics.Refine.BitOps
import Semantics.Refine.Immediate
-- memory/atomic/trap/syscall
import Semantics.Refine.BridgeMem
import Semantics.Refine.Atomic
import Semantics.Refine.Trap
import Semantics.Refine.Syscall
-- FPU memory/move/control/branch
import Semantics.Refine.BridgeFpuMove
import Semantics.Refine.FpuMemory
import Semantics.Refine.FpuMove
import Semantics.Refine.FpuControl
-- cycle refinement and top theorems
import Semantics.Manual.Relation
import Semantics.Refine.Cycle
import Semantics.Refine.Decode
import Semantics.Refine.Invariant
import Semantics.Refine.Instr
import Semantics.Refine.Step
import Semantics.Refine.Determinism
import Semantics.Refine.ChoiceExact
-- Tests (moved out of the definition files; they run in every build and under `lake check`).
import Semantics.Tests.WordTests
import Semantics.Tests.TypesTests
import Semantics.Tests.StateTests
import Semantics.Tests.InstructionTests
import Semantics.Tests.AsmTests
import Semantics.Tests.FpOpsTests
import Semantics.Tests.StepFixtures
import Semantics.Tests.StepArithTests
import Semantics.Tests.StepMemoryTests
import Semantics.Tests.StepControlTests
import Semantics.Tests.StepExceptionTests
import Semantics.Tests.StepFpTests
import Semantics.Tests.EnvTests
import Semantics.Tests.ManualTests
-- `Manual.modelImpl_valid` (RECIP/RSQRT accuracy from the proved core)
import Semantics.Refine.ImplValid
