-- Root of the `Semantics` library: importing here makes plain `lake build`
-- (and CI) cover every module. The only module deliberately left out is
-- `Semantics.Statements` (the statements-only `lake comparator` challenge,
-- whose proofs are `sorry` by design; see its header).
import Semantics.Word
import Semantics.Types
import Semantics.State
import Semantics.Instruction
import Semantics.Asm
import Semantics.FpOps
import Semantics.FpOpsFacts
import Semantics.FpCompareFacts
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
import Semantics.Refine.Abs
import Semantics.Refine.Bridge
import Semantics.Refine.Fetch
import Semantics.Refine.IntArith
import Semantics.Refine.Memory
import Semantics.Refine.Branch
import Semantics.Refine.BranchLikely
import Semantics.Refine.FpuArith
import Semantics.Refine.Cp0
import Semantics.Refine.Unaligned
-- 7C S3 control + system
import Semantics.Refine.BridgeControl
import Semantics.Refine.Jump
import Semantics.Refine.System
-- end 7C S3
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
