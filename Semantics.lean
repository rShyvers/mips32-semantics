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
-- All spec files (the index imports every `Semantics/Specs/*.lean`, including `DecodeSpec`).
import Semantics.Specs.StepSpec
-- The `lake comparator` solution module (one-line proofs of the statements in `Semantics/Statements.lean`).
import Semantics.StatementsProofs
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
