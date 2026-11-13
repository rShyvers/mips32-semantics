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
