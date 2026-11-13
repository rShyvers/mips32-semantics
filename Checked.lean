-- Root of the `Checked` library: the code `lake check` kernel-replays.
-- This is `lake check`'s default target (see `lakefile.toml`), so `lake
-- check` re-checks exactly this code in the kernel and fails on any axiom
-- other than `propext`, `Classical.choice`, `Quot.sound`.
--
-- `Semantics.Specs.StepSpec` is included: it no longer contains any
-- `sorry` (it was excluded while it had documented ones), so every theorem
-- in the project is now covered by this gate. `lake comparator` (see
-- `comparator.json`) still separately checks a named list of headline
-- StepSpec theorems against an explicit axiom allow-list.
import Semantics.Word
import Semantics.Types
import Semantics.State
import Semantics.Instruction
import Semantics.Asm
import Semantics.Step
import Semantics.Specs.StepSpec
