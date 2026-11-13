import Semantics.Env
import Semantics.Tests.StepFixtures

/-!
# Tests for the environment layer (`Semantics/Env.lean`): loader, hosted run, stopping conventions

Formerly part of `TypesTests.lean` (`HaltReason` lived in `Types.lean`).
-/

open StepTest

-- `HaltReason` sanity
example : HaltReason.exit ≠ HaltReason.noInstruction 0#32 := by decide
example : HaltReason.unhandledException 12#32 0#32 0#32 ≠ HaltReason.noInstruction 0#32 := by decide

-- The loader writes the image into memory, big-endian; the processor fetches it from there.
#guard readMemWord (load (prog1 (.addiu 0#32 8#32 5#32))) textBase
  = some (encode (.addiu 0#32 8#32 5#32))
#guard (load (prog1 (.addiu 0#32 8#32 5#32))).pc == textBase
#guard readReg (step (load (prog1 (.addiu 0#32 8#32 5#32)))) 8 == 5#32

-- Self-modifying code with the manual's SYNCI sequence (MD00086 Vol II-A Rev 6.06, SYNCI,
-- p.412-414): store a new instruction word over a later `nop`, `synci`, `sync`, `jr.hb` to it.
-- The stored `addiu $t2, $zero, 7` executes; then `exit`.
private def smcProg : Program :=
  buildProg textBase
    [ .lui 8#32 0x0040#32              -- $t0 = 0x00400000
    , .ori 8#32 8#32 0x0028#32              -- $t0 = textBase + 40 (the patched slot)
    , .lui 9#32 0x240a#32              -- $t1 = encode (addiu $t2, $zero, 7)
    , .ori 9#32 9#32 0x0007#32
    , .sw 8#32 9#32 0#32                    -- store it
    , .synci 8#32 0#32
    , .sync 0#32
    , .jr 8#32                              -- (jr.hb assembles to jr with the hint bit)
    , .sll 0#32 0#32 0#32                   -- delay slot
    , .sll 0#32 0#32 0#32
    , .sll 0#32 0#32 0#32                   -- textBase + 40: patched at run time
    , .addiu 0#32 2#32 10#32
    , .syscall 0#32 ]
#guard encode (.addiu 0#32 10#32 7#32) == 0x240a0007#32
#guard (match runProgram smcProg 100 with
        | .halted .exit h _ => readReg h.machine 10 == 7#32
        | _ => false)
-- The bare run executes the same instructions (no service is involved before the `syscall`).
#guard readReg (run (load smcProg) 11) 10 == 7#32

-- Bare mode: the `syscall` is the System Call exception; with no handler loaded the hosted
-- observer stops with `unhandledException 8`.
#guard (match runProgram (buildProg textBase [.addiu 0#32 2#32 1#32, .syscall 0#32]) 10 false with
        | .halted (.unhandledException c epc _) h _ => c == excCodeSys && epc == textBase + 4#32 && h.out == ""
        | _ => false)
