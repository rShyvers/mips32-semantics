import Semantics.Tests.StepFixtures

/-!
# `step` tests: loads/stores, `ll`/`sc`, `lwl`/`lwr`/`swl`/`swr`, `sb`, `sync`/`synci`

Moved verbatim out of `Semantics/Step.lean` (reviewability restructuring): the definition file now holds definitions only.
Every check that calls `step`/`run` is a `#guard` (see `StepFixtures.lean` for why).
-/

open StepTest

-- ### Loads/stores: big-endian composition, sign/zero extension, alignment

private def memTestState : State :=
  { (setRegs regs0 [(8, 0x10010000#32)]) with
      mem := ((((∅ : Std.HashMap W32 UInt8).insert 0x10010004#32 0x80).insert 0x10010005#32 0x01)
                |>.insert 0x10010006#32 0xff).insert 0x10010007#32 0x00 }

-- lw: full big-endian word
#guard nextRegEq (step (prog1 (.lw 8#32 9#32 4#32)) memTestState) 9 0x8001ff00#32
-- lb/lbu at the same address: sign-extend vs zero-extend a high-bit byte
#guard nextRegEq (step (prog1 (.lb 8#32 9#32 4#32)) memTestState) 9 0xffffff80#32
#guard nextRegEq (step (prog1 (.lbu 8#32 9#32 4#32)) memTestState) 9 0x00000080#32
-- lh/lhu at offset 4 (0x8001) and offset 6 (0xff00)
#guard nextRegEq (step (prog1 (.lh 8#32 9#32 4#32)) memTestState) 9 0xffff8001#32
#guard nextRegEq (step (prog1 (.lhu 8#32 9#32 4#32)) memTestState) 9 0x00008001#32
#guard nextRegEq (step (prog1 (.lh 8#32 9#32 6#32)) memTestState) 9 0xffffff00#32
#guard nextRegEq (step (prog1 (.lhu 8#32 9#32 6#32)) memTestState) 9 0x0000ff00#32
-- sw then read back
#guard (stepState (prog1 (.sw 8#32 9#32 4#32)) (setRegs regs0 [(8, 0x10010000#32), (9, 0x12345678#32)])).bind
        (fun s' => readMemWord s' 0x10010004#32) = some 0x12345678#32
-- sh stores only the low 16 bits, big-endian
#guard (stepState (prog1 (.sh 8#32 9#32 4#32)) (setRegs regs0 [(8, 0x10010000#32), (9, 0xffff1234#32)])).bind
        (fun s' => readMemHalf s' 0x10010004#32) = some 0x1234#32
-- misaligned lw/lh → AdEL, sw/sh → AdES (BadVAddr = the address); lb/lbu/sb never misalign
#guard raisesAddr (step (prog1 (.lw 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)])) excCodeAdEL 0x10010001#32
#guard raisesAddr (step (prog1 (.sw 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)])) excCodeAdES 0x10010001#32
#guard raisesAddr (step (prog1 (.lh 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)])) excCodeAdEL 0x10010001#32
#guard raisesAddr (step (prog1 (.sh 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)])) excCodeAdES 0x10010001#32
#guard isNext (step (prog1 (.lb 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)]))
-- effective address uses the sign-extended offset (SPEC-NOTES §9.3): a
-- negative offset must subtract, not add as a huge positive number.
#guard (stepState (prog1 (.sw 8#32 9#32 0xfffc#32)) (setRegs regs0 [(8, 0x10010010#32), (9, 0x2a#32)])).bind
        (fun s' => readMemWord s' 0x1001000c#32) = some 0x2a#32

-- ### ll/sc: load-linked/store-conditional (real MIPS32 atomic
-- synchronization primitives; see `Types.lean`'s `llBit` docstring for the
-- single-hart simplification). Same addressing/alignment as lw/sw.


-- `ll`: loads like `lw` and sets `llBit`.
#guard nextRegEq (step (prog1 (.ll 8#32 9#32 4#32)) memTestState) 9 0x8001ff00#32
#guard nextLlBitEq (step (prog1 (.ll 8#32 9#32 4#32)) memTestState) true
-- misaligned ll → AdEL, sc → AdES, same as lw/sw
#guard raisesAddr (step (prog1 (.ll 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)])) excCodeAdEL 0x10010001#32
#guard raisesAddr (step (prog1 (.sc 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)])) excCodeAdES 0x10010001#32

-- `sc` right after a matching `ll` succeeds: writes 1 to `$rt` and the store
-- commits.
private def llscSuccessProg : Program := buildProg textBase [.ll 8#32 9#32 0#32, .sc 8#32 10#32 0#32]
private def llscSuccessState : State := setRegs regs0 [(8, llscAddr), (10, 0xdeadbeef#32)]
#guard (stepN llscSuccessProg 2 llscSuccessState).bind (fun s => readMemWord s llscAddr)
  = some 0xdeadbeef#32
#guard (stepN llscSuccessProg 2 llscSuccessState).bind (fun s => some (readReg s 10))
  = some 1#32
#guard (stepN llscSuccessProg 2 llscSuccessState).bind (fun s => some s.llBit) = some false

-- `sc` after an intervening `sw` to *any* address (not just the `ll`'s own
-- address) fails: writes 0, the store does not commit, memory unchanged.
private def llscOtherAddr : W32 := 0x20000000#32
private def llscFailProg : Program :=
  buildProg textBase [.ll 8#32 9#32 0#32, .sw 11#32 12#32 0#32, .sc 8#32 10#32 0#32]
private def llscFailState : State :=
  setRegs regs0 [(8, llscAddr), (10, 0xdeadbeef#32), (11, llscOtherAddr), (12, 0x5555#32)]
#guard (stepN llscFailProg 3 llscFailState).bind (fun s => some (readReg s 10)) = some 0#32
#guard (stepN llscFailProg 3 llscFailState).bind (fun s => some s.llBit) = some false
-- the `ll`'s own address was never written by `sc` (it reads back as the
-- zero-fill default, not the attempted `0xdeadbeef` store)
#guard (stepN llscFailProg 3 llscFailState).bind (fun s => readMemWord s llscAddr) = some 0#32
-- the intervening `sw` itself did commit, to its own (different) address
#guard (stepN llscFailProg 3 llscFailState).bind (fun s => readMemWord s llscOtherAddr)
  = some 0x5555#32

-- `sc` always clears `llBit`, even on success, so a second immediate `sc`
-- (no intervening `ll`) fails: writes 0 and does not re-commit a new value.
private def llscDoubleProg : Program :=
  buildProg textBase [.ll 8#32 9#32 0#32, .sc 8#32 10#32 0#32, .sc 8#32 10#32 0#32]
private def llscDoubleState : State := setRegs regs0 [(8, llscAddr), (10, 0xaaaa5555#32)]
#guard (stepN llscDoubleProg 3 llscDoubleState).bind (fun s => some (readReg s 10)) = some 0#32
#guard (stepN llscDoubleProg 3 llscDoubleState).bind (fun s => some s.llBit) = some false
-- memory still holds the first `sc`'s committed value, not the second
-- (failed) attempt's
#guard (stepN llscDoubleProg 3 llscDoubleState).bind (fun s => readMemWord s llscAddr)
  = some 0xaaaa5555#32

-- ### lwl/lwr/swl/swr: classic MIPS32 unaligned load/store pair
-- (docs/spec/MIPS-COVERAGE-GAPS.md §3.6; docs/spec/INSTRUCTION-REF.md's
-- dedicated section). `A` below is word-aligned; bytes A..A+7 are
-- 0x11,0x22,...,0x88 so every byte-position merge is individually visible
-- in the resulting word.

private def unalignedBase : W32 := 0x10010000#32

private def unalignedTestState : State :=
  { (setRegs regs0 [(8, unalignedBase)]) with
      mem := (∅ : Std.HashMap W32 UInt8)
                |>.insert (unalignedBase + 0#32) 0x11
                |>.insert (unalignedBase + 1#32) 0x22
                |>.insert (unalignedBase + 2#32) 0x33
                |>.insert (unalignedBase + 3#32) 0x44
                |>.insert (unalignedBase + 4#32) 0x55
                |>.insert (unalignedBase + 5#32) 0x66
                |>.insert (unalignedBase + 6#32) 0x77
                |>.insert (unalignedBase + 7#32) 0x88 }

-- `lwl`: addr % 4 == 0 loads the full word, exactly matching plain `lw`.
#guard nextRegEq (step (prog1 (.lwl 8#32 9#32 0#32)) unalignedTestState) 9 0x11223344#32
#guard nextRegEq (step (prog1 (.lw  8#32 9#32 0#32)) unalignedTestState) 9 0x11223344#32
-- `lwl`: the three misaligned offsets, `$rt`'s untouched low bytes coming
-- from its prior value.
#guard nextRegEq (step (prog1 (.lwl 8#32 9#32 1#32)) (setRegs unalignedTestState [(9, 0x000000ff#32)]))
  9 0x223344ff#32
#guard nextRegEq (step (prog1 (.lwl 8#32 9#32 2#32)) (setRegs unalignedTestState [(9, 0x0000abcd#32)]))
  9 0x3344abcd#32
#guard nextRegEq (step (prog1 (.lwl 8#32 9#32 3#32)) (setRegs unalignedTestState [(9, 0x00112233#32)]))
  9 0x44112233#32
-- `lwl` never halts on a misaligned address (contrast `lw`).
#guard isNext (step (prog1 (.lwl 8#32 9#32 1#32)) unalignedTestState)

-- `lwr`: addr % 4 == 3 loads the full word, exactly matching plain `lw`.
#guard nextRegEq (step (prog1 (.lwr 8#32 9#32 3#32)) unalignedTestState) 9 0x11223344#32
-- `lwr`: the three misaligned offsets, `$rt`'s untouched high bytes coming
-- from its prior value.
#guard nextRegEq (step (prog1 (.lwr 8#32 9#32 0#32)) (setRegs unalignedTestState [(9, 0xaabbcc00#32)]))
  9 0xaabbcc11#32
#guard nextRegEq (step (prog1 (.lwr 8#32 9#32 1#32)) (setRegs unalignedTestState [(9, 0xaabb0000#32)]))
  9 0xaabb1122#32
#guard nextRegEq (step (prog1 (.lwr 8#32 9#32 2#32)) (setRegs unalignedTestState [(9, 0xaa000000#32)]))
  9 0xaa112233#32
-- `lwr` never halts on a misaligned address (contrast `lw`).
#guard isNext (step (prog1 (.lwr 8#32 9#32 1#32)) unalignedTestState)

-- Complementary-pair idiom: `lwl $rt, 1($rs)` then `lwr $rt, 4($rs)`
-- (addresses `A+1` and `A+4`, both unaligned/aligned-boundary-straddling)
-- together reconstruct the unaligned word spanning bytes `A+1..A+4`
-- (`0x22334455`), each byte supplied by exactly one of the two instructions.
private def lwlLwrIdiomProg : Program :=
  buildProg textBase [.lwl 8#32 9#32 1#32, .lwr 8#32 9#32 4#32]
#guard (stepN lwlLwrIdiomProg 2 unalignedTestState).bind (fun s => some (readReg s 9))
  = some 0x22334455#32

-- `swl`: addr % 4 == 0 stores the full word, exactly matching plain `sw`.
private def swTestState : State := setRegs regs0 [(8, unalignedBase), (9, 0xaabbccdd#32)]
#guard (stepState (prog1 (.swl 8#32 9#32 0#32)) swTestState).bind (fun s => readMemWord s unalignedBase)
  = some 0xaabbccdd#32
#guard (stepState (prog1 (.sw  8#32 9#32 0#32)) swTestState).bind (fun s => readMemWord s unalignedBase)
  = some 0xaabbccdd#32
-- `swl`: the three misaligned offsets store only the top `4 - off` bytes,
-- starting at `addr`; bytes before `addr` (and after the stored run) are
-- untouched (read back as the zero-fill default).
#guard (stepState (prog1 (.swl 8#32 9#32 1#32)) swTestState).bind
    (fun s => some (readMemByte s (unalignedBase+1#32), readMemByte s (unalignedBase+2#32),
                     readMemByte s (unalignedBase+3#32), readMemByte s (unalignedBase+4#32)))
  = some (some 0xaa, some 0xbb, some 0xcc, some 0)
#guard (stepState (prog1 (.swl 8#32 9#32 2#32)) swTestState).bind
    (fun s => some (readMemByte s (unalignedBase+2#32), readMemByte s (unalignedBase+3#32)))
  = some (some 0xaa, some 0xbb)
#guard (stepState (prog1 (.swl 8#32 9#32 3#32)) swTestState).bind
    (fun s => readMemByte s (unalignedBase+3#32)) = some 0xaa
-- `swl` never halts on a misaligned address (contrast `sw`), and clears
-- `llBit` like every other store-class instruction.
#guard isNext (step (prog1 (.swl 8#32 9#32 1#32)) swTestState)
#guard (stepState (prog1 (.swl 8#32 9#32 1#32)) { swTestState with llBit := true }).bind
    (fun s => some s.llBit) = some false

-- `swr`: addr % 4 == 3 stores the full word, exactly matching plain `sw`.
#guard (stepState (prog1 (.swr 8#32 9#32 3#32)) swTestState).bind (fun s => readMemWord s unalignedBase)
  = some 0xaabbccdd#32
-- `swr`: the three misaligned offsets store only the bottom `off + 1`
-- bytes, ending at `addr`.
#guard (stepState (prog1 (.swr 8#32 9#32 0#32)) swTestState).bind
    (fun s => readMemByte s unalignedBase) = some 0xdd
#guard (stepState (prog1 (.swr 8#32 9#32 1#32)) swTestState).bind
    (fun s => some (readMemByte s unalignedBase, readMemByte s (unalignedBase+1#32)))
  = some (some 0xcc, some 0xdd)
#guard (stepState (prog1 (.swr 8#32 9#32 2#32)) swTestState).bind
    (fun s => some (readMemByte s unalignedBase, readMemByte s (unalignedBase+1#32),
                     readMemByte s (unalignedBase+2#32)))
  = some (some 0xbb, some 0xcc, some 0xdd)
-- `swr` never halts on a misaligned address (contrast `sw`), and clears
-- `llBit` like every other store-class instruction.
#guard isNext (step (prog1 (.swr 8#32 9#32 1#32)) swTestState)
#guard (stepState (prog1 (.swr 8#32 9#32 1#32)) { swTestState with llBit := true }).bind
    (fun s => some s.llBit) = some false

-- Complementary-pair idiom: `swl $rt, 1($rs)` then `swr $rt, 4($rs)`
-- together store every byte of `$rt` into the unaligned word spanning
-- `A+1..A+4`, exactly once each.
private def swlSwrIdiomProg : Program :=
  buildProg textBase [.swl 8#32 9#32 1#32, .swr 8#32 9#32 4#32]
#guard (stepN swlSwrIdiomProg 2 swTestState).bind
    (fun s => some (readMemByte s (unalignedBase+1#32), readMemByte s (unalignedBase+2#32),
                     readMemByte s (unalignedBase+3#32), readMemByte s (unalignedBase+4#32)))
  = some (some 0xaa, some 0xbb, some 0xcc, some 0xdd)


-- ### sb

#guard (match stepState (prog1 (.sb 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32), (9, 0x123456ab#32)]) with
        | some s' => readMemByte s' 0x10010001#32 == some 0xab && readMemByte s' 0x10010000#32 == some 0
            && readMemByte s' 0x10010002#32 == some 0 && s'.pc == textBase + 4#32
        | none => false)
-- negative offset, odd address: no alignment requirement
#guard (match stepState (prog1 (.sb 8#32 9#32 0xffff#32)) (setRegs regs0 [(8, 0x10010004#32), (9, 0x7f#32)]) with
        | some s' => readMemByte s' 0x10010003#32 == some 0x7f
        | none => false)
-- `sb` then `lbu`/`lb` read it back (zero-/sign-extended)
#guard (match stepN (buildProg textBase [.sb 8#32 9#32 3#32, .lbu 8#32 10#32 3#32, .lb 8#32 11#32 3#32]) 3
          (setRegs regs0 [(8, 0x10010000#32), (9, 0xfffff180#32)]) with
        | some s' => readReg s' 10 == 0x80#32 && readReg s' 11 == 0xffffff80#32
        | none => false)
-- `sb` clears `llBit` (store pin), so a following `sc` fails
#guard (match stepState (prog1 (.sb 8#32 9#32 0#32)) { (setRegs regs0 [(8, 0x10010000#32)]) with llBit := true } with
        | some s' => s'.llBit == false
        | none => false)

-- wait: a documented no-op (no interrupt/timer model exists to wait for),
-- falls through to `pc + 4` with all state otherwise untouched.
#guard nextPcEq (step (prog1 (.wait 0#32)) regs0) (textBase + 4#32)
#guard (match stepState (prog1 (.wait 0#32)) regs0 with
        | some s' => s'.cp0Status == regs0.cp0Status && s'.cp0Cause == regs0.cp0Cause
                       && s'.cp0Epc == regs0.cp0Epc
        | none => false)

-- sync: a documented no-op (no concurrency/out-of-order execution exists to
-- order), falls through to `pc + 4` with *every* other field of `State`
-- left exactly as it was (`sameStateExceptPc`, not just a handful of
-- hand-picked fields the way the `wait` check above does).
#guard nextPcEq (step (prog1 (.sync 0#32)) regs0) (textBase + 4#32)
#guard (match stepState (prog1 (.sync 0#32)) regs0 with
        | some s' => sameStateExceptPc regs0 s'
        | none => false)

-- synci: a documented no-op (no instruction-cache model exists to flush),
-- same full-state-untouched check as `sync` above, run from a state with a
-- nonzero base register so the (unused) address computation actually reads
-- something -- confirms the computation itself has no observable effect.
private def synciTestState : State := setRegs regs0 [(8, 0x10010000#32)]
#guard nextPcEq (step (prog1 (.synci 8#32 4#32)) synciTestState) (textBase + 4#32)
#guard (match stepState (prog1 (.synci 8#32 4#32)) synciTestState with
        | some s' => sameStateExceptPc synciTestState s'
        | none => false)


-- ### sc compares its address with the preceding ll's
#guard (match stepState (prog1 (.ll 8#32 9#32 0#32)) (setRegs regs0 [(8, 0x10010000#32)]) with
        | some s1 => s1.llBit && s1.llAddr == 0x10010000#32 &&
            (match step (prog1 (.sc 8#32 10#32 4#32))
                (setRegs { s1 with pc := textBase } [(10, 0xdeadbeef#32)]) with
             | .next s2 => readReg s2 10 == 0#32 && !s2.llBit &&
                 readMemWord s2 0x10010004#32 == some 0#32
             | .halt _ => false)
        | none => false)
