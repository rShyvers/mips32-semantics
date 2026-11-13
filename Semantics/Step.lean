import Std.Data.HashMap.Basic
import Semantics.Word
import Semantics.Types
import Semantics.State
import Semantics.Instruction
import Semantics.FpOps

/-!
# Step — small-step semantics of the modeled MIPS32 Release 2 instruction set

`step` executes one instruction; `run` is `step` iterated with a fuel bound
and nothing else. Ground truth: the latest manual revisions in
`docs/spec/manuals/` are normative, read for the pre-Release-6 wording
(MD00082 Vol I-A Rev 6.01, MD00086 Vol II-A Rev 6.06, MD00090 Vol III
Rev 6.02; see CLAUDE.md), summarised per instruction in
`docs/spec/INSTRUCTION-REF.md`. Comments below that cite "MD00086 Rev 2.50"
with a table or page number are historical citations of that older revision.
Pinned conventions and divergences from the MARS test oracle are in
`docs/spec/SPEC-NOTES.md` §9.

## What `step` does

`step : State → State` is one instruction time of the processor and nothing else. It is total by
its type: the manual has no halting state, and every behaviour the model implements is a state
transition (possibly to the exception vector). Loading a program, the MARS-style `syscall`
services and the conventions for stopping a run are the environment's, not the processor's; they
are in `Semantics/Env.lean`.

1. **Fetch** the big-endian word at `pc` (`readMemWord s s.pc`): the virtual `pc` is translated
   by the Fixed Mapping MMU (`State.lean`, `translate`) and the word read from physical memory
   `State.physMem`. A misaligned `pc`, or a `pc` outside useg in User Mode, raises Address Error
   (AdEL, `BadVAddr = pc`). Memory that was never written reads as 0 (`State.lean`; 0 encodes
   `sll $0, $0, 0`, a no-op).
2. **Decode** it (`Instruction.decode`, strict). A word that does not decode raises Reserved
   Instruction (or Coprocessor Unusable for an unusable coprocessor's encoding space).
3. **Execute** it (`execInstr`).

Because fetch reads `physMem`, a store to the instruction stream changes what is executed (MD00086
Vol II-A Rev 6.06, SYNCI, p.412). The model has no caches, so `synci` has nothing to synchronize.

## Branch delay slots

`State.pendingBranch = some t` means "the instruction at `pc` is in a delay
slot; control goes to `t` after it". Every branch/jump sets it (taken: the
target; not taken: `pc + 8`). Every non-control-flow instruction goes
through `mkNext`/`advance`, which commits a pending target. A control-transfer
instruction in a delay slot (UNPREDICTABLE, or UNDEFINED for `eret`/`wait`, in the
architecture) raises Reserved Instruction (pin; `execInstr`). A not-taken branch-likely
nullifies its delay slot: its own step goes straight to `pc + 8`.

## Exceptions

`exceptionEntry` implements the general exception sequence (MD00090,
"General Exception Processing"): `EPC`/`Cause.BD` (only if `EXL` was 0),
`Cause.ExcCode`, `Status.EXL ← 1`, `PC ←` the general vector (`BEV`
selects which; `EBase` supplies the base when `BEV = 0`), and the pending
branch is abandoned. Raised here: Integer Overflow (`add`/`addi`/`sub`),
Address Error (misaligned load/store/fetch, or a kernel address referenced from User Mode;
sets `BadVAddr`), Reserved
Instruction, Coprocessor Unusable (`Cause.CE` = the unit), Floating Point,
System Call (`syscall`, always), Breakpoint, Trap.

## Floating point

All FP arithmetic is `Semantics/FpOps.lean` (`Mips.Fp`): exact results on bit
patterns, one correctly-rounded pack under FCSR.RM, IEEE flags. No host
`Float` appears anywhere in `step`. Every coprocessor-1 instruction first
checks `Status.CU1` (`usesCop1`); arithmetic instructions finish through
`fpFinishS`/`fpFinishD`/`fpFinishCmp`, which update FCSR with
`Mips.Fp.fpUpdate` and take the Floating Point exception instead of writing
the destination when an enabled exception was raised.

## Operating modes

Kernel Mode and User Mode (MD00090 Vol III Rev 6.02 ch.3, p.21-23; `kernelMode`, `userMode`):
Supervisor Mode and Debug Mode are not implemented. A coprocessor-0 instruction (`usesCop0`), an
undecodable COP0 word or a CACHE word (`isCop0Word`) executed outside Kernel Mode with
`Status.CU0 = 0` raises Coprocessor Unusable with `Cause.CE = 0` (§6.2.22, p.100). The User-Mode
address check (a reference outside useg from User Mode is an Address Error, Table 4.2, p.30)
belongs to the MMU: every memory access goes through the six `readMem*`/`writeMem*` functions of
`State.lean`, which translate through `translate` (`kernelMode`/`userMode` are defined there).

## Address translation

The MMU is the Fixed Mapping MMU (`Config.MT = 3`, `configValue`; MD00090 Vol III Rev 6.02
Appendix A.1, p.313-317), implemented once in `State.lean` (`fixedMappingPA`, `translate`):
kseg0/kseg1 → the low 512 MB, useg/kuseg → `VA + 1 GB` (`ERL = 0`) or `VA` (`ERL = 1`), kseg2/kseg3
→ `VA`.

## Reset

`resetException` is the Reset exception (§6.2.5, p.89-90) applied to a state; `resetState` is
`resetException powerOnState`, the machine after a cold reset.

## Not modeled

Interrupts, timer, TLB (the MMU is the Fixed Mapping MMU), caches, shadow register sets (see
`docs/spec/SPEC-NOTES.md`).
-/

/-- Convert a raw 5-bit register-field value (as extracted by `decode`, hence
always `< 32`) into a `Fin 32` index for `readReg`/`writeReg`. -/
def regIdx (w : W32) : Fin 32 :=
  Fin.ofNat 32 w.toNat

/-- Advance `s`'s program counter: if a branch/jump delay-slot transfer is
pending (`s.pendingBranch = some target`), resolve it now — `pc` becomes
`target` and `pendingBranch` is cleared — otherwise this is an ordinary
fallthrough, so `pc` advances by one instruction word (`W32` wraparound on
overflow, matching hardware). This is the one place the delay-slot exit is
implemented (SPEC-NOTES §9 item 1; INSTRUCTION-REF Global rule 3): every
non-control-flow `execInstr` case routes through `mkNext`/`advance`, so it
automatically commits a pending branch/jump when it is the delay-slot
instruction, without any of those cases mentioning `pendingBranch`
themselves. -/
def advance (orig result : State) : State :=
  match orig.pendingBranch with
  | some target => { result with pc := target, pendingBranch := none }
  | none => { result with pc := result.pc + 4#32 }

/-- Complete the current instruction with the ordinary, non-control-flow
effect `result`, resolving any delay-slot transfer
pending on `orig` -- the state `execInstr` was called with, i.e. *before*
this instruction's own effect -- via `advance`. Taking `orig` and `result`
as two separate arguments (rather than just the already-updated state)
keeps `orig.pendingBranch` syntactically visible at the call site instead of
buried behind an arbitrary `writeReg`/`writeMem*` call's own internal
register-index/alignment check, which matters for `StepSpec.lean`'s
`rfl`-based proofs (a symbolic register index makes `(writeReg s i v)`
itself irreducible, which would otherwise make its `.pendingBranch` field
irreducible too, even though `writeReg`/`writeMem*` never actually change
it). -/
def mkNext (orig result : State) : State :=
  advance orig result

/-- Whether `instr` is a control-transfer instruction that may not appear in
a branch delay slot: the 12 ordinary branches/jumps (`beq`,`bne`,`blez`,
`bgtz`,`bltz`,`bgez`,`bltzal`,`bgezal`,`j`,`jal`,`jr`,`jalr`), the 8
branch-likely instructions, the FP branches `bc1f`/`bc1t`/`bc1fl`/`bc1tl`,
`eret` and `wait` (26 in all): the control transfer instructions (CTIs) that
MD00082 Vol I-A Rev 6.01 §5.3.2.1 (p.62) forbids in a branch delay slot ("any
CTI, including branches and jumps, ERET, ERETNC, DERET, WAIT, and PAUSE";
`ERETNC`, `DERET`, `PAUSE` and `NAL` are not modeled). `execInstr` raises
Reserved Instruction when one of these is reached with `s.pendingBranch = some _`,
i.e. directly after *any* branch/jump, taken or not (pin; see `execInstr`). -/
def isBranchLike (instr : Instruction) : Bool :=
  match instr with
  | .beq _ _ _ | .bne _ _ _ | .blez _ _ | .bgtz _ _
  | .bltz _ _ | .bgez _ _ | .bltzal _ _ | .bgezal _ _
  | .j _ | .jal _ | .jr _ | .jalr _ _
  | .beql _ _ _ | .bnel _ _ _ | .blezl _ _ | .bgtzl _ _
  | .bltzl _ _ | .bgezl _ _ | .bltzall _ _ | .bgezall _ _
  | .bc1f _ _ | .bc1t _ _ | .bc1fl _ _ | .bc1tl _ _ | .eret | .wait _ => true
  | _ => false

/-- Signed-overflow predicate for `add`/`addi`, following INSTRUCTION-REF's
exact Java-derived test: overflow iff both operands are non-negative and the
(32-bit-wrapped) sum is negative, or both are negative and the sum is
non-negative. -/
def addOverflows (a b sum : Int) : Bool :=
  decide ((0 ≤ a ∧ 0 ≤ b ∧ sum < 0) ∨ (a < 0 ∧ b < 0 ∧ 0 ≤ sum))

/-- Signed-overflow predicate for `sub`, following INSTRUCTION-REF's exact
test: overflow iff the minuend is non-negative, the subtrahend is negative,
and the (32-bit-wrapped) difference is negative; or the minuend is negative,
the subtrahend is non-negative, and the difference is non-negative. -/
def subOverflows (a b diff : Int) : Bool :=
  decide ((0 ≤ a ∧ b < 0 ∧ diff < 0) ∨ (a < 0 ∧ 0 ≤ b ∧ 0 ≤ diff))

/-- Sign-extend a byte to a full `W32` (for `lb`). -/
def signExtByte (b : UInt8) : W32 :=
  (BitVec.ofNat 8 b.toNat).signExtend 32

/-- Zero-extend a byte to a full `W32` (for `lbu`). -/
def zeroExtByte (b : UInt8) : W32 :=
  BitVec.ofNat 32 b.toNat

/-- Replace byte-position `slot` of `w` with `b`, leaving the other three
byte-positions unchanged. `slot = 0` is the most-significant byte (bits
31..24), `slot = 3` the least-significant (bits 7..0) -- the same
big-endian byte-position convention `State.readMemWord`/`writeMemWord` use
(`slot` is literally "how many word-boundary-crossing bytes this position is
from the top"). Used by `lwl`/`lwr`'s partial-register merge (`docs/spec/
INSTRUCTION-REF.md`'s unaligned-memory-access section). -/
def setByteSlot (w : W32) (slot : Nat) (b : UInt8) : W32 :=
  let shift := (3 - slot) * 8
  let mask : W32 := 0xff#32 <<< shift
  (w &&& ~~~mask) ||| (zeroExtByte b <<< shift)

/-- Extract byte-position `slot` of `w` (same convention as `setByteSlot`).
Used by `swl`/`swr`'s partial-memory-store byte extraction. -/
def getByteSlot (w : W32) (slot : Nat) : UInt8 :=
  let shift := (3 - slot) * 8
  ((w >>> shift) &&& 0xff#32).toNat.toUInt8

/-- Sign-extend the low byte of a register value to 32 bits (for `seb`).
Same technique as `signExtByte`, but operating directly on a `W32` register
value rather than a `UInt8` loaded from memory. -/
def signExtLowByte (w : W32) : W32 :=
  (w.extractLsb 7 0).signExtend 32

/-- A `W32` with the low `n` bits set and all higher bits clear (`n = 0..32`).
Used by `ext`/`ins` to mask out a `size`-bit field. Built as `(1 <<< n) - 1`:
for `n = 32`, `1 <<< 32` wraps to `0` in a 32-bit `BitVec` (hardware shift
semantics, `BitVec.shiftLeft`), so `0 - 1` wraps to `0xffffffff` -- exactly
the all-ones mask a full-word field needs, with no separate case split. -/
def lowBitsMask (n : Nat) : W32 :=
  ((1#32) <<< n) - 1#32

/-- Count leading zero bits in `w` from the MSB (bit 31), stopping at the
first set bit; `32` if `w` is all-zero. `fuel` bounds the scan to the
remaining unscanned bit positions (`pos .. 31`) so this terminates by
structural recursion on `fuel`, with no `partial`/`sorry` needed. Used by
`clz`/`clo` (`docs/spec/INSTRUCTION-REF.md`): per the MIPS32 ISA, both
instructions report `32` when there is no bit of the relevant kind. -/
def countLeadingZerosFrom (w : W32) : Nat → Nat → Nat
  | 0, pos => pos
  | fuel + 1, pos => if w.getMsbD pos then pos else countLeadingZerosFrom w fuel (pos + 1)

/-- Count leading zero bits in `w`, from the MSB. -/
def countLeadingZeros (w : W32) : Nat :=
  countLeadingZerosFrom w 32 0

/-- Count leading one bits in `w`, from the MSB: a run of `1`s in `w` is
exactly a run of `0`s in `~~~w`, so this reduces to `countLeadingZeros`. -/
def countLeadingOnes (w : W32) : Nat :=
  countLeadingZeros (~~~w)

/-- The value of `EBase` as software reads it: the stored Exception Base
field (bits 29..12) under the fixed bits 31..30 = `10`; bits 11..0 zero
(MD00090 Vol III Rev 6.02 §9.41, Table 9.58, p.224). -/
def ebaseValue (s : State) : W32 := (s.cp0EBase &&& ebaseWriteMask) ||| ebaseFixedBits

/-- The general exception vector (MD00090 Vol III Rev 6.02 §6.2.3, p.88):
`0xBFC0_0380` when `Status.BEV = 1`; otherwise `EBase[31..12] ‖ 0x000` plus
the offset `0x180` ("PC ← vectorBase31..30 ‖ (vectorBase29..0 +
vectorOffset29..0)"). The base's low 12 bits are zero and the offset is below
`0x1000`, so that sum is the bitwise OR. With `EBase` at its reset value this
is `0x8000_0180`. -/
def exceptionVector (s : State) : W32 :=
  if s.cp0Status &&& statusBevMask == 0#32 then ebaseValue s ||| exceptionVectorOffset
  else exceptionVectorBevAddr

/-- The state after taking a general exception with `Cause.ExcCode = excCode`
from `s`, where `s.pc` is the faulting instruction (MD00090 Vol III Rev 6.02
§6.2.3 "General Exception Processing", p.86-88):

```
if Status.EXL = 0 then
  if InstructionInBranchDelaySlot then EPC ← PC − 4;  Cause.BD ← 1
  else                                 EPC ← PC;      Cause.BD ← 0
(if Status.EXL = 1, EPC and Cause.BD are left unchanged)
Cause.CE ← FaultingCoprocessorNumber     -- bits 29..28
Cause.ExcCode ← excCode                  -- bits 6..2; every other Cause bit kept
Status.EXL ← 1
PC ← vector                              -- `exceptionVector`
```

`ce` is the coprocessor unit number for Coprocessor Unusable; for every other
exception the field "is loaded, but not defined" (p.87) and the model loads
`0` (the default argument).

"In a branch delay slot" is `s.pendingBranch.isSome`. The pending branch is
abandoned (`pendingBranch := none`): the handler runs sequentially from the
vector, and `eret` to `EPC` re-executes the branch. `LLbit` is cleared
(MD00086 Vol II-A Rev 6.06, SC, p.350: "Exceptions between the LL and SC
cause SC to fail"). -/
def exceptionEntry (s : State) (excCode : W32) (ce : W32 := 0#32) : State :=
  let exl := s.cp0Status &&& statusExlMask != 0#32
  let inSlot := s.pendingBranch.isSome
  { s with
      cp0Epc := if exl then s.cp0Epc else if inSlot then s.pc - 4#32 else s.pc
      cp0Cause :=
        (((if exl then s.cp0Cause
          else if inSlot then s.cp0Cause ||| causeBdMask
          else s.cp0Cause &&& ~~~causeBdMask) &&& ~~~(causeExcCodeMask ||| causeCeMask))
          ||| ((excCode <<< 2) &&& causeExcCodeMask)) ||| ((ce <<< 28) &&& causeCeMask)
      cp0Status := s.cp0Status ||| statusExlMask
      pc := exceptionVector s
      pendingBranch := none
      llBit := false }

/-- Raise a general exception: the state after exception entry (the
processor continues at the exception vector). -/
def takeException (s : State) (excCode : W32) : State :=
  exceptionEntry s excCode

/-- Raise Coprocessor Unusable for coprocessor 1: `Cause.ExcCode = CpU` (11),
`Cause.CE = 1` (MD00090 Vol III Rev 6.02 §6.2.22, p.100). -/
def takeCoprocessorUnusable (s : State) : State :=
  exceptionEntry s excCodeCpU 1#32

/-- Raise an Address Error exception (`excCodeAdEL` for a load or fetch,
`excCodeAdES` for a store): as `takeException`, and additionally
`BadVAddr ← addr`, the failing address. -/
def takeAddressException (s : State) (excCode addr : W32) : State :=
  exceptionEntry { s with cp0BadVAddr := addr } excCode

/-- The `ExcCode` field (bits 6..2) of `Cause`, as a number. -/
def causeExcCode (s : State) : W32 :=
  (s.cp0Cause &&& causeExcCodeMask) >>> 2

/-- `Status.CU1`: coprocessor 1 is usable. -/
def cu1Enabled (s : State) : Bool := s.cp0Status &&& statusCu1Mask != 0#32

/-- **Coprocessor 0 is usable** (MD00090 Vol III Rev 6.02 §3.5.3, p.23): "Access to Coprocessor
0 registers are enabled under any of the following conditions: The processor is running in Kernel
Mode or Debug Mode, as defined above. The CU0 bit in the Status register is 1." -/
def cp0Usable (s : State) : Bool := kernelMode s || s.cp0Status &&& statusCu0Mask != 0#32

/-- The coprocessor-0 instructions of the model: `mfc0`, `mtc0`, `di`, `ei`, `eret`, `wait`.
Each page lists Coprocessor Unusable among its exceptions (MD00086 Vol II-A Rev 6.06: MFC0
p.266, MTC0 p.291, DI p.164, EI p.176, ERET p.178, WAIT p.443), which is raised when "A COP0
or Cache instruction was executed while the processor was running in a mode other than Debug
Mode or Kernel Mode, and the CU0 bit in the Status register was a zero" (MD00090 Vol III
Rev 6.02 §6.2.22, p.100). The other COP0 instructions (TLB instructions, `DERET`, `RDPGPR`,
`WRPGPR`) and `CACHE` are not implemented: their words do not decode and are covered by
`isCop0Word`. -/
def usesCop0 (instr : Instruction) : Bool :=
  match instr with
  | .mfc0 _ _ _ | .mtc0 _ _ _ | .di _ | .ei _ | .eret | .wait _ => true
  | _ => false

/-- Whether a word that does **not** decode belongs to coprocessor 0 or is a CACHE instruction:
opcode COP0 (0x10) or CACHE (0x2f). Outside Kernel Mode with `Status.CU0 = 0` such a word raises
Coprocessor Unusable (`Cause.CE = 0`) instead of Reserved Instruction: "An instruction was
executed that specifies an unimplemented COP0 opcode encoding of the function field when rs is
CO ... assuming that access to coprocessor 0 is allowed. If access to the coprocessor is not
allowed, a Coprocessor Unusable Exception occurs instead" (MD00090 Vol III Rev 6.02 §6.2.21,
p.99), and "If both exceptions occur on the same instruction, the Coprocessor Unusable Exception
takes priority over the Reserved Instruction Exception" (Table 6.6, p.83). -/
def isCop0Word (w : W32) : Bool :=
  opcodeOf w == 0x10#32 || opcodeOf w == 0x2f#32

/-- Raise Coprocessor Unusable for coprocessor 0: `Cause.ExcCode = CpU` (11),
`Cause.CE = 0` ("unit number of the coprocessor being referenced", MD00090 Vol III
Rev 6.02 §6.2.22, p.100). -/
def takeCop0Unusable (s : State) : State :=
  exceptionEntry s excCodeCpU 0#32

/-- The instructions that need `Status.CU1` (MD00090 Vol III Rev 6.02
§6.2.22, p.100: "A COP1, COP1X, LWC1, SWC1, LDC1, SDC1 or MOVCI (Special
opcode function field encoding) instruction was executed and the CU1 bit in
the Status register was a zero"): every COP1 and COP1X instruction
(including `prefx`), the four FP load/stores, and the GPR `movf`/`movt`. -/
def usesCop1 (instr : Instruction) : Bool :=
  match instr with
  | .mfc1 _ _ | .mtc1 _ _ | .mfhc1 _ _ | .mthc1 _ _ | .cfc1 _ _ | .ctc1 _ _
  | .lwc1 _ _ _ | .swc1 _ _ _ | .ldc1 _ _ _ | .sdc1 _ _ _
  | .lwxc1 _ _ _ | .ldxc1 _ _ _ | .swxc1 _ _ _ | .sdxc1 _ _ _ | .prefx _ _ _
  | .addS _ _ _ | .subS _ _ _ | .mulS _ _ _ | .divS _ _ _
  | .sqrtS _ _ | .absS _ _ | .movS _ _ | .negS _ _ | .recipS _ _ | .rsqrtS _ _
  | .roundWS _ _ | .truncWS _ _ | .ceilWS _ _ | .floorWS _ _ | .cvtWS _ _
  | .cvtDS _ _ | .cvtSW _ _ | .cvtDW _ _
  | .addD _ _ _ | .subD _ _ _ | .mulD _ _ _ | .divD _ _ _
  | .sqrtD _ _ | .absD _ _ | .movD _ _ | .negD _ _ | .recipD _ _ | .rsqrtD _ _
  | .roundWD _ _ | .truncWD _ _ | .ceilWD _ _ | .floorWD _ _ | .cvtWD _ _ | .cvtSD _ _
  | .cCondS _ _ _ _ | .cCondD _ _ _ _
  | .movfS _ _ _ | .movtS _ _ _ | .movfD _ _ _ | .movtD _ _ _
  | .movnS _ _ _ | .movzS _ _ _ | .movnD _ _ _ | .movzD _ _ _
  | .movf _ _ _ | .movt _ _ _
  | .maddS _ _ _ _ | .msubS _ _ _ _ | .nmaddS _ _ _ _ | .nmsubS _ _ _ _
  | .maddD _ _ _ _ | .msubD _ _ _ _ | .nmaddD _ _ _ _ | .nmsubD _ _ _ _
  | .bc1f _ _ | .bc1t _ _ | .bc1fl _ _ | .bc1tl _ _ => true
  | _ => false

/-- Whether a word that does **not** decode belongs to coprocessor 1's
encoding space: opcode COP1 (0x11) or COP1X (0x13), or SPECIAL with the
`MOVCI` function (0x01). For these, Coprocessor Unusable takes precedence
over Reserved Instruction when `Status.CU1 = 0` (MD00090 Vol III Rev 6.02
§6.2.21, p.99: "… assuming that access to the coprocessor is allowed. If
access to the coprocessor is not allowed, a Coprocessor Unusable Exception
occurs instead"). -/
def isCop1Word (w : W32) : Bool :=
  opcodeOf w == 0x11#32 || opcodeOf w == 0x13#32 || (opcodeOf w == 0#32 && functOf w == 1#32)

/-- Whether a word belongs to coprocessor 2's encoding space: opcode COP2
(0x12), `LWC2` (0x32), `LDC2` (0x36), `SWC2` (0x3a), `SDC2` (0x3e). The model
has no coprocessor 2 (`Config1.C2 = 0`) and `Status.CU2` always reads 0, so
these always raise Coprocessor Unusable with `Cause.CE = 2` (MD00090 Vol III
Rev 6.02 §6.2.22, p.100). -/
def isCop2Word (w : W32) : Bool :=
  opcodeOf w == 0x12#32 || opcodeOf w == 0x32#32 || opcodeOf w == 0x36#32 ||
    opcodeOf w == 0x3a#32 || opcodeOf w == 0x3e#32

/-- The arithmetic environment of the current FCSR (`RM`, `Enables`, `FS`). -/
def fpEnv (s : State) : Mips.Fp.Env := Mips.Fp.envOf s.fcsr

/-- A condition-code field value as an index. -/
def ccIdx (cc : W32) : Fin 8 := Fin.ofNat 8 cc.toNat

/-- Floating-point condition code `cc` (`FPConditionCode(cc)`). -/
def readFcc (s : State) (cc : W32) : Bool := Mips.Fp.getCC s.fcsr (ccIdx cc)

/-- The double in the FPR pair named by `f` (its low register): the 32-bit
FPU register model with `Status.FR = 0` (MD00082 Vol I-A Rev 6.01 §6.4.1,
p.84): `FPR[f]` holds the low word, `FPR[f+1]` the high word. An odd `f` is
UNPREDICTABLE in the architecture; the pair `(f, f+1 mod 32)` is used
regardless (pin). -/
def readFpD (s : State) (f : W32) : BitVec 64 :=
  readFpReg s (regIdx (f + 1#32)) ++ readFpReg s (regIdx f)

/-- Write the double `v` into the FPR pair named by `f` (low word to
`FPR[f]`, high word to `FPR[f+1]`). -/
def writeFpD (s : State) (f : W32) (v : BitVec 64) : State :=
  writeFpReg (writeFpReg s (regIdx f) (v.extractLsb' 0 32)) (regIdx (f + 1#32))
    (v.extractLsb' 32 32)

/-- Complete an FP instruction that computed the 32-bit result `r.1` (a
single, or a word fixed-point value) for `FPR[fd]` and raised the IEEE
exceptions `r.2`. `Mips.Fp.fpUpdate` sets FCSR.Cause to exactly `r.2`; if one
of them is enabled the Floating Point exception is taken (ExcCode 15) with
the destination **not written** and FCSR.Flags unchanged; otherwise `r.2` is
ORed into FCSR.Flags, the result is written and execution continues
(MD00082 Vol I-A Rev 6.01 §6.7.1 p.98-99; Table 6.8 `Flags`, p.94). -/
def fpFinishS (s : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags) : State :=
  let u := Mips.Fp.fpUpdate s.fcsr r.2
  if u.2 then takeException { s with fcsr := u.1 } excCodeFPE
  else mkNext s (writeFpReg { s with fcsr := u.1 } (regIdx fd) r.1)

/-- As `fpFinishS`, for a 64-bit (double) result written to the pair `fd`. -/
def fpFinishD (s : State) (fd : W32) (r : BitVec 64 × Mips.Fp.Flags) : State :=
  let u := Mips.Fp.fpUpdate s.fcsr r.2
  if u.2 then takeException { s with fcsr := u.1 } excCodeFPE
  else mkNext s (writeFpD { s with fcsr := u.1 } fd r.1)

/-- Complete a `C.cond.fmt`: as `fpFinishS`, the "result" being the Boolean
written to condition code `cc` ("If the Invalid Operation Enable bit is set
in the FCSR, no result is written and an Invalid Operation exception is taken
immediately. Otherwise, the Boolean result is written into condition code
CC" — MD00086 Vol II-A Rev 6.06, C.cond.fmt, p.110). -/
def fpFinishCmp (s : State) (cc : W32) (r : Bool × Mips.Fp.Flags) : State :=
  let u := Mips.Fp.fpUpdate s.fcsr r.2
  if u.2 then takeException { s with fcsr := u.1 } excCodeFPE
  else mkNext s { s with fcsr := Mips.Fp.setCC u.1 (ccIdx cc) r.1 }

/-- `PRId` (CP0 register 15, select 0; MD00090 Vol III Rev 6.02 §9.40,
Table 9.57, p.221): Company ID 1 (nonzero marks a MIPS32 processor),
Company Options, Processor ID and Revision 0 — an environment constant that
names no real product. -/
def prIdValue : W32 := 0x00010000

/-- `Config` (CP0 register 16, select 0; MD00090 Vol III Rev 6.02 §9.45,
Table 9.64, p.233-235; Appendix A.1.2, Figure A.3 / Table A.2, p.317): `M` = 1 (Config1
present), `BE` = 1 (big-endian), `AT` = 0 (MIPS32), `AR` = 1 (Release 2), `MT` = 3 (Fixed
Mapping MMU, "See “Fixed Mapping MMU” on page 313"), `Impl` = 0, `VI` = 0, and the three
Read/Write cacheability fields: `K23` (bits 30..28, `s.cp0ConfigK23`), `KU` (bits 27..25,
`s.cp0ConfigKU`) and `K0` (bits 2..0, `s.cp0ConfigK0`), reset `K0 = 2` (Uncached, Table 9.12
p.133; "Suggested", §6.2.5 p.90) and `K23 = KU = 2` (their reset state is "Undefined", p.233,
pinned like `K0`). So `configValue` is `0x8000_8580` plus the three fields (`0xA400_8582` after
Reset). `mtc0` stores the written bits 30..28, 27..25 and 2..0 into them unchanged (every 3-bit
value is accepted; pre-Release 6 the manual does not say what a write of an unsupported
attribute does: "For Release 6, writes of unsupported values are ignored", p.233, p.235). The
model has no cache, so they have no effect on anything else. The other fields are read-only. -/
def configValue (s : State) : W32 :=
  0x80008580#32 ||| (s.cp0ConfigK23.setWidth 32 <<< 28) ||| (s.cp0ConfigKU.setWidth 32 <<< 25) |||
    s.cp0ConfigK0.setWidth 32

/-- `Config1` (CP0 register 16, select 1; MD00090 Vol III Rev 6.02 §9.46,
Table 9.65, p.237-240): `FP` = 1 (FPU implemented) and nothing else — `M` = 0 (no
Config2), `MMU Size - 1` = 0, no caches (`IL` = `DL` = 0), no coprocessor 2, MDMX,
performance counters, watch registers, MIPS16e or EJTAG. `MMU Size - 1` is "Number of entries
in the TLB minus one ... The value zero is implied by ConfigMT having a value of ‘none’" (p.237);
the manual says nothing for a Fixed Mapping MMU (`MT = 3`), which has no TLB: 0 is the only value
the field can take that claims no more than one entry (pin). -/
def config1Value : W32 := 0x00000001

/-- The effect of the already-fetched, already-decoded instruction `instr`
in state `s`, **after** `execInstr`'s two guards (no control transfer in a
delay slot; coprocessor 1 usable for the instructions that need it). Total:
every case yields the next state (possibly at the exception vector). -/
def execBody (s : State) (instr : Instruction) : State :=
  match instr with
  -- R-type reg/reg/reg arithmetic
  | .add rs rt rd =>
    let av := readReg s (regIdx rs)
    let bv := readReg s (regIdx rt)
    let sumBV := av + bv
    if addOverflows (asSigned av) (asSigned bv) (asSigned sumBV) then
      takeException s excCodeOv
    else
      mkNext s (writeReg s (regIdx rd) sumBV)
  | .addu rs rt rd =>
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) + readReg s (regIdx rt)))
  | .sub rs rt rd =>
    let av := readReg s (regIdx rs)
    let bv := readReg s (regIdx rt)
    let diffBV := av - bv
    if subOverflows (asSigned av) (asSigned bv) (asSigned diffBV) then
      takeException s excCodeOv
    else
      mkNext s (writeReg s (regIdx rd) diffBV)
  | .subu rs rt rd =>
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) - readReg s (regIdx rt)))
  | .and rs rt rd =>
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) &&& readReg s (regIdx rt)))
  | .or rs rt rd =>
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) ||| readReg s (regIdx rt)))
  | .xor rs rt rd =>
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) ^^^ readReg s (regIdx rt)))
  | .nor rs rt rd =>
    mkNext s (writeReg s (regIdx rd) (~~~(readReg s (regIdx rs) ||| readReg s (regIdx rt))))
  | .slt rs rt rd =>
    let v := if asSigned (readReg s (regIdx rs)) < asSigned (readReg s (regIdx rt))
             then 1#32 else 0#32
    mkNext s (writeReg s (regIdx rd) v)
  | .sltu rs rt rd =>
    let v := if (readReg s (regIdx rs)).toNat < (readReg s (regIdx rt)).toNat
             then 1#32 else 0#32
    mkNext s (writeReg s (regIdx rd) v)
  -- Conditional move: `$rd` is left *unchanged*, not zeroed, when the
  -- condition fails (MIPS32r2 `movn`/`movz`; docs/spec/INSTRUCTION-REF.md).
  | .movn rs rt rd =>
    if readReg s (regIdx rt) != 0#32 then
      mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs)))
    else
      mkNext s s
  | .movz rs rt rd =>
    if readReg s (regIdx rt) == 0#32 then
      mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs)))
    else
      mkNext s s
  -- R-type shifts
  | .sll rd rt shamt =>
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt) <<< shamt.toNat))
  | .srl rd rt shamt =>
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt) >>> shamt.toNat))
  | .sra rd rt shamt =>
    mkNext s (writeReg s (regIdx rd) ((readReg s (regIdx rt)).sshiftRight shamt.toNat))
  -- R-type variable shifts (MIPS32): the shift amount comes from `$rs`'s
  -- low 5 bits (`extractLsb 4 0`), not a fixed `shamt` field \u2014 so e.g. a
  -- shift-amount register holding 33 (0b100001) behaves identically to one
  -- holding 1, per the real MIPS32 ISA (docs/spec/MIPS-COVERAGE-GAPS.md §3.4).
  | .sllv rd rt rs =>
    let amt := ((readReg s (regIdx rs)).extractLsb 4 0).toNat
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt) <<< amt))
  | .srlv rd rt rs =>
    let amt := ((readReg s (regIdx rs)).extractLsb 4 0).toNat
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt) >>> amt))
  | .srav rd rt rs =>
    let amt := ((readReg s (regIdx rs)).extractLsb 4 0).toNat
    mkNext s (writeReg s (regIdx rd) ((readReg s (regIdx rt)).sshiftRight amt))
  -- R-type rotate (MIPS32r2): bits shifted off the bottom wrap around to the
  -- top, unlike `srl`/`srlv`'s zero-fill on the same input
  -- (docs/spec/MIPS-COVERAGE-GAPS.md section 3.4). `BitVec.rotateRight` already
  -- reduces its shift amount mod the bitvector width, matching the real
  -- MIPS32 `sa`/`$rs & 0x1f` range (0-31) exactly.
  | .rotr rd rt sa =>
    mkNext s (writeReg s (regIdx rd) ((readReg s (regIdx rt)).rotateRight sa.toNat))
  | .rotrv rd rt rs =>
    let amt := ((readReg s (regIdx rs)).extractLsb 4 0).toNat
    mkNext s (writeReg s (regIdx rd) ((readReg s (regIdx rt)).rotateRight amt))
  -- R-type mult/div
  | .mult rs rt =>
    let a := asSigned (readReg s (regIdx rs))
    let b := asSigned (readReg s (regIdx rt))
    let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
    mkNext s { s with lo := prod64.extractLsb 31 0, hi := prod64.extractLsb 63 32 }
  | .multu rs rt =>
    let a := (readReg s (regIdx rs)).toNat
    let b := (readReg s (regIdx rt)).toNat
    let prod64 : BitVec 64 := BitVec.ofNat 64 (a * b)
    mkNext s { s with lo := prod64.extractLsb 31 0, hi := prod64.extractLsb 63 32 }
  | .div rs rt =>
    let a := asSigned (readReg s (regIdx rs))
    let b := asSigned (readReg s (regIdx rt))
    if b == 0 then
      -- SPEC-NOTES §9.2: hi/lo unchanged.
      mkNext s s
    else
      mkNext s { s with lo := ofInt32 (a.tdiv b), hi := ofInt32 (a.tmod b) }
  | .divu rs rt =>
    let a := (readReg s (regIdx rs)).toNat
    let b := (readReg s (regIdx rt)).toNat
    if b == 0 then
      mkNext s s
    else
      mkNext s { s with lo := BitVec.ofNat 32 (a / b), hi := BitVec.ofNat 32 (a % b) }
  -- SPECIAL2 multiply-accumulate (MIPS32): same signed/unsigned 64-bit
  -- product formation as `mult`/`multu` above, but added to (or subtracted
  -- from) the *existing* `{hi,lo}` pair instead of overwriting it. The
  -- 64-bit add/subtract is plain `BitVec 64` arithmetic, which already
  -- wraps on overflow -- no overflow trap, matching `mult`'s existing
  -- non-trapping precedent (docs/spec/MIPS-COVERAGE-GAPS.md §3.5). `hi ++ lo`
  -- reassembles the current 64-bit accumulator (`hi` is the high word).
  | .madd rs rt =>
    let a := asSigned (readReg s (regIdx rs))
    let b := asSigned (readReg s (regIdx rt))
    let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
    let acc64 : BitVec 64 := s.hi ++ s.lo
    let sum64 := acc64 + prod64
    mkNext s { s with lo := sum64.extractLsb 31 0, hi := sum64.extractLsb 63 32 }
  | .maddu rs rt =>
    let a := (readReg s (regIdx rs)).toNat
    let b := (readReg s (regIdx rt)).toNat
    let prod64 : BitVec 64 := BitVec.ofNat 64 (a * b)
    let acc64 : BitVec 64 := s.hi ++ s.lo
    let sum64 := acc64 + prod64
    mkNext s { s with lo := sum64.extractLsb 31 0, hi := sum64.extractLsb 63 32 }
  | .msub rs rt =>
    let a := asSigned (readReg s (regIdx rs))
    let b := asSigned (readReg s (regIdx rt))
    let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
    let acc64 : BitVec 64 := s.hi ++ s.lo
    let diff64 := acc64 - prod64
    mkNext s { s with lo := diff64.extractLsb 31 0, hi := diff64.extractLsb 63 32 }
  | .msubu rs rt =>
    let a := (readReg s (regIdx rs)).toNat
    let b := (readReg s (regIdx rt)).toNat
    let prod64 : BitVec 64 := BitVec.ofNat 64 (a * b)
    let acc64 : BitVec 64 := s.hi ++ s.lo
    let diff64 := acc64 - prod64
    mkNext s { s with lo := diff64.extractLsb 31 0, hi := diff64.extractLsb 63 32 }
  | .mflo rd => mkNext s (writeReg s (regIdx rd) s.lo)
  | .mfhi rd => mkNext s (writeReg s (regIdx rd) s.hi)
  -- R-type move, write direction: the write-direction counterparts to
  -- `mfhi`/`mflo` above (docs/spec/MIPS-COVERAGE-GAPS.md §3.5).
  | .mthi rs => mkNext s { s with hi := readReg s (regIdx rs) }
  | .mtlo rs => mkNext s { s with lo := readReg s (regIdx rs) }
  -- SPECIAL2 bit-count (MIPS32)
  | .clo rs rd =>
    mkNext s (writeReg s (regIdx rd) (BitVec.ofNat 32 (countLeadingOnes (readReg s (regIdx rs)))))
  | .clz rs rd =>
    mkNext s (writeReg s (regIdx rd) (BitVec.ofNat 32 (countLeadingZeros (readReg s (regIdx rs)))))
  -- SPECIAL2 GPR multiply (MIPS32): `$rd` gets the low 32 bits of the
  -- signed product, exactly the bits `mult`+`mflo` would leave in `lo`
  -- (two's-complement multiplication's low bits don't depend on the sign
  -- interpretation of the operands, so plain `W32` `*` already wraps
  -- correctly here \u2014 no need to go through `asSigned`/`BitVec.ofInt` the
  -- way `.mult` does). `hi`/`lo` are deliberately left **unchanged**: real
  -- MIPS32 hardware leaves them unpredictable after `mul`, and this is the
  -- simplest deterministic choice for this model (see `Instruction.mul`'s
  -- docstring and `docs/spec/INSTRUCTION-REF.md`).
  | .mul rs rt rd =>
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) * readReg s (regIdx rt)))
  -- SPECIAL3 BSHFL sign-extend (MIPS32r2)
  | .seb rd rt =>
    mkNext s (writeReg s (regIdx rd) (signExtLowByte (readReg s (regIdx rt))))
  | .seh rd rt =>
    mkNext s (writeReg s (regIdx rd) (signExt16 (readReg s (regIdx rt))))
  -- SPECIAL3 BSHFL word-swap-bytes-within-halfwords (MIPS32r2): swap the
  -- two bytes of each 16-bit half of `$rt` independently; the halfwords
  -- themselves stay in their original word positions (not a full 32-bit
  -- byte-reverse -- that's `wsbh` + `rotr 16`, not modeled as a single op).
  | .wsbh rd rt =>
    let v := readReg s (regIdx rt)
    let b0 := v &&& 0xff#32
    let b1 := (v >>> 8) &&& 0xff#32
    let b2 := (v >>> 16) &&& 0xff#32
    let b3 := (v >>> 24) &&& 0xff#32
    let result := (b2 <<< 24) ||| (b3 <<< 16) ||| (b0 <<< 8) ||| b1
    mkNext s (writeReg s (regIdx rd) result)
  -- SPECIAL3 bitfield extract/insert (MIPS32r2;
  -- docs/spec/MIPS-COVERAGE-GAPS.md section 3.4). `pos`/`size` are already the
  -- semantic values (`Instruction.decode` did the raw-field +-1 arithmetic),
  -- so this is pure bit masking -- no special-casing for the real
  -- `pos + size <= 32` hardware constraint, per this track's brief.
  | .ext rt rs pos size =>
    let field := (readReg s (regIdx rs) >>> pos.toNat) &&& lowBitsMask size.toNat
    mkNext s (writeReg s (regIdx rt) field)
  | .ins rt rs pos size =>
    let mask := lowBitsMask size.toNat
    let srcField := (readReg s (regIdx rs) &&& mask) <<< pos.toNat
    let clearMask := ~~~(mask <<< pos.toNat)
    let newVal := (readReg s (regIdx rt) &&& clearMask) ||| srcField
    mkNext s (writeReg s (regIdx rt) newVal)
  -- I-type arith/logic
  | .addi rs rt imm =>
    let av := readReg s (regIdx rs)
    let bv := signExt16 imm
    let sumBV := av + bv
    if addOverflows (asSigned av) (asSigned bv) (asSigned sumBV) then
      takeException s excCodeOv
    else
      mkNext s (writeReg s (regIdx rt) sumBV)
  | .addiu rs rt imm =>
    mkNext s (writeReg s (regIdx rt) (readReg s (regIdx rs) + signExt16 imm))
  | .slti rs rt imm =>
    let v := if asSigned (readReg s (regIdx rs)) < asSigned (signExt16 imm)
             then 1#32 else 0#32
    mkNext s (writeReg s (regIdx rt) v)
  | .sltiu rs rt imm =>
    let v := if (readReg s (regIdx rs)).toNat < (signExt16 imm).toNat
             then 1#32 else 0#32
    mkNext s (writeReg s (regIdx rt) v)
  | .andi rs rt imm =>
    mkNext s (writeReg s (regIdx rt) (readReg s (regIdx rs) &&& zeroExt16 imm))
  | .ori rs rt imm =>
    mkNext s (writeReg s (regIdx rt) (readReg s (regIdx rs) ||| zeroExt16 imm))
  | .xori rs rt imm =>
    mkNext s (writeReg s (regIdx rt) (readReg s (regIdx rs) ^^^ zeroExt16 imm))
  | .lui rt imm =>
    mkNext s (writeReg s (regIdx rt) (zeroExt16 imm <<< 16))
  -- Memory access: effective address = $rs + sign-extended offset
  -- (SPEC-NOTES §9.3 — we follow the ISA, not MARS's lw/sw zero-extension bug).
  | .lw rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemWord s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some v => mkNext s (writeReg s (regIdx rt) v)
  | .sw rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match writeMemWord s addr (readReg s (regIdx rt)) with
    | none => takeAddressException s excCodeAdES addr
    | some s' => mkNext s { s' with llBit := false }
  | .lb rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemByte s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some b => mkNext s (writeReg s (regIdx rt) (signExtByte b))
  | .lbu rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemByte s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some b => mkNext s (writeReg s (regIdx rt) (zeroExtByte b))
  | .lh rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemHalf s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some h => mkNext s (writeReg s (regIdx rt) (signExt16 h))
  | .lhu rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemHalf s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some h => mkNext s (writeReg s (regIdx rt) h)
  | .sh rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match writeMemHalf s addr (readReg s (regIdx rt)) with
    | none => takeAddressException s excCodeAdES addr
    | some s' => mkNext s { s' with llBit := false }
  -- `sb`: `StoreMemory(BYTE, GPR[rt]7..0)` at `base + sext(offset)`; no
  -- alignment requirement, so no Address Error. Clears `llBit` like every
  -- other store (the model's pinned choice; see `State.llBit`).
  | .sb rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match writeMemByte s addr ((readReg s (regIdx rt)) &&& 0xff#32).toNat.toUInt8 with
    | none => takeAddressException s excCodeAdES addr
    | some s' => mkNext s { s' with llBit := false }
  -- `ll`/`sc`: real MIPS32 atomic synchronization primitives (opcodes
  -- 0x30/0x38; MD00086 Rev 2.50 §3.2). `ll` loads like `lw` and additionally
  -- sets `llBit`; `sc` performs its store only if `llBit` is set (checked
  -- *before* clearing it), writing success/failure back to `$rt`, and
  -- always clears `llBit` afterward -- see `Types.lean`'s `llBit` docstring
  -- for this model's single-hart simplification.
  | .ll rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemWord s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some v => mkNext s { (writeReg s (regIdx rt) v) with llBit := true, llAddr := addr }
  | .sc rs rt imm =>
    -- The effective-address alignment check happens unconditionally, exactly
    -- as for `sw` (real MIPS32 computes/validates the memory reference
    -- regardless of whether `LLbit` ends up permitting the store); only
    -- *committing* `writeMemWord`'s result is conditional on `s.llBit`,
    -- which is checked before it is cleared below.
    let addr := readReg s (regIdx rs) + signExt16 imm
    match writeMemWord s addr (readReg s (regIdx rt)) with
    | none => takeAddressException s excCodeAdES addr
    | some stored =>
      -- "An SC will fail if the aligned address of the SC does not match
      -- that of the preceding LL" (MD00086 Vol II-A Rev 6.06, SC, p.347).
      if s.llBit && s.llAddr == addr then
        mkNext s { (writeReg stored (regIdx rt) 1#32) with llBit := false }
      else
        mkNext s { (writeReg s (regIdx rt) 0#32) with llBit := false }
  -- `sync`: a no-op for every `stype` (single hart, nothing to order).
  | .sync _ => mkNext s s
  -- `pref`: "Any action, including doing nothing, is permitted … PREF does
  -- not cause addressing-related exceptions" (MD00086 Vol II-A Rev 6.06,
  -- PREF, p.321). A no-op; in particular it does not touch `llBit`.
  | .pref _ _ _ => mkNext s s
  -- `synci` (MD00086 Vol II-A Rev 6.06, SYNCI, p.412-413): Operation
  -- `vaddr ← GPR[base] + sign_extend(offset); SynchronizeCacheLines(vaddr)`.
  -- The model has no caches (`Config1.IL = DL = 0`, `config1Value`) and
  -- fetches instructions straight from `physMem`, so every store is already
  -- visible to instruction fetch and there is no cache line to synchronize:
  -- the operation has no effect on architectural state. Its exceptions are
  -- TLB, Cache Error and an implementation-dependent AdEL for kernel
  -- addresses ("It is implementation dependent whether such an exception does
  -- occur", p.412); the model has no TLB or cache and raises none (pin).
  | .synci rs imm =>
    let _addr := readReg s (regIdx rs) + signExt16 imm
    mkNext s s
  -- `lwl`/`lwr`/`swl`/`swr`: real MIPS32 classic (pre-r6) unaligned
  -- load/store pair (MD00086 Vol II-A Rev 6.06, LWL p.240, LWR p.247, SWL p.397, SWR p.401;
  -- `docs/spec/MIPS-COVERAGE-GAPS.md` §3.6). Unlike `lw`/`sw`, `addr` has no alignment
  -- requirement. The only Address Error is the MMU's: a kernel address referenced from User Mode
  -- (`translate`; AdEL for `lwl`/`lwr`, AdES for `swl`/`swr`, `BadVAddr = addr`). Every byte
  -- touched lies in the aligned word containing `addr`, hence in `addr`'s 512 MB segment, so the
  -- first byte access decides: when it succeeds the others succeed too, and their `.getD`
  -- fallbacks are never used. `off = addr.toNat % 4` selects how many bytes straddle the word
  -- boundary. See `docs/spec/INSTRUCTION-REF.md`'s dedicated section for the worked
  -- byte-position example this case-split implements.
  | .lwl rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemByte s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some b0 =>
      let off := addr.toNat % 4
      let old := readReg s (regIdx rt)
      let v :=
        match off with
        | 0 =>
          let b1 := (readMemByte s (addr + 1#32)).getD 0
          let b2 := (readMemByte s (addr + 2#32)).getD 0
          let b3 := (readMemByte s (addr + 3#32)).getD 0
          setByteSlot (setByteSlot (setByteSlot (setByteSlot old 0 b0) 1 b1) 2 b2) 3 b3
        | 1 =>
          let b1 := (readMemByte s (addr + 1#32)).getD 0
          let b2 := (readMemByte s (addr + 2#32)).getD 0
          setByteSlot (setByteSlot (setByteSlot old 0 b0) 1 b1) 2 b2
        | 2 =>
          let b1 := (readMemByte s (addr + 1#32)).getD 0
          setByteSlot (setByteSlot old 0 b0) 1 b1
        | _ =>  -- off = 3 (Nat match needs a default; addr.toNat % 4 is always < 4)
          setByteSlot old 0 b0
      mkNext s (writeReg s (regIdx rt) v)
  | .lwr rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemByte s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some b3 =>
      let off := addr.toNat % 4
      let old := readReg s (regIdx rt)
      let v :=
        match off with
        | 0 =>
          setByteSlot old 3 b3
        | 1 =>
          let b2 := (readMemByte s (addr - 1#32)).getD 0
          setByteSlot (setByteSlot old 2 b2) 3 b3
        | 2 =>
          let b1 := (readMemByte s (addr - 2#32)).getD 0
          let b2 := (readMemByte s (addr - 1#32)).getD 0
          setByteSlot (setByteSlot (setByteSlot old 1 b1) 2 b2) 3 b3
        | _ =>  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
          let b0 := (readMemByte s (addr - 3#32)).getD 0
          let b1 := (readMemByte s (addr - 2#32)).getD 0
          let b2 := (readMemByte s (addr - 1#32)).getD 0
          setByteSlot (setByteSlot (setByteSlot (setByteSlot old 0 b0) 1 b1) 2 b2) 3 b3
      mkNext s (writeReg s (regIdx rt) v)
  -- `swl`/`swr` are store-class, so (like `sw`/`sh`/`swc1`) they clear
  -- `llBit` -- see the module docstring's `ll`/`sc` paragraph.
  | .swl rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    let v := readReg s (regIdx rt)
    match writeMemByte s addr (getByteSlot v 0) with
    | none => takeAddressException s excCodeAdES addr
    | some s1 =>
      let off := addr.toNat % 4
      let s' :=
        match off with
        | 0 =>
          let s2 := (writeMemByte s1 (addr + 1#32) (getByteSlot v 1)).getD s1
          let s3 := (writeMemByte s2 (addr + 2#32) (getByteSlot v 2)).getD s2
          (writeMemByte s3 (addr + 3#32) (getByteSlot v 3)).getD s3
        | 1 =>
          let s2 := (writeMemByte s1 (addr + 1#32) (getByteSlot v 1)).getD s1
          (writeMemByte s2 (addr + 2#32) (getByteSlot v 2)).getD s2
        | 2 => (writeMemByte s1 (addr + 1#32) (getByteSlot v 1)).getD s1
        | _ => s1  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
      mkNext s { s' with llBit := false }
  | .swr rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    let v := readReg s (regIdx rt)
    match writeMemByte s addr (getByteSlot v 3) with
    | none => takeAddressException s excCodeAdES addr
    | some s1 =>
      let off := addr.toNat % 4
      let s' :=
        match off with
        | 0 => s1
        | 1 => (writeMemByte s1 (addr - 1#32) (getByteSlot v 2)).getD s1
        | 2 =>
          let s2 := (writeMemByte s1 (addr - 2#32) (getByteSlot v 1)).getD s1
          (writeMemByte s2 (addr - 1#32) (getByteSlot v 2)).getD s2
        | _ =>  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
          let s2 := (writeMemByte s1 (addr - 3#32) (getByteSlot v 0)).getD s1
          let s3 := (writeMemByte s2 (addr - 2#32) (getByteSlot v 1)).getD s2
          (writeMemByte s3 (addr - 1#32) (getByteSlot v 2)).getD s3
      mkNext s { s' with llBit := false }
  -- Control flow: one architectural delay slot per branch/jump (SPEC-NOTES
  -- §9 item 1; INSTRUCTION-REF Global rule 3). No branch/jump changes `pc`
  -- to its target: it moves to `pcNext = pc + 4` (the delay-slot
  -- instruction) and records where control goes after that instruction in
  -- `pendingBranch` — the target `pcNext + (signExt16 imm <<< 2)` if taken,
  -- the fall-through address `pc + 8` if not. `advance`/`mkNext` commits it
  -- when the delay-slot instruction retires; `exceptionEntry` abandons it if
  -- that instruction faults. Jumps schedule a target whose top 4 bits come
  -- from `pcNext`.
  | .beq rs rt imm =>
    let pcNext := s.pc + 4#32
    if readReg s (regIdx rs) == readReg s (regIdx rt) then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  | .bne rs rt imm =>
    let pcNext := s.pc + 4#32
    if readReg s (regIdx rs) == readReg s (regIdx rt) then
      { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
    else
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
  | .blez rs imm =>
    let pcNext := s.pc + 4#32
    if asSigned (readReg s (regIdx rs)) ≤ 0 then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  | .bgtz rs imm =>
    let pcNext := s.pc + 4#32
    if 0 < asSigned (readReg s (regIdx rs)) then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  -- REGIMM zero-comparison branches (opcode 0x01; MD00086 Rev 2.50 §3.2,
  -- Table 3-2). `bltz`/`bgez` are plain conditional branches, same shape as
  -- `blez`/`bgtz` above. `bltzal`/`bgezal` additionally link `$ra` to
  -- `pcNext + 4` (`pc + 8`, past the delay slot, same convention as `jal`)
  -- -- real MIPS32 performs this link **unconditionally**, on every
  -- execution of the instruction, regardless of whether the branch itself
  -- is taken; only the branch transfer is conditional.
  | .bltz rs imm =>
    let pcNext := s.pc + 4#32
    if asSigned (readReg s (regIdx rs)) < 0 then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  | .bgez rs imm =>
    let pcNext := s.pc + 4#32
    if 0 ≤ asSigned (readReg s (regIdx rs)) then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  | .bltzal rs imm =>
    let pcNext := s.pc + 4#32
    let s' := writeReg s 31 (pcNext + 4#32)
    if asSigned (readReg s (regIdx rs)) < 0 then
      { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s' with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  | .bgezal rs imm =>
    let pcNext := s.pc + 4#32
    let s' := writeReg s 31 (pcNext + 4#32)
    if 0 ≤ asSigned (readReg s (regIdx rs)) then
      { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s' with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  -- "Branch likely" family (deprecated in MIPS32, removed in Release 6 --
  -- MD00086 Rev 2.50 Table 3-10). **Taken**: exactly like the non-likely
  -- counterpart (delay slot executes, then the target). **Not taken**: the
  -- delay-slot instruction is nullified -- never fetched, decoded or
  -- executed -- so this step moves `pc` directly to `pc + 8` and leaves
  -- `pendingBranch = none`. The nullification is therefore part of `step`
  -- itself. `bltzall`/`bgezall` still link `$ra` unconditionally.
  | .beql rs rt imm =>
    let pcNext := s.pc + 4#32
    if readReg s (regIdx rs) == readReg s (regIdx rt) then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := s.pc + 8#32 }
  | .bnel rs rt imm =>
    let pcNext := s.pc + 4#32
    if readReg s (regIdx rs) == readReg s (regIdx rt) then
      { s with pc := s.pc + 8#32 }
    else
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
  | .blezl rs imm =>
    let pcNext := s.pc + 4#32
    if asSigned (readReg s (regIdx rs)) ≤ 0 then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := s.pc + 8#32 }
  | .bgtzl rs imm =>
    let pcNext := s.pc + 4#32
    if 0 < asSigned (readReg s (regIdx rs)) then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := s.pc + 8#32 }
  | .bltzl rs imm =>
    let pcNext := s.pc + 4#32
    if asSigned (readReg s (regIdx rs)) < 0 then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := s.pc + 8#32 }
  | .bgezl rs imm =>
    let pcNext := s.pc + 4#32
    if 0 ≤ asSigned (readReg s (regIdx rs)) then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := s.pc + 8#32 }
  | .bltzall rs imm =>
    let pcNext := s.pc + 4#32
    let s' := writeReg s 31 (pcNext + 4#32)
    if asSigned (readReg s (regIdx rs)) < 0 then
      { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s' with pc := s.pc + 8#32 }
  | .bgezall rs imm =>
    let pcNext := s.pc + 4#32
    let s' := writeReg s 31 (pcNext + 4#32)
    if 0 ≤ asSigned (readReg s (regIdx rs)) then
      { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s' with pc := s.pc + 8#32 }
  | .j target =>
    let pcNext := s.pc + 4#32
    { s with pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) }
  | .jal target =>
    -- `$ra` links to `pc + 8` — past the delay slot — not `pcNext` (`pc + 4`):
    -- real MIPS32's `jal` link value is the address of the instruction
    -- *after* the delay slot, since the delay-slot instruction itself still
    -- executes before control reaches `$ra` on return.
    let pcNext := s.pc + 4#32
    let linkVal := pcNext + 4#32
    let s' := writeReg s 31 linkVal
    { s' with pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) }
  -- Register-indirect jump/call (real MIPS32 `jr`/`jalr`, MD00086 §3.2):
  -- same one-instruction delay-slot scheduling as `j`/`jal` above, but the
  -- target is the raw 32-bit value read from `$rs` instead of composed from
  -- the 26-bit `target` field. A misaligned `$rs` value is not special-cased
  -- here: the delay slot executes, `pc` becomes the misaligned target, and
  -- the next `step` raises Address Error (AdEL) on the fetch, with
  -- `EPC = BadVAddr =` that target -- as the architecture specifies.
  | .jr rs =>
    let pcNext := s.pc + 4#32
    { s with pc := pcNext, pendingBranch := some (readReg s (regIdx rs)) }
  | .jalr rs rd =>
    -- `$rd` links to `pc + 8` — past the delay slot — the same `jal` link-value
    -- convention as above. The link target is read before `$rd` is written,
    -- so `jalr $rs, $rs` (rd = rs) still reads the pre-write `$rs` value.
    let pcNext := s.pc + 4#32
    let linkVal := pcNext + 4#32
    let target := readReg s (regIdx rs)
    let s' := writeReg s (regIdx rd) linkVal
    { s' with pc := pcNext, pendingBranch := some target }
  -- Coprocessor 1 (FPU). Every arm below is reached only with
  -- `Status.CU1 = 1` (the `usesCop1` check above).
  -- Raw moves between GPRs and FPRs: no conversion, FCSR untouched.
  | .mfc1 rt fs =>
    mkNext s (writeReg s (regIdx rt) (readFpReg s (regIdx fs)))
  | .mtc1 rt fs =>
    mkNext s (writeFpReg s (regIdx fs) (readReg s (regIdx rt)))
  -- `mfhc1`/`mthc1`: the high word of the double in `fs` is `FPR[fs+1]`
  -- (FR = 0). "The results are UNPREDICTABLE if Status.FR = 0 and fs is odd"
  -- (MD00086 Vol II-A Rev 6.06, MFHC1 p.271, MTHC1 p.295); pinned to the
  -- same `fs + 1` register.
  | .mfhc1 rt fs =>
    mkNext s (writeReg s (regIdx rt) (readFpReg s (regIdx (fs + 1#32))))
  | .mthc1 rt fs =>
    mkNext s (writeFpReg s (regIdx (fs + 1#32)) (readReg s (regIdx rt)))
  -- `cfc1` (MD00086 Vol II-A Rev 6.06, CFC1, p.129-130): FIR (0), FCCR (25),
  -- FEXR (26), FENR (28), FCSR (31) via `Mips.Fp.readControl`. Any other
  -- register number is UNPREDICTABLE; pinned to read 0.
  | .cfc1 rt fs =>
    mkNext s (writeReg s (regIdx rt) ((Mips.Fp.readControl s.fcsr fs.toNat).getD 0#32))
  -- `ctc1` (MD00086 Vol II-A Rev 6.06, CTC1, p.149-151): the register is
  -- written (`Mips.Fp.writeControl`: reserved bits of the written value,
  -- UNPREDICTABLE if nonzero, are ignored; FIR is read-only), then
  -- `CheckFPException()`: "The register is written before the exception
  -- occurs". Any other register number is UNPREDICTABLE; pinned to a no-op.
  | .ctc1 rt fs =>
    match Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt)) with
    | none => mkNext s s
    | some f =>
      if Mips.Fp.fcsrTrapPending f then takeException { s with fcsr := f } excCodeFPE
      else mkNext s { s with fcsr := f }
  | .lwc1 rs ft imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemWord s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some v => mkNext s (writeFpReg s (regIdx ft) v)
  | .swc1 rs ft imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match writeMemWord s addr (readFpReg s (regIdx ft)) with
    | none => takeAddressException s excCodeAdES addr
    | some s' => mkNext s { s' with llBit := false }
  -- `ldc1`/`sdc1`: "An Address Error exception occurs if
  -- EffectiveAddress2..0 ≠ 0 (not doubleword-aligned)" (MD00086 Vol II-A
  -- Rev 6.06, LDC1 p.215, SDC1 p.362). Big-endian: the word at `addr` is the
  -- high half (`FPR[ft+1]`), the word at `addr + 4` the low half (`FPR[ft]`).
  | .ldc1 rs ft imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdEL addr
    else
    match readMemWord s addr, readMemWord s (addr + 4#32) with
    | some hi, some lo =>
      mkNext s (writeFpReg (writeFpReg s (regIdx ft) lo) (regIdx (ft + 1#32)) hi)
    | _, _ => takeAddressException s excCodeAdEL addr
  | .sdc1 rs ft imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdES addr
    else
    match writeMemWord s addr (readFpReg s (regIdx (ft + 1#32))) with
    | none => takeAddressException s excCodeAdES addr
    | some s' =>
      match writeMemWord s' (addr + 4#32) (readFpReg s (regIdx ft)) with
      | none => takeAddressException s excCodeAdES addr
      | some s'' => mkNext s { s'' with llBit := false }
  -- Indexed FP load/store (COP1X): effective address `GPR[base] + GPR[index]`
  -- (MD00086 Vol II-A Rev 6.06, LWXC1 p.254, LDXC1 p.218, SWXC1 p.406,
  -- SDXC1 p.364), same alignment rules as the displacement forms.
  | .lwxc1 fd index base =>
    let addr := readReg s (regIdx base) + readReg s (regIdx index)
    match readMemWord s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some v => mkNext s (writeFpReg s (regIdx fd) v)
  | .ldxc1 fd index base =>
    let addr := readReg s (regIdx base) + readReg s (regIdx index)
    if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdEL addr
    else
    match readMemWord s addr, readMemWord s (addr + 4#32) with
    | some hi, some lo =>
      mkNext s (writeFpReg (writeFpReg s (regIdx fd) lo) (regIdx (fd + 1#32)) hi)
    | _, _ => takeAddressException s excCodeAdEL addr
  | .swxc1 fs index base =>
    let addr := readReg s (regIdx base) + readReg s (regIdx index)
    match writeMemWord s addr (readFpReg s (regIdx fs)) with
    | none => takeAddressException s excCodeAdES addr
    | some s' => mkNext s { s' with llBit := false }
  | .sdxc1 fs index base =>
    let addr := readReg s (regIdx base) + readReg s (regIdx index)
    if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdES addr
    else
    match writeMemWord s addr (readFpReg s (regIdx (fs + 1#32))) with
    | none => takeAddressException s excCodeAdES addr
    | some s' =>
      match writeMemWord s' (addr + 4#32) (readFpReg s (regIdx fs)) with
      | none => takeAddressException s excCodeAdES addr
      | some s'' => mkNext s { s'' with llBit := false }
  -- `prefx`: a no-op, like `pref` (MD00086 Vol II-A Rev 6.06, PREFX, p.329).
  | .prefx _ _ _ => mkNext s s
  -- Single-precision arithmetic: `Mips.Fp` on the raw bit patterns, under
  -- the FCSR environment; `fpFinishS` records the exceptions / traps.
  | .addS fd fs ft =>
    fpFinishS s fd (Mips.Fp.f32Add (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .subS fd fs ft =>
    fpFinishS s fd (Mips.Fp.f32Sub (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .mulS fd fs ft =>
    fpFinishS s fd (Mips.Fp.f32Mul (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .divS fd fs ft =>
    fpFinishS s fd (Mips.Fp.f32Div (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .sqrtS fd fs =>
    fpFinishS s fd (Mips.Fp.f32Sqrt (fpEnv s) (readFpReg s (regIdx fs)))
  -- `abs`/`neg` are arithmetic (`FIR.Has2008 = 0`): a NaN signals Invalid.
  | .absS fd fs => fpFinishS s fd (Mips.Fp.f32Abs (readFpReg s (regIdx fs)))
  | .negS fd fs => fpFinishS s fd (Mips.Fp.f32Neg (readFpReg s (regIdx fs)))
  | .recipS fd fs =>
    fpFinishS s fd (Mips.Fp.f32Recip (fpEnv s) (readFpReg s (regIdx fs)))
  | .rsqrtS fd fs =>
    fpFinishS s fd (Mips.Fp.f32Rsqrt (fpEnv s) (readFpReg s (regIdx fs)))
  -- `mov.fmt` is non-arithmetic: raw copy, FCSR untouched.
  | .movS fd fs =>
    mkNext s (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs)))
  -- Float → word: fixed rounding direction for round/trunc/ceil/floor,
  -- FCSR.RM for `cvt.w`.
  | .roundWS fd fs => fpFinishS s fd (Mips.Fp.f32ToW32 .RN (readFpReg s (regIdx fs)))
  | .truncWS fd fs => fpFinishS s fd (Mips.Fp.f32ToW32 .RZ (readFpReg s (regIdx fs)))
  | .ceilWS fd fs => fpFinishS s fd (Mips.Fp.f32ToW32 .RP (readFpReg s (regIdx fs)))
  | .floorWS fd fs => fpFinishS s fd (Mips.Fp.f32ToW32 .RM (readFpReg s (regIdx fs)))
  | .cvtWS fd fs =>
    fpFinishS s fd (Mips.Fp.f32ToW32 (Mips.Fp.getRM s.fcsr) (readFpReg s (regIdx fs)))
  | .cvtDS fd fs => fpFinishD s fd (Mips.Fp.f32ToF64 (readFpReg s (regIdx fs)))
  | .cvtSW fd fs => fpFinishS s fd (Mips.Fp.w32ToF32 (fpEnv s) (readFpReg s (regIdx fs)))
  | .cvtDW fd fs => fpFinishD s fd (Mips.Fp.w32ToF64F (readFpReg s (regIdx fs)))
  -- Double-precision arithmetic, on the register pairs.
  | .addD fd fs ft =>
    fpFinishD s fd (Mips.Fp.f64Add (fpEnv s) (readFpD s fs) (readFpD s ft))
  | .subD fd fs ft =>
    fpFinishD s fd (Mips.Fp.f64Sub (fpEnv s) (readFpD s fs) (readFpD s ft))
  | .mulD fd fs ft =>
    fpFinishD s fd (Mips.Fp.f64Mul (fpEnv s) (readFpD s fs) (readFpD s ft))
  | .divD fd fs ft =>
    fpFinishD s fd (Mips.Fp.f64Div (fpEnv s) (readFpD s fs) (readFpD s ft))
  | .sqrtD fd fs => fpFinishD s fd (Mips.Fp.f64Sqrt (fpEnv s) (readFpD s fs))
  | .absD fd fs => fpFinishD s fd (Mips.Fp.f64Abs (readFpD s fs))
  | .negD fd fs => fpFinishD s fd (Mips.Fp.f64Neg (readFpD s fs))
  | .recipD fd fs => fpFinishD s fd (Mips.Fp.f64Recip (fpEnv s) (readFpD s fs))
  | .rsqrtD fd fs => fpFinishD s fd (Mips.Fp.f64Rsqrt (fpEnv s) (readFpD s fs))
  | .movD fd fs => mkNext s (writeFpD s fd (readFpD s fs))
  | .roundWD fd fs => fpFinishS s fd (Mips.Fp.f64ToW32 .RN (readFpD s fs))
  | .truncWD fd fs => fpFinishS s fd (Mips.Fp.f64ToW32 .RZ (readFpD s fs))
  | .ceilWD fd fs => fpFinishS s fd (Mips.Fp.f64ToW32 .RP (readFpD s fs))
  | .floorWD fd fs => fpFinishS s fd (Mips.Fp.f64ToW32 .RM (readFpD s fs))
  | .cvtWD fd fs => fpFinishS s fd (Mips.Fp.f64ToW32 (Mips.Fp.getRM s.fcsr) (readFpD s fs))
  | .cvtSD fd fs => fpFinishS s fd (Mips.Fp.f64ToF32 (fpEnv s) (readFpD s fs))
  -- `C.cond.fmt`: the low 4 bits of `cond` select the predicate; the result
  -- goes to condition code `cc`.
  | .cCondS cond cc fs ft =>
    fpFinishCmp s cc
      (Mips.Fp.f32Compare (cond.setWidth 4) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .cCondD cond cc fs ft =>
    fpFinishCmp s cc (Mips.Fp.f64Compare (cond.setWidth 4) (readFpD s fs) (readFpD s ft))
  -- Conditional moves: non-arithmetic ("it causes no IEEE 754 exceptions,
  -- and the FCSR Cause and Flags fields are not modified" — MD00086 Vol II-A
  -- Rev 6.06, MOVF.fmt p.277); the destination keeps its value otherwise.
  | .movfS fd fs cc =>
    if readFcc s cc then mkNext s s
    else mkNext s (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs)))
  | .movtS fd fs cc =>
    if readFcc s cc then mkNext s (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs)))
    else mkNext s s
  | .movfD fd fs cc =>
    if readFcc s cc then mkNext s s else mkNext s (writeFpD s fd (readFpD s fs))
  | .movtD fd fs cc =>
    if readFcc s cc then mkNext s (writeFpD s fd (readFpD s fs)) else mkNext s s
  | .movnS fd fs rt =>
    if readReg s (regIdx rt) != 0#32 then
      mkNext s (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs)))
    else mkNext s s
  | .movzS fd fs rt =>
    if readReg s (regIdx rt) == 0#32 then
      mkNext s (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs)))
    else mkNext s s
  | .movnD fd fs rt =>
    if readReg s (regIdx rt) != 0#32 then mkNext s (writeFpD s fd (readFpD s fs)) else mkNext s s
  | .movzD fd fs rt =>
    if readReg s (regIdx rt) == 0#32 then mkNext s (writeFpD s fd (readFpD s fs)) else mkNext s s
  -- GPR conditional move on an FP condition code (`MOVCI`).
  | .movf rs cc rd =>
    if readFcc s cc then mkNext s s
    else mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs)))
  | .movt rs cc rd =>
    if readFcc s cc then mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs)))
    else mkNext s s
  -- Multiply-add family: unfused (`Mips.Fp.f32Madd` …).
  | .maddS fd fr fs ft =>
    fpFinishS s fd (Mips.Fp.f32Madd (fpEnv s) (readFpReg s (regIdx fr))
      (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .msubS fd fr fs ft =>
    fpFinishS s fd (Mips.Fp.f32Msub (fpEnv s) (readFpReg s (regIdx fr))
      (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .nmaddS fd fr fs ft =>
    fpFinishS s fd (Mips.Fp.f32Nmadd (fpEnv s) (readFpReg s (regIdx fr))
      (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .nmsubS fd fr fs ft =>
    fpFinishS s fd (Mips.Fp.f32Nmsub (fpEnv s) (readFpReg s (regIdx fr))
      (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .maddD fd fr fs ft =>
    fpFinishD s fd (Mips.Fp.f64Madd (fpEnv s) (readFpD s fr) (readFpD s fs) (readFpD s ft))
  | .msubD fd fr fs ft =>
    fpFinishD s fd (Mips.Fp.f64Msub (fpEnv s) (readFpD s fr) (readFpD s fs) (readFpD s ft))
  | .nmaddD fd fr fs ft =>
    fpFinishD s fd (Mips.Fp.f64Nmadd (fpEnv s) (readFpD s fr) (readFpD s fs) (readFpD s ft))
  | .nmsubD fd fr fs ft =>
    fpFinishD s fd (Mips.Fp.f64Nmsub (fpEnv s) (readFpD s fr) (readFpD s fs) (readFpD s ft))
  -- FP branches: same delay-slot scheduling as `beq`/`bne`; the likely
  -- forms nullify the delay slot when not taken (MD00086 Vol II-A Rev 6.06,
  -- BC1F p.56, BC1FL p.58, BC1T p.60, BC1TL p.62).
  | .bc1f cc imm =>
    let pcNext := s.pc + 4#32
    if readFcc s cc then
      { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
    else
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
  | .bc1t cc imm =>
    let pcNext := s.pc + 4#32
    if readFcc s cc then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  | .bc1fl cc imm =>
    let pcNext := s.pc + 4#32
    if readFcc s cc then
      { s with pc := s.pc + 8#32 }
    else
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
  | .bc1tl cc imm =>
    let pcNext := s.pc + 4#32
    if readFcc s cc then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := s.pc + 8#32 }
  -- `syscall`: "A system call exception occurs, immediately and
  -- unconditionally transferring control to the exception handler";
  -- Operation: `SignalException(SystemCall)` (MD00086 Vol II-A Rev 6.06,
  -- SYSCALL, p.415). The MARS-style print/exit services are not the
  -- processor's: the hosted run (`Semantics/Env.lean`) performs them *instead
  -- of* stepping when it sees a `syscall` selecting one.
  | .syscall _ => takeException s excCodeSys
  -- Trap-on-condition (coprocessor-0 exception model, real MIPS32 ISA; see
  -- `takeException` above and `docs/spec/INSTRUCTION-REF.md`). Trap-not-taken
  -- behaves like an ordinary instruction: `mkNext s` falls through to
  -- `pc + 4` with no CP0 state touched at all.
  | .teq rs rt _ =>
    if readReg s (regIdx rs) == readReg s (regIdx rt) then takeException s excCodeTr else mkNext s s
  | .tne rs rt _ =>
    if readReg s (regIdx rs) ≠ readReg s (regIdx rt) then takeException s excCodeTr else mkNext s s
  | .tlt rs rt _ =>
    if asSigned (readReg s (regIdx rs)) < asSigned (readReg s (regIdx rt))
    then takeException s excCodeTr else mkNext s s
  | .tge rs rt _ =>
    if asSigned (readReg s (regIdx rs)) ≥ asSigned (readReg s (regIdx rt))
    then takeException s excCodeTr else mkNext s s
  | .tltu rs rt _ =>
    if (readReg s (regIdx rs)).toNat < (readReg s (regIdx rt)).toNat
    then takeException s excCodeTr else mkNext s s
  | .tgeu rs rt _ =>
    if (readReg s (regIdx rs)).toNat ≥ (readReg s (regIdx rt)).toNat
    then takeException s excCodeTr else mkNext s s
  -- Trap-immediate (REGIMM, real MIPS32 ISA; `docs/spec/MIPS-COVERAGE-GAPS.md`
  -- §3.8): same coprocessor-0 trap model as `teq`/`tne`/etc. above, but
  -- comparing `$rs` against a sign-extended 16-bit immediate instead of a
  -- second register. `tgeiu`/`tltiu` sign-extend the immediate to 32 bits
  -- first, then compare the resulting bit pattern as unsigned — same
  -- convention `sltiu` already uses.
  | .teqi rs imm =>
    if readReg s (regIdx rs) == signExt16 imm then takeException s excCodeTr else mkNext s s
  | .tnei rs imm =>
    if readReg s (regIdx rs) ≠ signExt16 imm then takeException s excCodeTr else mkNext s s
  | .tgei rs imm =>
    if asSigned (readReg s (regIdx rs)) ≥ asSigned (signExt16 imm)
    then takeException s excCodeTr else mkNext s s
  | .tgeiu rs imm =>
    if (readReg s (regIdx rs)).toNat ≥ (signExt16 imm).toNat
    then takeException s excCodeTr else mkNext s s
  | .tlti rs imm =>
    if asSigned (readReg s (regIdx rs)) < asSigned (signExt16 imm)
    then takeException s excCodeTr else mkNext s s
  | .tltiu rs imm =>
    if (readReg s (regIdx rs)).toNat < (signExt16 imm).toNat
    then takeException s excCodeTr else mkNext s s
  -- break: unconditional trap (coprocessor-0 exception model).
  | .break _ => takeException s excCodeBp
  -- Coprocessor 0 register moves, for the `(rd, sel)` pairs of
  -- `isModeledCp0Reg`: (8,0) BadVAddr, (12,0) Status, (13,0) Cause, (14,0)
  -- EPC, (15,0) PRId, (15,1) EBase, (16,0) Config, (16,1) Config1, (30,0)
  -- ErrorEPC. `decode` only produces `mfc0`/`mtc0` for these; an
  -- `Instruction` value built by hand with any other pair raises Reserved
  -- Instruction, matching what the undecodable word would do. Outside Kernel
  -- Mode with `Status.CU0 = 0` they raise Coprocessor Unusable before reaching
  -- this arm (`execInstr`, `usesCop0`).
  | .mfc0 rt rd sel =>
    match rd.toNat, sel.toNat with
    | 8, 0 => mkNext s (writeReg s (regIdx rt) s.cp0BadVAddr)
    | 12, 0 => mkNext s (writeReg s (regIdx rt) s.cp0Status)
    | 13, 0 => mkNext s (writeReg s (regIdx rt) s.cp0Cause)
    | 14, 0 => mkNext s (writeReg s (regIdx rt) s.cp0Epc)
    | 15, 0 => mkNext s (writeReg s (regIdx rt) prIdValue)
    | 15, 1 => mkNext s (writeReg s (regIdx rt) (ebaseValue s))
    | 16, 0 => mkNext s (writeReg s (regIdx rt) (configValue s))
    | 16, 1 => mkNext s (writeReg s (regIdx rt) config1Value)
    | 30, 0 => mkNext s (writeReg s (regIdx rt) s.cp0ErrorEpc)
    | _, _ => takeException s excCodeRI
  -- `mtc0` write masks: `BadVAddr`, `PRId`, `Config1` are
  -- read-only (the write is ignored); `Config` takes only `K23` (30..28), `KU` (27..25) and `K0`
  -- (2..0); `Status` keeps only `statusWriteMask`
  -- bits (others read as zero); `Cause` changes only `causeWriteMask` bits
  -- (DC, IV, IP1..0), keeping `BD`/`CE`/`ExcCode`/everything else; `EPC`/
  -- `ErrorEPC` are fully writable; `EBase` takes the Exception Base field
  -- (bits 29..12) only.
  | .mtc0 rt rd sel =>
    match rd.toNat, sel.toNat with
    | 8, 0 => mkNext s s
    | 12, 0 => mkNext s { s with cp0Status := readReg s (regIdx rt) &&& statusWriteMask }
    | 13, 0 => mkNext s { s with cp0Cause :=
              (s.cp0Cause &&& ~~~causeWriteMask) ||| (readReg s (regIdx rt) &&& causeWriteMask) }
    | 14, 0 => mkNext s { s with cp0Epc := readReg s (regIdx rt) }
    | 15, 0 => mkNext s s
    | 15, 1 => mkNext s { s with cp0EBase :=
              (readReg s (regIdx rt) &&& ebaseWriteMask) ||| ebaseFixedBits }
    | 16, 0 => mkNext s { s with cp0ConfigK0 := (readReg s (regIdx rt)).setWidth 3,
                                 cp0ConfigK23 := (readReg s (regIdx rt) >>> 28).setWidth 3,
                                 cp0ConfigKU := (readReg s (regIdx rt) >>> 25).setWidth 3 }
    | 16, 1 => mkNext s s
    | 30, 0 => mkNext s { s with cp0ErrorEpc := readReg s (regIdx rt) }
    | _, _ => takeException s excCodeRI
  -- `di`/`ei` (MD00086 Vol II-A Rev 6.06, DI p.164, EI p.176):
  -- `GPR[rt] ← Status; Status.IE ← 0` / `1`. The value written to `$rt` is
  -- the Status value *before* the change.
  | .di rt =>
    mkNext s (writeReg { s with cp0Status := s.cp0Status &&& ~~~statusIeMask } (regIdx rt)
      s.cp0Status)
  | .ei rt =>
    mkNext s (writeReg { s with cp0Status := s.cp0Status ||| statusIeMask } (regIdx rt)
      s.cp0Status)
  -- `eret` (MD00086 "ERET"):
  --   if Status.ERL = 1 then PC ← ErrorEPC; Status.ERL ← 0
  --   else                   PC ← EPC;      Status.EXL ← 0
  --   LLbit ← 0
  -- It has no delay slot: `pc` is set directly. (`eret` *in* a delay slot
  -- never reaches this arm: `execInstr` raises Reserved Instruction for it.)
  | .eret =>
    if s.cp0Status &&& statusErlMask != 0#32 then
      { s with pc := s.cp0ErrorEpc, cp0Status := s.cp0Status &&& ~~~statusErlMask, llBit := false }
    else
      { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask, llBit := false }
  -- `wait` (MD00086 Vol II-A Rev 6.06, WAIT, p.442-443): "The WAIT instruction
  -- performs an implementation-dependent operation, involving a lower power
  -- mode"; "The pipeline is restarted when an external event, such as an
  -- interrupt or external request occurs, and execution continues with the
  -- instruction following the WAIT instruction". The pre-Release-6 Operation
  -- is "I: Enter implementation dependent lower power mode / I+1: Potential
  -- interrupt taken here". The model has no interrupts and no power modes; it
  -- pins the restart event as immediate, so the only architectural effect is
  -- the one the manual states for the restart without an enabled interrupt:
  -- `PC ← PC + 4` (p.443, "continue execution at instruction after wait").
  | .wait _ => mkNext s s

/-- Execute the already-fetched, already-decoded instruction `instr` in
state `s`.

First check: if `s` is in a delay slot (`s.pendingBranch = some _`) and
`instr` is a control-transfer instruction (`isBranchLike`), raise Reserved
Instruction. **Pin.** For a pre-Release-6 processor the manual makes this
UNPREDICTABLE ("Pre-Release 6: Processor operation is UNPREDICTABLE if a
control transfer instruction (CTI) is placed in the delay slot of a branch or
jump", MD00086 Vol II-A Rev 6.06, BEQ, p.72; MD00082 Vol I-A Rev 6.01 §5.3.2.1,
p.62) or UNDEFINED (`eret`: ERET, p.177; `wait`: WAIT, p.442), and
"UNPREDICTABLE operations may cause arbitrary exceptions" while they "must not
halt or hang the processor" (MD00086 §1.2.1, p.3-4; UNDEFINED operations "must
not cause the processor to hang", §1.2.2, p.4). Reserved Instruction is also
exactly what Release 6 requires here ("implementations are required to signal
a Reserved Instruction exception", MD00082 §5.3.2.1, p.62). The exception is
taken in the delay slot: `EPC` = the branch, `Cause.BD = 1` (`exceptionEntry`).
(The test is written `isBranchLike instr && …` in that order so that it reduces
to `false` by computation for any non-branch instruction, whatever `s` is.)

Second check: a coprocessor-1 instruction (`usesCop1`) with `Status.CU1 = 0`
raises Coprocessor Unusable (`Cause.CE = 1`) and does nothing else.

Third check: a coprocessor-0 instruction (`usesCop0`) executed when coprocessor 0 is not usable
(`cp0Usable`: not Kernel Mode and `Status.CU0 = 0`) raises Coprocessor Unusable (`Cause.CE = 0`)
and does nothing else (MD00090 Vol III Rev 6.02 §6.2.22, p.100). The second and third checks
concern disjoint sets of instructions, so their order does not matter. The first check comes
before the third: `eret` or `wait` in a delay slot is UNDEFINED (ERET p.177, WAIT p.442) and the
pin is Reserved Instruction in every mode.

Otherwise the instruction's effect is `execBody s instr`. -/
def execInstr (s : State) (instr : Instruction) : State :=
  if isBranchLike instr && s.pendingBranch.isSome then
    takeException s excCodeRI
  else if usesCop1 instr && !cu1Enabled s then
    takeCoprocessorUnusable s
  else if usesCop0 instr && !cp0Usable s then
    takeCop0Unusable s
  else execBody s instr

/-- One instruction time: fetch the word at `s.pc` from memory, decode, execute.

* Fetch is `readMemWord s s.pc`, a big-endian word read from physical memory through the MMU
  (`translate`); it fails only for a misaligned `pc` or a `pc` outside useg in User Mode, which
  raise Address Error (AdEL) with `BadVAddr = pc` (MD00090 Vol III Rev 6.02 §6.2.9, p.92-93).
* A word that does not decode: Reserved Instruction — except that a COP0 or
  CACHE word (`isCop0Word`) raises Coprocessor Unusable (`CE = 0`) when
  coprocessor 0 is not usable (`cp0Usable`), a word in coprocessor 1's
  encoding space (`isCop1Word`) raises Coprocessor Unusable (`CE = 1`) when
  `Status.CU1 = 0`, and a word in coprocessor 2's (`isCop2Word`) always raises
  Coprocessor Unusable (`CE = 2`): the model has no coprocessor 2 and
  `Status.CU2` reads 0.
* Otherwise `execInstr`.

There is no halting case: the result is always the next architectural state. -/
def step (s : State) : State :=
  match readMemWord s s.pc with
  | none => takeAddressException s excCodeAdEL s.pc
  | some w =>
    match decode w with
    | none =>
      if isCop0Word w && !cp0Usable s then takeCop0Unusable s
      else if isCop1Word w && !cu1Enabled s then takeCoprocessorUnusable s
      else if isCop2Word w then exceptionEntry s excCodeCpU 2#32
      else takeException s excCodeRI
    | some instr => execInstr s instr

/-- The bare machine run: `step` iterated `n` times from `s`. It knows nothing about programs,
services or halting (those are `Semantics/Env.lean`'s `runHosted`). Total by structural
recursion on `n`. -/
def run (s : State) : Nat → State
  | 0 => s
  | n + 1 => run (step s) n

/-! ## Reset -/

/-- **The Reset exception** (cold reset), taken from state `s` (MD00090 Vol III Rev 6.02 §6.2.5
"Reset Exception", p.89-90). "On a Reset Exception, only the following registers have defined
state"; the Operation (p.89-90), restricted to the registers this model has:

```
StatusBEV ← 1;  StatusERL ← 1
StatusRP ← 0;  StatusTS ← 0;  StatusSR ← 0;  StatusNMI ← 0   -- not implemented: read as 0
CauseDC ← 0
EBaseExceptionBase ← 0                                     -- EBase reads 0x8000_0000
Config ← ConfigurationState;  ConfigK0 ← 2                 -- "Suggested"; Config1 fixed
                                     -- K23, KU: reset "Undefined" (p.233), pinned to 2 like K0
if InstructionInBranchDelaySlot then ErrorEPC ← restartPC  # PC of branch/jump
else ErrorEPC ← restartPC                                  # PC of instruction
PC ← 0xBFC0 0000
```

The rest of the Operation names registers the model does not implement (Random, PageMask,
PageGrain, Wired, HWREna, EntryHi, IntCtl, SRSCtl, SRSMap, Config2, Config3, WatchLo,
PerfCnt): nothing to do. Every register the section does not list keeps whatever it held: its
reset state is undefined, and keeping it is one legal value (pin). In particular the other
`Status` bits (`UM`, `EXL`, `IE`, `IM`, `CU0`, `CU1`) are unchanged; with `ERL = 1` the processor
is in Kernel Mode regardless (§3.2, p.21). Two further pins: the pending branch is dropped (the
reset "aborts state machines", p.89; "restart PC" is the branch when the interrupted instruction
was in a delay slot, `s.pc - 4`), and `LLbit` is cleared (its reset state is not given). -/
def resetException (s : State) : State :=
  { s with
      cp0Status := s.cp0Status ||| statusBevMask ||| statusErlMask
      cp0Cause := s.cp0Cause &&& ~~~causeDcMask
      cp0EBase := ebaseFixedBits
      cp0ConfigK0 := 2#3
      cp0ConfigK23 := 2#3
      cp0ConfigKU := 2#3
      cp0ErrorEpc := if s.pendingBranch.isSome then s.pc - 4#32 else s.pc
      pc := resetVector
      pendingBranch := none
      llBit := false }

/-- **The state after a cold reset**: the Reset exception applied to `powerOnState` (whose
values for the registers the reset leaves undefined are all pinned to 0, `State.lean`). So
`pc = 0xBFC0_0000`, `Status = BEV | ERL` (0x0040_0004: Kernel Mode, bootstrap vectors, CU0 = CU1
= 0), `Cause = 0`, `EBase` reads 0x8000_0000, `Config.K0 = K23 = KU = 2`, `ErrorEPC = 0` (the restart PC
of a power-on reset is not meaningful, p.89: "this value may or may not be predictable if the
Reset Exception was taken as the result of power being applied to the processor"), every GPR,
`HI`/`LO`, FPR and `FCSR` 0, memory empty. Properties: `Specs/Reset.lean`. -/
def resetState : State := resetException powerOnState
