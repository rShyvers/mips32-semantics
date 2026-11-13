import Std.Data.HashMap.Basic
import Semantics.Word
import Semantics.Types
import Semantics.State
import Semantics.Instruction
import Semantics.FpOps

/-!
# Step — small-step semantics of the modeled MIPS32 Release 2 instruction set

`step` executes one instruction; `run` is `step` iterated with a fuel bound
and nothing else. Ground truth: MD00086 Rev 2.50 (Vol II, instruction set)
and MD00090 (Vol III, privileged architecture), summarised per instruction in
`docs/spec/INSTRUCTION-REF.md`; pinned conventions and divergences from the
MARS test oracle are in `docs/spec/SPEC-NOTES.md` §9.

## What `step` does

1. **Fetch** the word at `pc` from the immutable `Program` (not from
   `State.mem` — SPEC-NOTES §9: self-modifying code is not modeled).
   A misaligned `pc` raises Address Error (AdEL, `BadVAddr = pc`). An aligned
   `pc` with no instruction halts: `unhandledException` if the machine is
   sitting at the exception vector with `Status.EXL = 1` (an exception was
   taken and no handler is installed), `noInstruction` otherwise.
2. **Decode** it (`Instruction.decode`, strict). A word that does not decode
   raises Reserved Instruction.
3. **Execute** it (`execInstr`).

## Branch delay slots

`State.pendingBranch = some t` means "the instruction at `pc` is in a delay
slot; control goes to `t` after it". Every branch/jump sets it (taken: the
target; not taken: `pc + 8`). Every non-control-flow instruction goes
through `mkNext`/`advance`, which commits a pending target. A branch, jump or
`eret` in a delay slot halts with `branchInDelaySlot` (UNPREDICTABLE in the
architecture). A not-taken branch-likely nullifies its delay slot: its own
step goes straight to `pc + 8`.

## Exceptions

`exceptionEntry` implements the general exception sequence (MD00090,
"General Exception Processing"): `EPC`/`Cause.BD` (only if `EXL` was 0),
`Cause.ExcCode`, `Status.EXL ← 1`, `PC ←` the general vector (`BEV`
selects which; `EBase` supplies the base when `BEV = 0`), and the pending
branch is abandoned. Raised here: Integer Overflow (`add`/`addi`/`sub`),
Address Error (misaligned load/store/fetch; sets `BadVAddr`), Reserved
Instruction, Coprocessor Unusable (`Cause.CE` = the unit), Floating Point,
Syscall (service numbers outside the environment-call convention),
Breakpoint, Trap.

## Floating point

All FP arithmetic is `Semantics/FpOps.lean` (`Mips.Fp`): exact results on bit
patterns, one correctly-rounded pack under FCSR.RM, IEEE flags. No host
`Float` appears anywhere in `step`. Every coprocessor-1 instruction first
checks `Status.CU1` (`usesCop1`); arithmetic instructions finish through
`fpFinishS`/`fpFinishD`/`fpFinishCmp`, which update FCSR with
`Mips.Fp.fpUpdate` and take the Floating Point exception instead of writing
the destination when an enabled exception was raised.

## Environment calls

`syscall` with `$v0 ∈ {1, 4, 10, 11}` is serviced by the model itself, as a
documented environment-call convention borrowed from MARS/SPIM (print int,
print string, exit, print char). `exit` is the one clean `HaltReason`. Any
other `$v0` raises the architectural Syscall exception.

## Not modeled

User/kernel mode (`Status.UM`/`KSU`): everything runs as kernel, so CP0
instructions never raise Coprocessor Unusable. Interrupts, timer, TLB,
caches, shadow register sets (see `docs/spec/SPEC-NOTES.md`).

`step` is total: every `(p, s)` yields a `StepResult`.
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

/-- Package `result` (the ordinary, non-control-flow effect of the current
instruction) as a successful step, resolving any delay-slot transfer
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
def mkNext (orig result : State) : StepResult :=
  StepResult.next (advance orig result)

/-- Whether `instr` is a control-transfer instruction that may not appear in
a branch delay slot: the 12 ordinary branches/jumps (`beq`,`bne`,`blez`,
`bgtz`,`bltz`,`bgez`,`bltzal`,`bgezal`,`j`,`jal`,`jr`,`jalr`), the 8
branch-likely instructions, the FP branches `bc1f`/`bc1t`/`bc1fl`/`bc1tl`,
`eret` and `wait` (26 in all). `execInstr` halts with `HaltReason.branchInDelaySlot` when one
of these is reached with `s.pendingBranch = some _` — i.e. directly after
*any* branch/jump, taken or not. The architecture makes these cases
UNPREDICTABLE (branches/jumps) or UNDEFINED (`eret`, `wait`); the halt is
a model pin. -/
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

/-- Raise a general exception: a real state transition (`StepResult.next`)
to the exception vector, not a halt. -/
def takeException (s : State) (excCode : W32) : StepResult :=
  StepResult.next (exceptionEntry s excCode)

/-- Raise Coprocessor Unusable for coprocessor 1: `Cause.ExcCode = CpU` (11),
`Cause.CE = 1` (MD00090 Vol III Rev 6.02 §6.2.22, p.100). -/
def takeCoprocessorUnusable (s : State) : StepResult :=
  StepResult.next (exceptionEntry s excCodeCpU 1#32)

/-- Raise an Address Error exception (`excCodeAdEL` for a load or fetch,
`excCodeAdES` for a store): as `takeException`, and additionally
`BadVAddr ← addr`, the failing address. -/
def takeAddressException (s : State) (excCode addr : W32) : StepResult :=
  StepResult.next (exceptionEntry { s with cp0BadVAddr := addr } excCode)

/-- "An exception was taken and no handler is installed": `Status.EXL = 1`
and `pc` is the general exception vector. `step` consults this only when the
fetch at `pc` finds no instruction. -/
def atUnhandledVector (s : State) : Bool :=
  s.cp0Status &&& statusExlMask != 0#32 && s.pc == exceptionVector s

/-- The `ExcCode` field (bits 6..2) of `Cause`, as a number. -/
def causeExcCode (s : State) : W32 :=
  (s.cp0Cause &&& causeExcCodeMask) >>> 2

/-- Maximum number of bytes scanned by syscall 4 (`PrintString`) before
giving up. This is a simulator limitation (needed for `step` to remain a
total function without assuming anything about how "long" a null-terminated
string in sparse memory can be): any realistic test-corpus string is many
orders of magnitude shorter than this. Documented for the Wave 3 harness in
case a corpus program relies on a longer unterminated scan. -/
def printStringFuel : Nat := 65536

/-- Scan up to `fuel` bytes starting at `addr`, stopping at the first `0x00`
byte (exclusive) or when fuel runs out, decoding each byte as ASCII. Absent
bytes read as `0` (`State.readMemByte`'s zero-fill convention), so any scan
over memory that is not deliberately padded with a long run of distinct
nonzero bytes terminates well within `printStringFuel`. -/
def readCString (s : State) (addr : W32) : Nat → String
  | 0 => ""
  | fuel + 1 =>
    let b := (s.mem.get? addr).getD 0
    if b == 0 then ""
    else String.singleton (Char.ofNat b.toNat) ++ readCString s (addr + 1#32) fuel

/-- `Status.CU1`: coprocessor 1 is usable. -/
def cu1Enabled (s : State) : Bool := s.cp0Status &&& statusCu1Mask != 0#32

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
def fpFinishS (s : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags) : StepResult :=
  let u := Mips.Fp.fpUpdate s.fcsr r.2
  if u.2 then takeException { s with fcsr := u.1 } excCodeFPE
  else mkNext s (writeFpReg { s with fcsr := u.1 } (regIdx fd) r.1)

/-- As `fpFinishS`, for a 64-bit (double) result written to the pair `fd`. -/
def fpFinishD (s : State) (fd : W32) (r : BitVec 64 × Mips.Fp.Flags) : StepResult :=
  let u := Mips.Fp.fpUpdate s.fcsr r.2
  if u.2 then takeException { s with fcsr := u.1 } excCodeFPE
  else mkNext s (writeFpD { s with fcsr := u.1 } fd r.1)

/-- Complete a `C.cond.fmt`: as `fpFinishS`, the "result" being the Boolean
written to condition code `cc` ("If the Invalid Operation Enable bit is set
in the FCSR, no result is written and an Invalid Operation exception is taken
immediately. Otherwise, the Boolean result is written into condition code
CC" — MD00086 Vol II-A Rev 6.06, C.cond.fmt, p.110). -/
def fpFinishCmp (s : State) (cc : W32) (r : Bool × Mips.Fp.Flags) : StepResult :=
  let u := Mips.Fp.fpUpdate s.fcsr r.2
  if u.2 then takeException { s with fcsr := u.1 } excCodeFPE
  else mkNext s { s with fcsr := Mips.Fp.setCC u.1 (ccIdx cc) r.1 }

/-- `PRId` (CP0 register 15, select 0; MD00090 Vol III Rev 6.02 §9.40,
Table 9.57, p.221): Company ID 1 (nonzero marks a MIPS32 processor),
Company Options, Processor ID and Revision 0 — an environment constant that
names no real product. -/
def prIdValue : W32 := 0x00010000

/-- `Config` (CP0 register 16, select 0; MD00090 Vol III Rev 6.02 §9.45,
Table 9.64, p.233-235): `M` = 1 (Config1 present), `BE` = 1 (big-endian),
`AT` = 0 (MIPS32), `AR` = 1 (Release 2), `MT` = 0 (no MMU), `VI` = 0,
`K0` = 2 (uncached, Table 9.12 p.133), everything else 0. The register is
read-only in this model (the architecture makes `K0` writable; there is no
cache for it to control). -/
def configValue : W32 := 0x80008402

/-- `Config1` (CP0 register 16, select 1; MD00090 Vol III Rev 6.02 §9.46,
Table 9.65): `FP` = 1 (FPU implemented) and nothing else — `M` = 0 (no
Config2), no TLB entries beyond the encoding's minimum, no caches (`IL` =
`DL` = 0), no coprocessor 2, MDMX, performance counters, watch registers,
MIPS16e or EJTAG. -/
def config1Value : W32 := 0x00000001

/-- The effect of the already-fetched, already-decoded instruction `instr`
in state `s`, **after** `execInstr`'s two guards (no control transfer in a
delay slot; coprocessor 1 usable for the instructions that need it). Total:
every case yields a next state (possibly the exception vector) or a defined
`HaltReason`. -/
def execBody (s : State) (instr : Instruction) : StepResult :=
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
  -- holding 1, per the real MIPS32 ISA (docs/spec/MIPS-COVERAGE-GAPS.md \u00a73.4).
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
      -- SPEC-NOTES §9.2: hi/lo unchanged, no halt.
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
  -- `synci`: real MIPS32 instruction-cache-flush hint (REGIMM opcode 0x01,
  -- `rt` field 0x1f; MIPS32r2, `docs/spec/MIPS-COVERAGE-GAPS.md` §3.7),
  -- used by self-modifying code / JIT compilers to flush a stale
  -- instruction-cache line after writing new code bytes. Computes the same
  -- effective address as `lw`/`sw` for architectural fidelity, but this
  -- simulator has no instruction-cache model at all, so the address is
  -- never read from or written to memory -- a documented no-op that falls
  -- through to `pc + 4` via `mkNext`, touching no state at all (not even a
  -- memory read).
  | .synci rs imm =>
    let _addr := readReg s (regIdx rs) + signExt16 imm
    mkNext s s
  -- `lwl`/`lwr`/`swl`/`swr`: real MIPS32 classic (pre-r6) unaligned
  -- load/store pair (MD00086 Rev 2.50 §3.2, Table 3-4; `docs/spec/
  -- MIPS-COVERAGE-GAPS.md` §3.6). Unlike `lw`/`sw`, `addr` has no alignment
  -- requirement -- `readMemByte`/`writeMemByte` are already total, so none
  -- of these four cases can halt. `off = addr.toNat % 4` selects how many
  -- bytes straddle the word boundary; the `.getD` fallback on every
  -- `readMemByte`/`writeMemByte` result is never actually exercised (those
  -- helpers always return `some`), it just discharges the `Option` they
  -- still return. See `docs/spec/INSTRUCTION-REF.md`'s dedicated section
  -- for the worked byte-position example this case-split implements.
  | .lwl rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    let off := addr.toNat % 4
    let old := readReg s (regIdx rt)
    let b0 := (readMemByte s addr).getD 0
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
    let off := addr.toNat % 4
    let old := readReg s (regIdx rt)
    let v :=
      match off with
      | 0 =>
        let b3 := (readMemByte s addr).getD 0
        setByteSlot old 3 b3
      | 1 =>
        let b2 := (readMemByte s (addr - 1#32)).getD 0
        let b3 := (readMemByte s addr).getD 0
        setByteSlot (setByteSlot old 2 b2) 3 b3
      | 2 =>
        let b1 := (readMemByte s (addr - 2#32)).getD 0
        let b2 := (readMemByte s (addr - 1#32)).getD 0
        let b3 := (readMemByte s addr).getD 0
        setByteSlot (setByteSlot (setByteSlot old 1 b1) 2 b2) 3 b3
      | _ =>  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
        let b0 := (readMemByte s (addr - 3#32)).getD 0
        let b1 := (readMemByte s (addr - 2#32)).getD 0
        let b2 := (readMemByte s (addr - 1#32)).getD 0
        let b3 := (readMemByte s addr).getD 0
        setByteSlot (setByteSlot (setByteSlot (setByteSlot old 0 b0) 1 b1) 2 b2) 3 b3
    mkNext s (writeReg s (regIdx rt) v)
  -- `swl`/`swr` are store-class, so (like `sw`/`sh`/`swc1`) they clear
  -- `llBit` -- see the module docstring's `ll`/`sc` paragraph.
  | .swl rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    let off := addr.toNat % 4
    let v := readReg s (regIdx rt)
    let s1 := (writeMemByte s addr (getByteSlot v 0)).getD s
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
    let off := addr.toNat % 4
    let v := readReg s (regIdx rt)
    let s' :=
      match off with
      | 0 => (writeMemByte s addr (getByteSlot v 3)).getD s
      | 1 =>
        let s1 := (writeMemByte s (addr - 1#32) (getByteSlot v 2)).getD s
        (writeMemByte s1 addr (getByteSlot v 3)).getD s1
      | 2 =>
        let s1 := (writeMemByte s (addr - 2#32) (getByteSlot v 1)).getD s
        let s2 := (writeMemByte s1 (addr - 1#32) (getByteSlot v 2)).getD s1
        (writeMemByte s2 addr (getByteSlot v 3)).getD s2
      | _ =>  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
        let s1 := (writeMemByte s (addr - 3#32) (getByteSlot v 0)).getD s
        let s2 := (writeMemByte s1 (addr - 2#32) (getByteSlot v 1)).getD s1
        let s3 := (writeMemByte s2 (addr - 1#32) (getByteSlot v 2)).getD s2
        (writeMemByte s3 addr (getByteSlot v 3)).getD s3
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
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  | .bne rs rt imm =>
    let pcNext := s.pc + 4#32
    if readReg s (regIdx rs) == readReg s (regIdx rt) then
      StepResult.next { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
    else
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
  | .blez rs imm =>
    let pcNext := s.pc + 4#32
    if asSigned (readReg s (regIdx rs)) ≤ 0 then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  | .bgtz rs imm =>
    let pcNext := s.pc + 4#32
    if 0 < asSigned (readReg s (regIdx rs)) then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  -- REGIMM zero-comparison branches (opcode 0x01; MD00086 Rev 2.50 \u00a73.2,
  -- Table 3-2). `bltz`/`bgez` are plain conditional branches, same shape as
  -- `blez`/`bgtz` above. `bltzal`/`bgezal` additionally link `$ra` to
  -- `pcNext + 4` (`pc + 8`, past the delay slot, same convention as `jal`)
  -- -- real MIPS32 performs this link **unconditionally**, on every
  -- execution of the instruction, regardless of whether the branch itself
  -- is taken; only the branch transfer is conditional.
  | .bltz rs imm =>
    let pcNext := s.pc + 4#32
    if asSigned (readReg s (regIdx rs)) < 0 then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  | .bgez rs imm =>
    let pcNext := s.pc + 4#32
    if 0 ≤ asSigned (readReg s (regIdx rs)) then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  | .bltzal rs imm =>
    let pcNext := s.pc + 4#32
    let s' := writeReg s 31 (pcNext + 4#32)
    if asSigned (readReg s (regIdx rs)) < 0 then
      StepResult.next { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s' with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  | .bgezal rs imm =>
    let pcNext := s.pc + 4#32
    let s' := writeReg s 31 (pcNext + 4#32)
    if 0 ≤ asSigned (readReg s (regIdx rs)) then
      StepResult.next { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s' with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
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
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := s.pc + 8#32 }
  | .bnel rs rt imm =>
    let pcNext := s.pc + 4#32
    if readReg s (regIdx rs) == readReg s (regIdx rt) then
      StepResult.next { s with pc := s.pc + 8#32 }
    else
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
  | .blezl rs imm =>
    let pcNext := s.pc + 4#32
    if asSigned (readReg s (regIdx rs)) ≤ 0 then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := s.pc + 8#32 }
  | .bgtzl rs imm =>
    let pcNext := s.pc + 4#32
    if 0 < asSigned (readReg s (regIdx rs)) then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := s.pc + 8#32 }
  | .bltzl rs imm =>
    let pcNext := s.pc + 4#32
    if asSigned (readReg s (regIdx rs)) < 0 then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := s.pc + 8#32 }
  | .bgezl rs imm =>
    let pcNext := s.pc + 4#32
    if 0 ≤ asSigned (readReg s (regIdx rs)) then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := s.pc + 8#32 }
  | .bltzall rs imm =>
    let pcNext := s.pc + 4#32
    let s' := writeReg s 31 (pcNext + 4#32)
    if asSigned (readReg s (regIdx rs)) < 0 then
      StepResult.next { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s' with pc := s.pc + 8#32 }
  | .bgezall rs imm =>
    let pcNext := s.pc + 4#32
    let s' := writeReg s 31 (pcNext + 4#32)
    if 0 ≤ asSigned (readReg s (regIdx rs)) then
      StepResult.next { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s' with pc := s.pc + 8#32 }
  | .j target =>
    let pcNext := s.pc + 4#32
    StepResult.next
      { s with pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) }
  | .jal target =>
    -- `$ra` links to `pc + 8` — past the delay slot — not `pcNext` (`pc + 4`):
    -- real MIPS32's `jal` link value is the address of the instruction
    -- *after* the delay slot, since the delay-slot instruction itself still
    -- executes before control reaches `$ra` on return.
    let pcNext := s.pc + 4#32
    let linkVal := pcNext + 4#32
    let s' := writeReg s 31 linkVal
    StepResult.next
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
    StepResult.next { s with pc := pcNext, pendingBranch := some (readReg s (regIdx rs)) }
  | .jalr rs rd =>
    -- `$rd` links to `pc + 8` — past the delay slot — the same `jal` link-value
    -- convention as above. The link target is read before `$rd` is written,
    -- so `jalr $rs, $rs` (rd = rs) still reads the pre-write `$rs` value.
    let pcNext := s.pc + 4#32
    let linkVal := pcNext + 4#32
    let target := readReg s (regIdx rs)
    let s' := writeReg s (regIdx rd) linkVal
    StepResult.next { s' with pc := pcNext, pendingBranch := some target }
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
      StepResult.next { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
    else
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
  | .bc1t cc imm =>
    let pcNext := s.pc + 4#32
    if readFcc s cc then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  | .bc1fl cc imm =>
    let pcNext := s.pc + 4#32
    if readFcc s cc then
      StepResult.next { s with pc := s.pc + 8#32 }
    else
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
  | .bc1tl cc imm =>
    let pcNext := s.pc + 4#32
    if readFcc s cc then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := s.pc + 8#32 }
  -- `syscall`. Architecturally this always raises the Syscall exception
  -- (ExcCode 8). The model pins an explicit **environment-call convention**
  -- (MARS/SPIM service numbers, SPEC-NOTES §5/§9): when `$v0` is 1 (print
  -- int), 4 (print string), 10 (exit) or 11 (print char) the model performs
  -- the service itself, as if an operating system had handled the exception
  -- and returned; `exit` halts the machine. Any other `$v0` raises the real
  -- Syscall exception.
  | .syscall _ =>
    match (readReg s 2).toNat with
    | 1 =>
      let n := asSigned (readReg s 4)
      mkNext s { s with out := s.out ++ toString n }
    | 4 =>
      let str := readCString s (readReg s 4) printStringFuel
      mkNext s { s with out := s.out ++ str }
    | 10 => StepResult.halt .exit
    | 11 =>
      let c := Char.ofNat ((readReg s 4 &&& 0xff#32).toNat)
      mkNext s { s with out := s.out ++ String.singleton c }
    | _ => takeException s excCodeSys
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
  -- Instruction, matching what the undecodable word would do. User mode is
  -- not modeled, so these never raise Coprocessor Unusable.
  | .mfc0 rt rd sel =>
    match rd.toNat, sel.toNat with
    | 8, 0 => mkNext s (writeReg s (regIdx rt) s.cp0BadVAddr)
    | 12, 0 => mkNext s (writeReg s (regIdx rt) s.cp0Status)
    | 13, 0 => mkNext s (writeReg s (regIdx rt) s.cp0Cause)
    | 14, 0 => mkNext s (writeReg s (regIdx rt) s.cp0Epc)
    | 15, 0 => mkNext s (writeReg s (regIdx rt) prIdValue)
    | 15, 1 => mkNext s (writeReg s (regIdx rt) (ebaseValue s))
    | 16, 0 => mkNext s (writeReg s (regIdx rt) configValue)
    | 16, 1 => mkNext s (writeReg s (regIdx rt) config1Value)
    | 30, 0 => mkNext s (writeReg s (regIdx rt) s.cp0ErrorEpc)
    | _, _ => takeException s excCodeRI
  -- `mtc0` write masks: `BadVAddr`, `PRId`, `Config`, `Config1` are
  -- read-only (the write is ignored); `Status` keeps only `statusWriteMask`
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
    | 16, 0 => mkNext s s
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
  -- never reaches this arm -- `isBranchLike` halts it above.)
  | .eret =>
    if s.cp0Status &&& statusErlMask != 0#32 then
      StepResult.next
        { s with pc := s.cp0ErrorEpc, cp0Status := s.cp0Status &&& ~~~statusErlMask, llBit := false }
    else
      StepResult.next
        { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask, llBit := false }
  -- `wait`: real hardware halts the pipeline until an interrupt arrives;
  -- this simulator has no interrupt/timer model at all, so the only
  -- sensible behavior is a documented no-op that falls through to `pc + 4`
  -- via `mkNext`, the same as any other non-control-flow instruction.
  | .wait _ => mkNext s s

/-- Execute the already-fetched, already-decoded instruction `instr` in
state `s`.

First check: if `s` is in a delay slot (`s.pendingBranch = some _`) and
`instr` is a control-transfer instruction (`isBranchLike`), halt with
`HaltReason.branchInDelaySlot` (UNPREDICTABLE in the architecture). (The
test is written `isBranchLike instr && …` in that order so that it reduces
to `false` by computation for any non-branch instruction, whatever `s` is.)

Second check: a coprocessor-1 instruction (`usesCop1`) with `Status.CU1 = 0`
raises Coprocessor Unusable and does nothing else.

Otherwise the instruction's effect is `execBody s instr`. -/
def execInstr (s : State) (instr : Instruction) : StepResult :=
  if isBranchLike instr && s.pendingBranch.isSome then
    StepResult.halt .branchInDelaySlot
  else if usesCop1 instr && !cu1Enabled s then
    takeCoprocessorUnusable s
  else execBody s instr

/-- Execute a single instruction: fetch at `s.pc`, decode, execute.

* Misaligned `pc`: Address Error (AdEL) with `BadVAddr = pc`.
* Aligned `pc` holding no instruction in `p`: a halt. If the machine is at
  the exception vector with `Status.EXL = 1` (`atUnhandledVector`) the halt
  is `unhandledException ExcCode EPC BadVAddr` -- the model-level convention
  for "an exception was taken and no handler is installed"; otherwise it is
  `noInstruction pc`.
* A word that does not decode: Reserved Instruction — except that a word
  in coprocessor 1's encoding space (`isCop1Word`) raises Coprocessor
  Unusable (`CE = 1`) when `Status.CU1 = 0`, and a word in coprocessor 2's
  (`isCop2Word`) always raises Coprocessor Unusable (`CE = 2`): the model has
  no coprocessor 2 and `Status.CU2` reads 0.
* Otherwise `execInstr`. -/
def step (p : Program) (s : State) : StepResult :=
  match fetchWord p s.pc with
  | none =>
    if s.pc.toNat % 4 ≠ 0 then takeAddressException s excCodeAdEL s.pc
    else if atUnhandledVector s then
      StepResult.halt (.unhandledException (causeExcCode s) s.cp0Epc s.cp0BadVAddr)
    else StepResult.halt (.noInstruction s.pc)
  | some w =>
    match decode w with
    | none =>
      if isCop1Word w && !cu1Enabled s then takeCoprocessorUnusable s
      else if isCop2Word w then StepResult.next (exceptionEntry s excCodeCpU 2#32)
      else takeException s excCodeRI
    | some instr => execInstr s instr

/-- Outcome of running a bounded number of steps: either the program halted
(carrying the reason, the final state, and how many steps were taken
including the halting one), or the step budget was exhausted first. -/
inductive RunResult where
  | halted (r : HaltReason) (s : State) (steps : Nat)
  | limitReached (s : State) (steps : Nat)

/-- `step` iterated: run from `s₀` until `step` halts or `maxSteps` steps have
been taken. Nothing else happens here -- every piece of instruction
semantics, including delay slots, branch-likely nullification and exception
entry, is in `step`. Total by structural recursion on the fuel. -/
def run (p : Program) (s₀ : State) (maxSteps : Nat) : RunResult :=
  let rec go : Nat → State → Nat → RunResult
    | 0, s, steps => .limitReached s steps
    | fuel + 1, s, steps =>
      match step p s with
      | .halt r => .halted r s (steps + 1)
      | .next s' => go fuel s' (steps + 1)
  go maxSteps s₀ 0

-- ## Tests
--
-- Per DESIGN.md §5 / CLAUDE.md §5: pure arithmetic helpers (no `Program` or
-- `State.mem` HashMap access) are checked with `by decide`/`by rfl`. Anything
-- that calls `step`/`run` touches `Program` (`Std.HashMap W32 W32`), which is
-- `cbv_opaque` and not kernel-reducible, so *every* `step`/`run` check below
-- uses `#guard` (compiled evaluation) — this is a strictly larger scope than
-- Wave 1's "memory contents" rule, because `step` always fetches from
-- `Program` first. The one exception is the misaligned-fetch case, which
-- short-circuits before touching the map and so is provable by `decide`.

section TestHelpers

private def regs0 : State := initialState textBase

private def setRegs (s : State) (kvs : List (Fin 32 × W32)) : State :=
  kvs.foldl (fun acc kv => writeReg acc kv.1 kv.2) s

private def setFpRegs (s : State) (kvs : List (Fin 32 × W32)) : State :=
  kvs.foldl (fun acc kv => writeFpReg acc kv.1 kv.2) s

private def prog1 (instr : Instruction) : Program :=
  (∅ : Program).insert textBase (encode instr)

private def progAt (addr : W32) (instr : Instruction) : Program :=
  (∅ : Program).insert addr (encode instr)

private def buildProg (base : W32) (instrs : List Instruction) : Program :=
  instrs.zipIdx.foldl (fun acc (instr, i) => acc.insert (base + BitVec.ofNat 32 (4 * i)) (encode instr))
    (∅ : Program)

private def stepState (p : Program) (s : State) : Option State :=
  match step p s with
  | .next s' => some s'
  | .halt _ => none

private def nextRegEq (r : StepResult) (i : Fin 32) (v : W32) : Bool :=
  match r with
  | .next s => readReg s i == v
  | .halt _ => false

private def nextPcEq (r : StepResult) (pc : W32) : Bool :=
  match r with
  | .next s => s.pc == pc
  | .halt _ => false

private def nextHiLoEq (r : StepResult) (hi lo : W32) : Bool :=
  match r with
  | .next s => s.hi == hi && s.lo == lo
  | .halt _ => false

private def nextFpRegEq (r : StepResult) (i : Fin 32) (v : W32) : Bool :=
  match r with
  | .next s => readFpReg s i == v
  | .halt _ => false

private def isNext (r : StepResult) : Bool :=
  match r with
  | .next _ => true
  | .halt _ => false

/-- `r` is exception entry (from a state with `EXL = 0`, `BEV = 0`) with
`Cause.ExcCode = code`: at the general vector, `EXL` set, no pending branch. -/
private def raises (r : StepResult) (code : W32) : Bool :=
  match r with
  | .next s' => causeExcCode s' == code && s'.pc == exceptionVectorAddr
      && (s'.cp0Status &&& statusExlMask) == statusExlMask && s'.pendingBranch.isNone
  | .halt _ => false

/-- `r` is an Address Error exception entry with the given code (AdEL/AdES)
and `BadVAddr = a`. -/
private def raisesAddr (r : StepResult) (code a : W32) : Bool :=
  raises r code && (match r with | .next s' => s'.cp0BadVAddr == a | .halt _ => false)

/-- `r` is a halt with `unhandledException code epc badVAddr`. -/
private def isHaltUnhandled (r : StepResult) (code epc badVAddr : W32) : Bool :=
  match r with
  | .halt (.unhandledException c e b) => c == code && e == epc && b == badVAddr
  | _ => false

private def isHaltNoInstr (r : StepResult) (pc : W32) : Bool :=
  match r with
  | .halt (.noInstruction pc') => pc' == pc
  | _ => false

private def isHaltExit (r : StepResult) : Bool :=
  match r with
  | .halt .exit => true
  | _ => false

private def isHaltBranchInDelaySlot (r : StepResult) : Bool :=
  match r with
  | .halt .branchInDelaySlot => true
  | _ => false

private def nextPendingEq (r : StepResult) (pb : Option W32) : Bool :=
  match r with
  | .next s => s.pendingBranch == pb
  | .halt _ => false

private def nextLlBitEq (r : StepResult) (b : Bool) : Bool :=
  match r with
  | .next s => s.llBit == b
  | .halt _ => false

/-- Every `State` field except `pc` is unchanged between `s` and `s'`. Used
to confirm a genuinely-no-op instruction (`sync`/`synci`) touches *no*
state at all, not just the few fields any individual existing test happens
to check. -/
private def sameStateExceptPc (s s' : State) : Bool :=
  s'.regs == s.regs && s'.hi == s.hi && s'.lo == s.lo && s'.fpRegs == s.fpRegs &&
    s'.fcsr == s.fcsr && s'.mem == s.mem && s'.out == s.out &&
    s'.pendingBranch == s.pendingBranch && s'.llBit == s.llBit &&
    s'.cp0Status == s.cp0Status && s'.cp0Cause == s.cp0Cause && s'.cp0Epc == s.cp0Epc &&
    s'.cp0EBase == s.cp0EBase && s'.llAddr == s.llAddr && s'.cp0BadVAddr == s.cp0BadVAddr

-- `sll $zero, $zero, 0` — the canonical MIPS encoding of `nop` (word
-- `0x00000000`) — used as an inert delay-slot filler instruction below.
private def nopInstr : Instruction := .sll 0#32 0#32 0#32

/-- Step once through `instr` placed at `base` (with `nopInstr` as its delay
slot at `base + 4`) from `s`, then step once more through the delay slot:
returns the landing `pc` after both steps, or `none` if either step halts.
Used to exercise the full two-step delay-slot behavior of a taken
branch/jump (SPEC-NOTES §9 item 1). -/
private def stepThroughDelaySlot (base : W32) (instr : Instruction) (s : State) : Option W32 :=
  let p := buildProg base [instr, nopInstr]
  match stepState p s with
  | some s1 => match step p s1 with
    | .next s2 => some s2.pc
    | .halt _ => none
  | none => none

end TestHelpers

-- ### Pure-arithmetic helper sanity (`by decide`/`by rfl`, no `Program`/`mem`)

example : regIdx (5#32) = (5 : Fin 32) := by decide
example : regIdx (31#32) = (31 : Fin 32) := by decide
example : (advance (initialState textBase) (initialState textBase)).pc = textBase + 4#32 := by decide
example : addOverflows 0x7fffffff (1 : Int) (-0x80000000 : Int) = true := by decide
example : addOverflows 5 7 12 = false := by decide
example : subOverflows (-0x80000000 : Int) 1 0x7fffffff = true := by decide
example : subOverflows 10 3 7 = false := by decide
example : signExtByte 0x80 = 0xffffff80#32 := by decide
example : zeroExtByte 0x80 = 0x00000080#32 := by decide
example : signExtLowByte 0x00000080#32 = 0xffffff80#32 := by decide
example : signExtLowByte 0x0000007f#32 = 0x0000007f#32 := by decide
example : countLeadingZeros 0#32 = 32 := by decide
example : countLeadingZeros 0xffffffff#32 = 0 := by decide
example : countLeadingZeros 0x80000000#32 = 0 := by decide
example : countLeadingZeros 1#32 = 31 := by decide
example : countLeadingZeros 0x0000ffff#32 = 16 := by decide
example : countLeadingOnes 0xffffffff#32 = 32 := by decide
example : countLeadingOnes 0#32 = 0 := by decide
example : countLeadingOnes 0xffff0000#32 = 16 := by decide
example : countLeadingOnes 0x7fffffff#32 = 0 := by decide  -- MSB clear -> zero leading ones
-- PC wraparound (W32 arithmetic): pc+4 wraps past 0xffffffff.
example : (0xfffffffc#32 : W32) + 4#32 = 0#32 := by decide

-- Misaligned instruction fetch short-circuits before touching `Program`
-- (same reasoning as `fetchWord`'s own tests in State.lean), so this is
-- provable by `decide` even though `step`'s signature takes a `Program`.
private def misalignedState : State := { (initialState textBase) with pc := textBase + 1#32 }
example : raisesAddr (step (∅ : Program) misalignedState) excCodeAdEL (textBase + 1#32) = true := by decide

-- ### R-type reg/reg/reg: one basic case each, plus `$zero` write-ignore

#guard nextRegEq (step (prog1 (.add 8#32 9#32 10#32)) (setRegs regs0 [(8, 5#32), (9, 7#32)]))
  10 12#32
#guard nextRegEq (step (prog1 (.addu 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 2#32)]))
  10 1#32
#guard nextRegEq (step (prog1 (.sub 8#32 9#32 10#32)) (setRegs regs0 [(8, 10#32), (9, 3#32)]))
  10 7#32
#guard nextRegEq (step (prog1 (.subu 8#32 9#32 10#32)) (setRegs regs0 [(8, 0#32), (9, 1#32)]))
  10 0xffffffff#32
#guard nextRegEq (step (prog1 (.and 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)]))
  10 0x0f000f00#32
#guard nextRegEq (step (prog1 (.or 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)]))
  10 0xff0fff0f#32
#guard nextRegEq (step (prog1 (.xor 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)]))
  10 0xf00ff00f#32
#guard nextRegEq (step (prog1 (.nor 8#32 9#32 10#32)) (setRegs regs0 [(8, 0#32), (9, 0#32)]))
  10 0xffffffff#32
#guard nextRegEq (step (prog1 (.slt 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))
  10 1#32  -- signed: -1 < 1
#guard nextRegEq (step (prog1 (.sltu 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))
  10 0#32  -- unsigned: 0xffffffff is not < 1
-- `$rd = $zero` write-ignore, observed through `step` (and pc still advances)
#guard (match step (prog1 (.add 8#32 9#32 0#32)) (setRegs regs0 [(8, 5#32), (9, 7#32)]) with
        | .next s' => readReg s' 0 == 0#32 && s'.pc == textBase + 4#32
        | .halt _ => false)

-- ### movn/movz: conditional move -- the "condition fails" case must leave
-- `$rd` at its *preset* value (99 below), not zero it (a real no-op, per
-- docs/spec/INSTRUCTION-REF.md's movn/movz entries).
#guard nextRegEq (step (prog1 (.movn 8#32 9#32 10#32)) (setRegs regs0 [(8, 5#32), (9, 1#32), (10, 99#32)]))
  10 5#32   -- movn, $rt != 0: moves
#guard nextRegEq (step (prog1 (.movn 8#32 9#32 10#32)) (setRegs regs0 [(8, 5#32), (9, 0#32), (10, 99#32)]))
  10 99#32  -- movn, $rt == 0: $rd unchanged
#guard nextRegEq (step (prog1 (.movz 8#32 9#32 10#32)) (setRegs regs0 [(8, 5#32), (9, 0#32), (10, 99#32)]))
  10 5#32   -- movz, $rt == 0: moves
#guard nextRegEq (step (prog1 (.movz 8#32 9#32 10#32)) (setRegs regs0 [(8, 5#32), (9, 1#32), (10, 99#32)]))
  10 99#32  -- movz, $rt != 0: $rd unchanged

-- ### add/sub overflow traps

#guard raises (step (prog1 (.add 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x7fffffff#32), (9, 1#32)])) excCodeOv
#guard raises (step (prog1 (.sub 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 1#32)])) excCodeOv
-- addu/subu never trap on the same operands
#guard isNext (step (prog1 (.addu 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x7fffffff#32), (9, 1#32)]))
#guard isNext (step (prog1 (.subu 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 1#32)]))

-- ### Shifts: shamt 0 and 31; sra sign-fill

#guard nextRegEq (step (prog1 (.sll 10#32 8#32 0#32)) (setRegs regs0 [(8, 0x12345678#32)])) 10 0x12345678#32
#guard nextRegEq (step (prog1 (.sll 10#32 8#32 31#32)) (setRegs regs0 [(8, 1#32)])) 10 0x80000000#32
#guard nextRegEq (step (prog1 (.srl 10#32 8#32 0#32)) (setRegs regs0 [(8, 0x12345678#32)])) 10 0x12345678#32
#guard nextRegEq (step (prog1 (.srl 10#32 8#32 31#32)) (setRegs regs0 [(8, 0x80000000#32)])) 10 1#32
#guard nextRegEq (step (prog1 (.sra 10#32 8#32 0#32)) (setRegs regs0 [(8, 0x80000000#32)])) 10 0x80000000#32
#guard nextRegEq (step (prog1 (.sra 10#32 8#32 31#32)) (setRegs regs0 [(8, 0x80000000#32)])) 10 0xffffffff#32

-- ### slt vs sltu with a negative operand; slti/sltiu

#guard nextRegEq (step (prog1 (.slti 8#32 9#32 0x0000#32)) (setRegs regs0 [(8, 0xffffffff#32)])) 9 1#32  -- -1 < 0
#guard nextRegEq (step (prog1 (.sltiu 8#32 9#32 0x0000#32)) (setRegs regs0 [(8, 0xffffffff#32)])) 9 0#32 -- 0xffffffff </u 0 is false

-- ### mult / multu / div / divu / mflo / mfhi

-- mult: positive × positive
#guard nextHiLoEq (step (prog1 (.mult 8#32 9#32)) (setRegs regs0 [(8, 6#32), (9, 7#32)])) 0#32 42#32
-- mult: negative × negative, hi ≠ 0
#guard nextHiLoEq (step (prog1 (.mult 8#32 9#32)) (setRegs regs0 [(8, 0x88ca6c00#32), (9, 0x88ca6c00#32)]))
  0x3782dace#32 0x9d900000#32
-- mflo/mfhi read both halves back out
#guard (match stepState (prog1 (.mult 8#32 9#32)) (setRegs regs0 [(8, 0x88ca6c00#32), (9, 0x88ca6c00#32)]) with
        | some s' =>
          let s'' := { s' with pc := textBase }
          nextRegEq (step (prog1 (.mflo 10#32)) s'') 10 0x9d900000#32 &&
          nextRegEq (step (prog1 (.mfhi 11#32)) s'') 11 0x3782dace#32
        | none => false)
-- multu: both operands > 2^31
#guard nextHiLoEq (step (prog1 (.multu 8#32 9#32)) (setRegs regs0 [(8, 0xb2d05e00#32), (9, 0xb2d05e00#32)]))
  0x7ce66c50#32 0xe2840000#32

-- div: positive dividend
#guard nextHiLoEq (step (prog1 (.div 8#32 9#32)) (setRegs regs0 [(8, 17#32), (9, 5#32)])) 2#32 3#32
-- div: negative dividend — remainder takes the dividend's sign
#guard nextHiLoEq (step (prog1 (.div 8#32 9#32)) (setRegs regs0 [(8, 0xffffffef#32), (9, 5#32)]))
  0xfffffffe#32 0xfffffffd#32  -- hi = -2, lo = -3  (tdiv(-17,5)=-3, tmod(-17,5)=-2)
-- div: zero divisor with pre-seeded hi/lo — unchanged, no halt
private def seededHiLo : State := { regs0 with hi := 0xdeadbeef#32, lo := 0xcafef00d#32 }
#guard isNext (step (prog1 (.div 8#32 9#32)) (setRegs seededHiLo [(8, 10#32), (9, 0#32)]))
#guard nextHiLoEq (step (prog1 (.div 8#32 9#32)) (setRegs seededHiLo [(8, 10#32), (9, 0#32)]))
  0xdeadbeef#32 0xcafef00d#32
-- div: INT_MIN / -1 wraps silently (no halt, no overflow concept for div)
#guard nextHiLoEq (step (prog1 (.div 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 0xffffffff#32)]))
  0#32 0x80000000#32
-- divu: basic
#guard nextHiLoEq (step (prog1 (.divu 8#32 9#32)) (setRegs regs0 [(8, 17#32), (9, 5#32)])) 2#32 3#32
-- divu: zero divisor unchanged, no halt
#guard isNext (step (prog1 (.divu 8#32 9#32)) (setRegs seededHiLo [(8, 10#32), (9, 0#32)]))

-- ### mul (MIPS32 SPECIAL2 GPR multiply; docs/spec/MIPS-COVERAGE-GAPS.md §3.5)
-- `mul`'s result must match the low 32 bits `mult`+`mflo` would produce, for
-- the same operand pairs already exercised above -- including one whose
-- 64-bit product overflows 32 bits signed, confirming the wraparound -- and
-- `mul` must leave `hi`/`lo` unchanged (the pinned dialect choice).
#guard nextRegEq (step (prog1 (.mul 8#32 9#32 10#32)) (setRegs regs0 [(8, 6#32), (9, 7#32)])) 10 42#32  -- matches mult/mflo's lo above (0#32 42#32)
#guard nextRegEq (step (prog1 (.mul 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x88ca6c00#32), (9, 0x88ca6c00#32)]))
  10 0x9d900000#32  -- matches mult/mflo's lo above (overflows 32-bit signed: hi was nonzero, 0x3782dace)
#guard nextHiLoEq (step (prog1 (.mul 8#32 9#32 10#32)) (setRegs seededHiLo [(8, 6#32), (9, 7#32)]))
  0xdeadbeef#32 0xcafef00d#32  -- hi/lo unchanged by mul
#guard nextRegEq (step (prog1 (.mul 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 2#32)])) 10 0xfffffffe#32  -- (-1) * 2 = -2, wraps

-- ### madd/maddu/msub/msubu/mthi/mtlo (MIPS32 multiply-accumulate and HI/LO
-- register moves; docs/spec/MIPS-COVERAGE-GAPS.md §3.5). The key property
-- that distinguishes these from mult/multu/mul: starting from a nonzero
-- `seededHiLo` accumulator, the result must be the *sum* (or difference) of
-- the prior accumulator and the product, never just the product alone.

-- madd: positive × positive (product 42, same pair as the plain mult test
-- above) accumulated on top of seededHiLo instead of overwriting it
#guard nextHiLoEq (step (prog1 (.madd 8#32 9#32)) (setRegs seededHiLo [(8, 6#32), (9, 7#32)]))
  0xdeadbeef#32 0xcafef037#32
-- madd: negative × negative (same pair as the mult test whose product is
-- 0x3782dace_9d900000), accumulated onto seededHiLo with a 64-bit carry
-- into the hi word
#guard nextHiLoEq (step (prog1 (.madd 8#32 9#32)) (setRegs seededHiLo [(8, 0x88ca6c00#32), (9, 0x88ca6c00#32)]))
  0x163099be#32 0x688ef00d#32
-- maddu: unsigned operands > 2^31 (same pair as the multu test above)
#guard nextHiLoEq (step (prog1 (.maddu 8#32 9#32)) (setRegs seededHiLo [(8, 0xb2d05e00#32), (9, 0xb2d05e00#32)]))
  0x5b942b40#32 0xad82f00d#32
-- msub: subtracts the product from the prior accumulator (inverse of the
-- positive madd case above)
#guard nextHiLoEq (step (prog1 (.msub 8#32 9#32)) (setRegs seededHiLo [(8, 6#32), (9, 7#32)]))
  0xdeadbeef#32 0xcafeefe3#32
-- msubu: unsigned subtract
#guard nextHiLoEq (step (prog1 (.msubu 8#32 9#32)) (setRegs seededHiLo [(8, 0xb2d05e00#32), (9, 0xb2d05e00#32)]))
  0x61c7529e#32 0xe87af00d#32

-- mthi/mtlo: write-direction counterparts to mfhi/mflo. Each sets only its
-- own half, leaving the other half (0 on regs0) untouched
#guard nextHiLoEq (step (prog1 (.mthi 8#32)) (setRegs regs0 [(8, 0x12345678#32)])) 0x12345678#32 0#32
#guard nextHiLoEq (step (prog1 (.mtlo 8#32)) (setRegs regs0 [(8, 0x87654321#32)])) 0#32 0x87654321#32
-- round trip through the register file: mthi $8 then mfhi $9 reads back
-- $8's original value (symmetric for mtlo/mflo)
#guard (match stepState (prog1 (.mthi 8#32)) (setRegs regs0 [(8, 0x12345678#32)]) with
        | some s' =>
          let s'' := { s' with pc := textBase }
          nextRegEq (step (prog1 (.mfhi 9#32)) s'') 9 0x12345678#32
        | none => false)
#guard (match stepState (prog1 (.mtlo 8#32)) (setRegs regs0 [(8, 0x87654321#32)]) with
        | some s' =>
          let s'' := { s' with pc := textBase }
          nextRegEq (step (prog1 (.mflo 9#32)) s'') 9 0x87654321#32
        | none => false)

-- ### clo/clz/movn/movz/seb/seh (MIPS32/MIPS32r2 additions; see
-- docs/spec/INSTRUCTION-REF.md)

-- clo: all-ones -> 32; a mixed pattern; all-zero -> 0 leading ones
#guard nextRegEq (step (prog1 (.clo 8#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32)])) 10 32#32
#guard nextRegEq (step (prog1 (.clo 8#32 10#32)) (setRegs regs0 [(8, 0xfff0ffff#32)])) 10 12#32
#guard nextRegEq (step (prog1 (.clo 8#32 10#32)) (setRegs regs0 [(8, 0x00000000#32)])) 10 0#32
-- clz: all-zero -> 32; a mixed pattern; all-ones -> 0 leading zeros
#guard nextRegEq (step (prog1 (.clz 8#32 10#32)) (setRegs regs0 [(8, 0x00000000#32)])) 10 32#32
#guard nextRegEq (step (prog1 (.clz 8#32 10#32)) (setRegs regs0 [(8, 0x0000ffff#32)])) 10 16#32
#guard nextRegEq (step (prog1 (.clz 8#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32)])) 10 0#32

-- seb: sign-extends only the low byte of $rt, ignoring higher bits
#guard nextRegEq (step (prog1 (.seb 10#32 8#32)) (setRegs regs0 [(8, 0x12345680#32)])) 10 0xffffff80#32
#guard nextRegEq (step (prog1 (.seb 10#32 8#32)) (setRegs regs0 [(8, 0x1234567f#32)])) 10 0x0000007f#32
-- seh: sign-extends only the low halfword of $rt
#guard nextRegEq (step (prog1 (.seh 10#32 8#32)) (setRegs regs0 [(8, 0x1234ffff#32)])) 10 0xffffffff#32
#guard nextRegEq (step (prog1 (.seh 10#32 8#32)) (setRegs regs0 [(8, 0x12347fff#32)])) 10 0x00007fff#32

-- ### sllv/srlv/srav (MIPS32 variable shifts; docs/spec/MIPS-COVERAGE-GAPS.md
-- §3.4): the shift amount is `$rs`'s low 5 bits, not a `shamt` field --
-- these mirror the sll/srl/sra shamt-0/31 cases above but via a register,
-- and a shift-amount register holding 33 (0x21, i.e. 32 + 1) must behave
-- identically to one holding 1 (the masking test).
#guard nextRegEq (step (prog1 (.sllv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x12345678#32), (9, 0#32)]))
  10 0x12345678#32
#guard nextRegEq (step (prog1 (.sllv 10#32 8#32 9#32)) (setRegs regs0 [(8, 1#32), (9, 31#32)]))
  10 0x80000000#32
#guard nextRegEq (step (prog1 (.srlv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 31#32)]))
  10 1#32
#guard nextRegEq (step (prog1 (.srav 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 31#32)]))
  10 0xffffffff#32
-- masking: shift-amount register holding 33 behaves identically to holding 1
#guard nextRegEq (step (prog1 (.sllv 10#32 8#32 9#32)) (setRegs regs0 [(8, 1#32), (9, 33#32)]))
  10 2#32
#guard nextRegEq (step (prog1 (.sllv 10#32 8#32 9#32)) (setRegs regs0 [(8, 1#32), (9, 1#32)]))
  10 2#32
#guard nextRegEq (step (prog1 (.srlv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 33#32)]))
  10 0x40000000#32
#guard nextRegEq (step (prog1 (.srlv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 1#32)]))
  10 0x40000000#32
#guard nextRegEq (step (prog1 (.srav 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 33#32)]))
  10 0xc0000000#32
#guard nextRegEq (step (prog1 (.srav 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 1#32)]))
  10 0xc0000000#32

-- ### rotr/rotrv/ext/ins/wsbh (MIPS32r2 additions; docs/spec/MIPS-COVERAGE-GAPS.md
-- §3.4)

-- rotr: wrap-around is the whole point -- contrast directly with `srl` on
-- the exact same input (0x80000000 >> 31 would be 1 either way, so use a
-- shamt where zero-fill and wrap-around visibly differ).
#guard nextRegEq (step (prog1 (.rotr 10#32 8#32 4#32)) (setRegs regs0 [(8, 0x12345678#32)]))
  10 0x81234567#32  -- rotate right 4: low nibble (0x8) wraps to the top
#guard nextRegEq (step (prog1 (.srl 10#32 8#32 4#32)) (setRegs regs0 [(8, 0x12345678#32)]))
  10 0x01234567#32  -- srl on the same input: zero-fills instead of wrapping
#guard nextRegEq (step (prog1 (.rotr 10#32 8#32 0#32)) (setRegs regs0 [(8, 0x12345678#32)]))
  10 0x12345678#32  -- rotate by 0 is a no-op
#guard nextRegEq (step (prog1 (.rotr 10#32 8#32 31#32)) (setRegs regs0 [(8, 0x80000000#32)]))
  10 1#32  -- rotate right 31 == rotate left 1

-- rotrv: same wrap-around behavior, but the amount comes from a register's
-- low 5 bits (masking case included, mirroring sllv/srlv/srav above).
#guard nextRegEq (step (prog1 (.rotrv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x12345678#32), (9, 4#32)]))
  10 0x81234567#32
#guard nextRegEq (step (prog1 (.rotrv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x12345678#32), (9, 36#32)]))
  10 0x81234567#32  -- 36 & 0x1f = 4, masks identically to rotrv by 4

-- ext: extract a 10-bit field starting at bit 6 out of a known pattern.
-- 0x12345678 = 0001 0010 0011 0100 0101 0110 0111 1000; bits [15:6]
-- (10 bits starting at pos 6, i.e. (0x12345678 >> 6) & 0x3ff) = 0x159.
#guard nextRegEq (step (prog1 (.ext 10#32 8#32 6#32 10#32)) (setRegs regs0 [(8, 0x12345678#32)]))
  10 0x159#32
-- ext: pos=0, size=32 extracts the whole register unchanged
#guard nextRegEq (step (prog1 (.ext 10#32 8#32 0#32 32#32)) (setRegs regs0 [(8, 0x89abcdef#32)]))
  10 0x89abcdef#32
-- ext: a single bit
#guard nextRegEq (step (prog1 (.ext 10#32 8#32 31#32 1#32)) (setRegs regs0 [(8, 0x80000000#32)]))
  10 1#32

-- ins: insert the low 10 bits of $rs (0x159) at pos 6 into $rt, leaving the
-- bits outside [15:6] unchanged -- round-trips with the `ext` example above.
#guard nextRegEq (step (prog1 (.ins 10#32 8#32 6#32 10#32)) (setRegs regs0 [(8, 0x159#32), (10, 0x12345678#32)]))
  10 0x12345678#32  -- re-inserting the field ext'd out above reproduces the original word
-- ins leaves bits outside the target field unchanged, even when the source
-- register has garbage in its higher bits (only the low `size` bits of $rs
-- are used) and $rt's target field previously held something different.
-- low 10 bits of $rs = 0xfffffc01 & 0x3ff = 0x001, shifted to pos 6 = 0x40;
-- $rt starts at 0, so only that one bit (bit 6) ends up set.
#guard nextRegEq (step (prog1 (.ins 10#32 8#32 6#32 10#32)) (setRegs regs0 [(8, 0xfffffc01#32), (10, 0x00000000#32)]))
  10 0x40#32
-- ext/ins round-trip: ins-ing a field then ext-racting it back gives the
-- original (masked-to-size) value, for an arbitrary field/position.
-- (`prog1` always places its single instruction at `textBase`, so a true
-- two-instruction sequence needs `buildProg`, threading the same program
-- across two `stepState` calls -- the first executes `ins` at `textBase`
-- and advances `pc` to `textBase+4`, where the second call then finds
-- `ext`.)
private def extInsRoundTripProg : Program :=
  buildProg textBase [.ins 10#32 8#32 3#32 7#32, .ext 11#32 10#32 3#32 7#32]
#guard (stepState extInsRoundTripProg (setRegs regs0 [(8, 0x7f#32), (10, 0#32)])).bind
        (fun s' => (stepState extInsRoundTripProg s').map (fun s'' => readReg s'' 11))
  = some 0x7f#32

-- wsbh: swap bytes within each halfword independently, halfwords stay put.
-- 0x12345678 -> halfword0 (0x5678) swaps to 0x7856, halfword1 (0x1234)
-- swaps to 0x3412 -> result 0x34127856.
#guard nextRegEq (step (prog1 (.wsbh 10#32 8#32)) (setRegs regs0 [(8, 0x12345678#32)]))
  10 0x34127856#32

-- ### addi overflow trap vs addiu wrap; andi/ori/xori high-imm-bits; lui

#guard raises (step (prog1 (.addi 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x7fffffff#32)])) excCodeOv
#guard nextRegEq (step (prog1 (.addiu 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x7fffffff#32)])) 9 0x80000000#32
-- `andi`/`ori`/`xori` zero-extend the immediate (imm bit 15 set must NOT sign-extend)
#guard nextRegEq (step (prog1 (.andi 8#32 9#32 0x8001#32)) (setRegs regs0 [(8, 0xffffffff#32)])) 9 0x00008001#32
#guard nextRegEq (step (prog1 (.ori 8#32 9#32 0x8001#32)) (setRegs regs0 [(8, 0#32)])) 9 0x00008001#32
#guard nextRegEq (step (prog1 (.xori 8#32 9#32 0x8001#32)) (setRegs regs0 [(8, 0#32)])) 9 0x00008001#32
#guard nextRegEq (step (prog1 (.lui 9#32 0x8001#32)) regs0) 9 0x80010000#32

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

/-- Step through `p` from `s` exactly `n` times, threading the state;
`none` if any intermediate step halts. Used below to exercise `ll`/`sc`
multi-instruction sequences (ordinary fallthrough, no delay slot involved). -/
private def stepN (p : Program) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => (stepState p s).bind (stepN p n)

-- `ll`: loads like `lw` and sets `llBit`.
#guard nextRegEq (step (prog1 (.ll 8#32 9#32 4#32)) memTestState) 9 0x8001ff00#32
#guard nextLlBitEq (step (prog1 (.ll 8#32 9#32 4#32)) memTestState) true
-- misaligned ll → AdEL, sc → AdES, same as lw/sw
#guard raisesAddr (step (prog1 (.ll 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)])) excCodeAdEL 0x10010001#32
#guard raisesAddr (step (prog1 (.sc 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)])) excCodeAdES 0x10010001#32

-- `sc` right after a matching `ll` succeeds: writes 1 to `$rt` and the store
-- commits.
private def llscAddr : W32 := 0x10010000#32
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

-- ### beq/bne/blez/bgtz: taken schedules a `pendingBranch` and falls
-- through to the delay slot; not-taken behaves exactly as before (SPEC-NOTES
-- §9 item 1). `stepThroughDelaySlot` executes the branch *and* an inert
-- delay-slot instruction, landing on the real target.

-- `beq` taken: the branch's own step falls through to `pcNext` with the
-- real target recorded in `pendingBranch`, not yet applied to `pc`.
#guard (match step (prog1 (.beq 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false)
-- ... and the delay-slot instruction's own step is what actually lands on
-- the target.
#guard stepThroughDelaySlot textBase (.beq 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 5#32)])
  = some (textBase + 4#32 + 12#32)
#guard nextPcEq (step (prog1 (.beq 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]))
  (textBase + 4#32)
-- not taken: still in a delay slot -- the pending target is the fall-through `pc + 8`
#guard nextPendingEq (step (prog1 (.beq 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]))
  (some (textBase + 8#32))
#guard stepThroughDelaySlot textBase (.beq 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 6#32)])
  = some (textBase + 8#32)

#guard stepThroughDelaySlot textBase (.bne 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 6#32)])
  = some (textBase + 4#32 + 12#32)
#guard nextPcEq (step (prog1 (.bne 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]))
  (textBase + 4#32)

#guard stepThroughDelaySlot textBase (.blez 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])  -- -5 ≤ 0
  = some (textBase + 4#32 + 8#32)
#guard stepThroughDelaySlot textBase (.blez 8#32 2#32) (setRegs regs0 [(8, 0#32)])  -- 0 ≤ 0
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.blez 8#32 2#32)) (setRegs regs0 [(8, 5#32)]))  -- 5 ≤ 0 is false
  (textBase + 4#32)
#guard stepThroughDelaySlot textBase (.bgtz 8#32 2#32) (setRegs regs0 [(8, 5#32)])  -- 5 > 0
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.bgtz 8#32 2#32)) (setRegs regs0 [(8, 0#32)]))  -- 0 > 0 is false
  (textBase + 4#32)

-- ### bltz/bgez/bltzal/bgezal (REGIMM, opcode 0x01): same `pendingBranch`
-- delay-slot scheduling as blez/bgtz, taken/not-taken for each; the `al`
-- variants additionally link `$ra` unconditionally.

-- bltz: taken on a negative $rs, not taken on zero/positive
#guard stepThroughDelaySlot textBase (.bltz 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])  -- -5 < 0
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.bltz 8#32 2#32)) (setRegs regs0 [(8, 0#32)]))  -- 0 < 0 is false
  (textBase + 4#32)
#guard nextPcEq (step (prog1 (.bltz 8#32 2#32)) (setRegs regs0 [(8, 5#32)]))  -- 5 < 0 is false
  (textBase + 4#32)

-- bgez: taken on zero/positive $rs, not taken on negative
#guard stepThroughDelaySlot textBase (.bgez 8#32 2#32) (setRegs regs0 [(8, 0#32)])  -- 0 >= 0
  = some (textBase + 4#32 + 8#32)
#guard stepThroughDelaySlot textBase (.bgez 8#32 2#32) (setRegs regs0 [(8, 5#32)])  -- 5 >= 0
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.bgez 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)]))  -- -5 >= 0 is false
  (textBase + 4#32)

-- bltzal: link into $ra is unconditional (pc + 8, past the delay slot),
-- whether or not the branch itself is taken.
#guard nextRegEq (step (prog1 (.bltzal 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)])) 31
  (textBase + 8#32)  -- taken: -5 < 0
#guard nextRegEq (step (prog1 (.bltzal 8#32 2#32)) (setRegs regs0 [(8, 5#32)])) 31
  (textBase + 8#32)  -- not taken: 5 < 0 is false, $ra still linked
#guard stepThroughDelaySlot textBase (.bltzal 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.bltzal 8#32 2#32)) (setRegs regs0 [(8, 5#32)]))
  (textBase + 4#32)

-- bgezal: same unconditional-link convention as bltzal, >= 0 condition.
#guard nextRegEq (step (prog1 (.bgezal 8#32 2#32)) (setRegs regs0 [(8, 5#32)])) 31
  (textBase + 8#32)  -- taken: 5 >= 0
#guard nextRegEq (step (prog1 (.bgezal 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)])) 31
  (textBase + 8#32)  -- not taken: -5 >= 0 is false, $ra still linked
#guard stepThroughDelaySlot textBase (.bgezal 8#32 2#32) (setRegs regs0 [(8, 5#32)])
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.bgezal 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)]))
  (textBase + 4#32)

-- ### Branch-likely family (deprecated in MIPS32, removed in Release 6).
-- A **taken** instance behaves exactly like its non-likely counterpart
-- (`stepThroughDelaySlot`); a **not-taken** instance nullifies its own
-- delay-slot instruction: its single `step` moves `pc` straight to `pc + 8`
-- with no pending branch, so the delay-slot word is never fetched, decoded
-- or executed -- even if it is undecodable garbage.

-- `beql` taken: identical two-step shape to `beq` taken.
#guard stepThroughDelaySlot textBase (.beql 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 5#32)])
  = some (textBase + 4#32 + 12#32)
-- `beql` not taken: one bare `step` skips the delay slot.
#guard (match step (prog1 (.beql 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]) with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false)

-- The nullified delay-slot word is never looked at: here it is undecodable
-- garbage (it would raise Reserved Instruction if executed) followed by an
-- `addiu`. Two bare `step`s execute the `beql` and then the `addiu` at
-- `pc + 8`; no exception is raised (`EXL` stays 0). `run` (which is just
-- `step` iterated) agrees.
private def squashGarbageWord : W32 := (0x11#32 <<< 26) ||| (0x1f#32 <<< 21)  -- undecodable: COP1 fmt 0x1f
private def beqlNotTakenGarbageProg : Program :=
  (((∅ : Program).insert textBase (encode (.beql 8#32 9#32 3#32))).insert (textBase + 4#32) squashGarbageWord).insert
    (textBase + 8#32) (encode (.addiu 0#32 10#32 7#32))
#guard decode squashGarbageWord = none
#guard (match stepState beqlNotTakenGarbageProg (setRegs regs0 [(8, 5#32), (9, 6#32)]) with
        | some s1 =>
          (match step beqlNotTakenGarbageProg s1 with
           | .next s2 => s2.pc == textBase + 12#32 && readReg s2 10 == 7#32 && s2.cp0Status == statusCu1Mask
           | .halt _ => false)
        | none => false)
#guard (match run beqlNotTakenGarbageProg (setRegs regs0 [(8, 5#32), (9, 6#32)]) 2 with
        | .limitReached s2 steps => steps == 2 && s2.pc == textBase + 12#32 && readReg s2 10 == 7#32
        | .halted _ _ _ => false)

-- `bnel`: opposite polarity to `beql`, same mechanism.
#guard stepThroughDelaySlot textBase (.bnel 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 6#32)])
  = some (textBase + 4#32 + 12#32)
#guard (match step (prog1 (.bnel 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false)

-- `blezl`/`bgtzl`: same conditions as `blez`/`bgtz`, squash instead of
-- ordinary fallthrough when not taken.
#guard stepThroughDelaySlot textBase (.blezl 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])  -- -5 \u2264 0
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.blezl 8#32 2#32)) (setRegs regs0 [(8, 5#32)]) with  -- 5 \u2264 0 is false
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false)
#guard stepThroughDelaySlot textBase (.bgtzl 8#32 2#32) (setRegs regs0 [(8, 5#32)])  -- 5 > 0
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.bgtzl 8#32 2#32)) (setRegs regs0 [(8, 0#32)]) with  -- 0 > 0 is false
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false)

-- `bltzl`/`bgezl` (REGIMM): same conditions as `bltz`/`bgez`.
#guard stepThroughDelaySlot textBase (.bltzl 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])  -- -5 < 0
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.bltzl 8#32 2#32)) (setRegs regs0 [(8, 0#32)]) with  -- 0 < 0 is false
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false)
#guard stepThroughDelaySlot textBase (.bgezl 8#32 2#32) (setRegs regs0 [(8, 0#32)])  -- 0 >= 0
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.bgezl 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)]) with  -- -5>=0 false
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false)

-- `bltzall`/`bgezall` (REGIMM): same unconditional-`$ra`-link convention as
-- `bltzal`/`bgezal` -- the link happens whether the branch is taken or
-- squashed.
#guard nextRegEq (step (prog1 (.bltzall 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)])) 31
  (textBase + 8#32)  -- taken: -5 < 0
#guard nextRegEq (step (prog1 (.bltzall 8#32 2#32)) (setRegs regs0 [(8, 5#32)])) 31
  (textBase + 8#32)  -- squashed: 5 < 0 is false, $ra still linked
#guard stepThroughDelaySlot textBase (.bltzall 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.bltzall 8#32 2#32)) (setRegs regs0 [(8, 5#32)]) with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false)
#guard nextRegEq (step (prog1 (.bgezall 8#32 2#32)) (setRegs regs0 [(8, 5#32)])) 31
  (textBase + 8#32)  -- taken: 5 >= 0
#guard nextRegEq (step (prog1 (.bgezall 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)])) 31
  (textBase + 8#32)  -- squashed: -5 >= 0 is false, $ra still linked
#guard stepThroughDelaySlot textBase (.bgezall 8#32 2#32) (setRegs regs0 [(8, 5#32)])
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.bgezall 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)]) with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false)

-- ### j/jal: exact targets including top-4-bit preservation from `pc_next`;
-- jal $ra links to `pc + 8` (past the delay slot), not `pc + 4`

private def crossRegionState : State := { regs0 with pc := 0x90400000#32 }
-- `j`'s own step falls through to the delay slot, scheduling the target.
#guard (match step (progAt 0x90400000#32 (.j 0x1000#32)) crossRegionState with
        | .next s => s.pc == 0x90400004#32 && s.pendingBranch == some 0x90004000#32
        | .halt _ => false)
#guard stepThroughDelaySlot 0x90400000#32 (.j 0x1000#32) crossRegionState = some 0x90004000#32
-- `jal`: `$ra` is `pc + 8`, and the target lands the same way as `j` after
-- the delay slot.
#guard nextRegEq (step (progAt 0x90400000#32 (.jal 0x1000#32)) crossRegionState) 31 0x90400008#32
#guard stepThroughDelaySlot 0x90400000#32 (.jal 0x1000#32) crossRegionState = some 0x90004000#32

-- ### jr/jalr: register-indirect jump/call, same one-delay-slot scheduling
-- as j/jal, but the target comes from a register read. `jr $ra` is the
-- canonical function-return idiom; `jalr $rd, $rs` additionally links `$rd`
-- to `pc + 8`, exactly like `jal`'s link-value convention.

-- `jr`'s own step falls through to the delay slot, scheduling `$rs`'s raw
-- value as the target (no top-4-bit composition, unlike `j`).
#guard (match step (progAt 0x90400000#32 (.jr 8#32)) (setRegs crossRegionState [(8, 0x80020000#32)]) with
        | .next s => s.pc == 0x90400004#32 && s.pendingBranch == some 0x80020000#32
        | .halt _ => false)
#guard stepThroughDelaySlot 0x90400000#32 (.jr 8#32) (setRegs crossRegionState [(8, 0x80020000#32)])
  = some 0x80020000#32
-- the classic `jr $ra` function-return idiom: landing on whatever address
-- was previously linked into `$ra`.
#guard stepThroughDelaySlot textBase (.jr 31#32) (setRegs regs0 [(31, 0x00400040#32)])
  = some 0x00400040#32

-- `jalr $rd, $rs`: `$rd` is `pc + 8` (past the delay slot, same convention
-- as `jal`), and the target lands the same way as `jr` after the delay slot.
#guard nextRegEq (step (progAt 0x90400000#32 (.jalr 8#32 9#32)) (setRegs crossRegionState [(8, 0x80020000#32)]))
  9 0x90400008#32
#guard stepThroughDelaySlot 0x90400000#32 (.jalr 8#32 9#32) (setRegs crossRegionState [(8, 0x80020000#32)])
  = some 0x80020000#32
-- `jalr $t9, $t9` (rd = rs): the link value overwrites `$rs` only *after*
-- its pre-write value has been captured as the jump target.
#guard nextRegEq (step (progAt 0x90400000#32 (.jalr 9#32 9#32)) (setRegs crossRegionState [(9, 0x80020000#32)]))
  9 0x90400008#32
#guard stepThroughDelaySlot 0x90400000#32 (.jalr 9#32 9#32) (setRegs crossRegionState [(9, 0x80020000#32)])
  = some 0x80020000#32

-- a `jr` target that isn't 4-byte-aligned is not special-cased: the branch
-- step itself still schedules it as an ordinary `pendingBranch`, and the
-- misalignment only surfaces as an Address Error (AdEL) exception on the
-- *next* fetch attempt, once `pc` actually becomes that value.
#guard stepThroughDelaySlot 0x90400000#32 (.jr 8#32) (setRegs crossRegionState [(8, 0x80020001#32)])
  = some 0x80020001#32
#guard (match stepState (buildProg 0x90400000#32 [.jr 8#32, nopInstr])
          (setRegs crossRegionState [(8, 0x80020001#32)]) with
        | some s1 =>
          (match stepState (buildProg 0x90400000#32 [.jr 8#32, nopInstr]) s1 with
           | some s2 => raisesAddr (step (buildProg 0x90400000#32 [.jr 8#32, nopInstr]) s2) excCodeAdEL 0x80020001#32
           | none => false)
        | none => false)

-- ### branch/jump in a delay slot: diagnosable halt, not arbitrary behavior

-- A branch immediately following a *taken* branch (i.e. itself occupying
-- the delay slot) halts rather than silently scheduling/overwriting
-- anything — real MIPS32 leaves this architecturally discouraged/
-- implementation-defined (INSTRUCTION-REF Global rule 3).
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .beq 0#32 0#32 0#32])
          (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          isHaltBranchInDelaySlot
            (step (buildProg textBase [.beq 8#32 9#32 1#32, .beq 0#32 0#32 0#32]) s1)
        | none => false)
-- A branch following a *not-taken* branch is in a delay slot just the same
-- (the delay slot exists whether or not the branch is taken), so it halts
-- identically.
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .beq 0#32 0#32 0#32])
          (setRegs regs0 [(8, 5#32), (9, 6#32)]) with
        | some s1 =>
          isHaltBranchInDelaySlot
            (step (buildProg textBase [.beq 8#32 9#32 1#32, .beq 0#32 0#32 0#32]) s1)
        | none => false)
-- ... as do `eret` and `bc1t`/`bc1f` in a delay slot (taken or not).
#guard (match stepState (buildProg textBase [.j 0x100#32, .eret]) regs0 with
        | some s1 => isHaltBranchInDelaySlot (step (buildProg textBase [.j 0x100#32, .eret]) s1)
        | none => false)
#guard (match stepState (buildProg textBase [.bne 0#32 0#32 1#32, .bc1t 0#32 1#32]) regs0 with
        | some s1 => isHaltBranchInDelaySlot (step (buildProg textBase [.bne 0#32 0#32 1#32, .bc1t 0#32 1#32]) s1)
        | none => false)
#guard (match stepState (buildProg textBase [.jr 31#32, .bc1f 0#32 1#32]) regs0 with
        | some s1 => isHaltBranchInDelaySlot (step (buildProg textBase [.jr 31#32, .bc1f 0#32 1#32]) s1)
        | none => false)
-- `j` right after a taken `beq` halts the same way.
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .j 0x1000#32])
          (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          isHaltBranchInDelaySlot (step (buildProg textBase [.beq 8#32 9#32 1#32, .j 0x1000#32]) s1)
        | none => false)
-- `bltz` right after a taken `beq` halts the same way (confirms the REGIMM
-- branches are included in `isBranchLike`).
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .bltz 8#32 0#32])
          (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          isHaltBranchInDelaySlot
            (step (buildProg textBase [.beq 8#32 9#32 1#32, .bltz 8#32 0#32]) s1)
        | none => false)
-- `beql` right after a taken `beq` halts the same way (confirms the
-- branch-likely family is included in `isBranchLike`, same `pendingBranch`
-- condition as every other branch/jump).
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .beql 8#32 8#32 0#32])
          (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          isHaltBranchInDelaySlot
            (step (buildProg textBase [.beq 8#32 9#32 1#32, .beql 8#32 8#32 0#32]) s1)
        | none => false)

-- ### syscalls

#guard (stepState (prog1 (.syscall 0#32)) (setRegs regs0 [(2, 1#32), (4, 5#32)])).bind (fun s => some s.out)
  = some "5"
#guard (stepState (prog1 (.syscall 0#32)) (setRegs regs0 [(2, 1#32), (4, 0xfffffffb#32)])).bind (fun s => some s.out)
  = some "-5"
private def syscall4State : State :=
  { (setRegs regs0 [(2, 4#32), (4, 0x10010000#32)]) with
      mem := (((∅ : Std.HashMap W32 UInt8).insert 0x10010000#32 0x48).insert 0x10010001#32 0x69)
               |>.insert 0x10010002#32 0 }
#guard (stepState (prog1 (.syscall 0#32)) syscall4State).bind (fun s => some s.out) = some "Hi"
private def syscall4EmptyState : State :=
  { (setRegs regs0 [(2, 4#32), (4, 0x10010000#32)]) with
      mem := (∅ : Std.HashMap W32 UInt8).insert 0x10010000#32 0 }
#guard (stepState (prog1 (.syscall 0#32)) syscall4EmptyState).bind (fun s => some s.out) = some ""
#guard isHaltExit (step (prog1 (.syscall 0#32)) (setRegs regs0 [(2, 10#32)]))
#guard (stepState (prog1 (.syscall 0#32)) (setRegs regs0 [(2, 11#32), (4, 0x41#32)])).bind (fun s => some s.out)
  = some "A"
#guard raises (step (prog1 (.syscall 0#32)) (setRegs regs0 [(2, 999#32)])) excCodeSys

-- ### Traps / exceptions (coprocessor 0): teq/tne/tlt/tge/tltu/tgeu/break

private def cp0Eq (r : StepResult) (epc cause status pc : W32) : Bool :=
  match r with
  | .next s => s.cp0Epc == epc && s.cp0Cause == cause && s.cp0Status == status && s.pc == pc
  | .halt _ => false

private def cp0Untouched (r : StepResult) (before : State) : Bool :=
  match r with
  | .next s => s.cp0Epc == before.cp0Epc && s.cp0Cause == before.cp0Cause
                 && s.cp0Status == before.cp0Status
  | .halt _ => false

-- teq: trap-taken from `textBase` sets `EPC = textBase` (the trapping
-- instruction's own address, not `pc + 4`), `Cause.ExcCode = excCodeTr`
-- packed into bits 6..2 (`excCodeTr <<< 2`), `Status.EXL` (bit 1) set, and
-- `pc = exceptionVectorAddr`.
#guard cp0Eq (step (prog1 (.teq 8#32 9#32 0#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr
-- teq: trap-not-taken behaves like an ordinary instruction (falls through
-- to `pc + 4`) and leaves all CP0 state untouched.
#guard nextPcEq (step (prog1 (.teq 8#32 9#32 0#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]))
  (textBase + 4#32)
#guard cp0Untouched (step (prog1 (.teq 8#32 9#32 0#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)])) regs0

-- tne: trap on not-equal (opposite condition from teq)
#guard cp0Eq (step (prog1 (.tne 8#32 9#32 0#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr
#guard isNext (step (prog1 (.tne 8#32 9#32 0#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]))

-- tlt/tge: signed comparison (negative `$rs` is less than positive `$rt`)
#guard cp0Eq (step (prog1 (.tlt 8#32 9#32 0#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr  -- -1 < 1
#guard isNext (step (prog1 (.tlt 8#32 9#32 0#32)) (setRegs regs0 [(8, 1#32), (9, 0xffffffff#32)]))  -- 1 < -1 false
#guard cp0Eq (step (prog1 (.tge 8#32 9#32 0#32)) (setRegs regs0 [(8, 1#32), (9, 0xffffffff#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr  -- 1 >= -1
#guard isNext (step (prog1 (.tge 8#32 9#32 0#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))  -- -1 >= 1 false

-- tltu/tgeu: unsigned comparison (0xffffffff is the largest unsigned value,
-- so it is never `<u` anything and always `>=u` everything)
#guard isNext (step (prog1 (.tltu 8#32 9#32 0#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))
#guard cp0Eq (step (prog1 (.tgeu 8#32 9#32 0#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr

-- ### Trap-immediate family (REGIMM, real MIPS32 ISA;
-- docs/spec/MIPS-COVERAGE-GAPS.md §3.8): teqi/tnei/tgei/tgeiu/tlti/tltiu,
-- the sign-extended-16-bit-immediate counterpart of teq/tne/tlt/tge/tltu/tgeu.

-- teqi: trap-taken when `$rs == sext16(imm)`; trap-not-taken behaves like
-- an ordinary instruction and leaves all CP0 state untouched.
#guard cp0Eq (step (prog1 (.teqi 8#32 5#32)) (setRegs regs0 [(8, 5#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr
#guard isNext (step (prog1 (.teqi 8#32 5#32)) (setRegs regs0 [(8, 6#32)]))
#guard cp0Untouched (step (prog1 (.teqi 8#32 5#32)) (setRegs regs0 [(8, 6#32)])) regs0

-- tnei: trap on not-equal (opposite condition from teqi)
#guard cp0Eq (step (prog1 (.tnei 8#32 5#32)) (setRegs regs0 [(8, 6#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr
#guard isNext (step (prog1 (.tnei 8#32 5#32)) (setRegs regs0 [(8, 5#32)]))

-- tgei/tlti: signed comparison against `sext16(imm)`; imm = 0xffff sign-
-- extends to -1.
#guard cp0Eq (step (prog1 (.tgei 8#32 0xffff#32)) (setRegs regs0 [(8, 0xffffffff#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr  -- -1 >= -1
#guard isNext (step (prog1 (.tgei 8#32 0xffff#32)) (setRegs regs0 [(8, 0xfffffffe#32)]))  -- -2 >= -1 false
#guard cp0Eq (step (prog1 (.tlti 8#32 1#32)) (setRegs regs0 [(8, 0xffffffff#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr  -- -1 < 1
#guard isNext (step (prog1 (.tlti 8#32 1#32)) (setRegs regs0 [(8, 1#32)]))  -- 1 < 1 false

-- tgeiu/tltiu: the immediate is sign-extended to 32 bits first, *then* the
-- comparison is unsigned on the resulting bit pattern -- same convention
-- `sltiu` already uses. Edge case where the signed and unsigned
-- interpretations of the same `$rs` bit pattern disagree: $rs = 0xffffffff
-- (signed -1, unsigned max) against imm = 1 (sext16(1) = 1); unsigned
-- 0xffffffff >=u 1 is true (traps), even though a signed read of the same
-- bits (-1 >= 1) would be false.
#guard cp0Eq (step (prog1 (.tgeiu 8#32 1#32)) (setRegs regs0 [(8, 0xffffffff#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr
#guard isNext (step (prog1 (.tltiu 8#32 1#32)) (setRegs regs0 [(8, 0xffffffff#32)]))  -- 0xffffffff <u 1 false
#guard cp0Eq (step (prog1 (.tltiu 8#32 1#32)) (setRegs regs0 [(8, 0#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr  -- 0 <u 1 true

-- a negative-immediate edge case: imm = 0xffff (sext16 = -1, i.e. bit
-- pattern 0xffffffff) compared *unsigned* against $rs = 1 does NOT trap
-- (1 >=u 0xffffffff is false) under tgeiu, unlike the signed tgei case
-- with the exact same operands (1 >= -1 is true, traps) -- demonstrating
-- tgeiu really does compare unsigned, not just sign-extend-and-reuse-tgei.
#guard isNext (step (prog1 (.tgeiu 8#32 0xffff#32)) (setRegs regs0 [(8, 1#32)]))
#guard cp0Eq (step (prog1 (.tgei 8#32 0xffff#32)) (setRegs regs0 [(8, 1#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr

-- break: unconditional trap, distinct `ExcCode` (`excCodeBp` ≠ `excCodeTr`)
-- from the same starting state/address as the teq case above.
#guard excCodeBp ≠ excCodeTr
#guard cp0Eq (step (prog1 (.break 0#32)) regs0)
  textBase (excCodeBp <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr

-- a second trap from a nonzero `pc` records that instruction's own address
-- in `EPC`, not `textBase`/`pc + 4`.
private def trapAtState : State := { regs0 with pc := textBase + 0x100#32 }
#guard cp0Eq (step (progAt (textBase + 0x100#32) (.break 0#32)) trapAtState)
  (textBase + 0x100#32) (excCodeBp <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr

-- no handler installed at the vector: the *next* `step` from the post-trap
-- state finds no instruction there while `EXL = 1`, and halts with
-- `unhandledException ExcCode EPC BadVAddr`.
#guard (match stepState (prog1 (.break 0#32)) regs0 with
        | some s' => isHaltUnhandled (step (prog1 (.break 0#32)) s') excCodeBp textBase 0#32
        | none => false)
-- an aligned `pc` outside the program, with no exception pending, is the
-- model-boundary halt `noInstruction`.
#guard isHaltNoInstr (step (∅ : Program) regs0) textBase

-- if a real handler word *is* present at the vector address, it executes
-- normally after the trap (e.g. an `addi` landing there).
private def vectorHandlerProg : Program :=
  (prog1 (.break 0#32)).insert exceptionVectorAddr (encode (.addi 0#32 8#32 42#32))
#guard (match stepState vectorHandlerProg regs0 with
        | some s' => nextRegEq (step vectorHandlerProg s') 8 42#32
        | none => false)

-- ### Coprocessor 0 (CP0): mfc0/mtc0/eret/wait (docs/spec/MIPS-COVERAGE-GAPS.md
-- §3.10A)

-- mfc0 reads back Status/Cause/EPC, selected by `rd` (12/13/14).
#guard nextRegEq (step (prog1 (.mfc0 8#32 12#32 0#32)) { regs0 with cp0Status := 0x2#32 }) 8 0x2#32
#guard nextRegEq (step (prog1 (.mfc0 8#32 13#32 0#32)) { regs0 with cp0Cause := 0x34#32 }) 8 0x34#32
#guard nextRegEq (step (prog1 (.mfc0 8#32 14#32 0#32)) { regs0 with cp0Epc := 0x3000#32 }) 8 0x3000#32

-- mtc0 writes Status/EPC from a GPR (Cause/BadVAddr/ErrorEPC: see below).
#guard (match stepState (prog1 (.mtc0 8#32 12#32 0#32)) (setRegs regs0 [(8, 0x2#32)]) with
        | some s' => s'.cp0Status == 0x2#32
        | none => false)
-- `mtc0` to Cause writes only DC (27), IV (23) and IP1..0 (9:8); ExcCode/BD
-- and every other bit keep their old value.
#guard (match stepState (prog1 (.mtc0 8#32 13#32 0#32)) (setRegs regs0 [(8, 0xffffffff#32)]) with
        | some s' => s'.cp0Cause == 0x08800300#32
        | none => false)
#guard (match stepState (prog1 (.mtc0 8#32 13#32 0#32))
          { (setRegs regs0 [(8, 0#32)]) with cp0Cause := 0x80c00334#32 } with
        | some s' => s'.cp0Cause == 0x80400034#32
        | none => false)
-- `mtc0` to Status keeps only IE, EXL, ERL, IM7..0, BEV, CU1.
#guard (match stepState (prog1 (.mtc0 8#32 12#32 0#32)) (setRegs regs0 [(8, 0xffffffff#32)]) with
        | some s' => s'.cp0Status == 0x2040ff07#32
        | none => false)
-- BadVAddr (8) is read-only: `mtc0` to it is ignored; `mfc0` reads it.
#guard (match stepState (prog1 (.mtc0 8#32 8#32 0#32)) { (setRegs regs0 [(8, 0x1234#32)]) with cp0BadVAddr := 0x77#32 } with
        | some s' => s'.cp0BadVAddr == 0x77#32 && s'.pc == textBase + 4#32
        | none => false)
#guard nextRegEq (step (prog1 (.mfc0 8#32 8#32 0#32)) { regs0 with cp0BadVAddr := 0x10010001#32 }) 8 0x10010001#32
-- ErrorEPC (30) is fully readable/writable.
#guard (match stepState (prog1 (.mtc0 8#32 30#32 0#32)) (setRegs regs0 [(8, 0x3000#32)]) with
        | some s' => s'.cp0ErrorEpc == 0x3000#32
        | none => false)
#guard nextRegEq (step (prog1 (.mfc0 8#32 30#32 0#32)) { regs0 with cp0ErrorEpc := 0x3004#32 }) 8 0x3004#32
#guard (match stepState (prog1 (.mtc0 8#32 14#32 0#32)) (setRegs regs0 [(8, 0x3000#32)]) with
        | some s' => s'.cp0Epc == 0x3000#32
        | none => false)

-- mtc0 then mfc0 reads back the written value through the register's write
-- mask (Status: 0xabcd &&& 0x2040ff07; Cause: 0xabcd &&& 0x00800300; EPC: all).
#guard (match stepState (prog1 (.mtc0 8#32 12#32 0#32)) (setRegs regs0 [(8, 0xabcd#32)]) with
        | some s' => nextRegEq (step (prog1 (.mfc0 9#32 12#32 0#32)) { s' with pc := textBase }) 9
            0xab05#32
        | none => false)
#guard (match stepState (prog1 (.mtc0 8#32 13#32 0#32)) (setRegs regs0 [(8, 0xabcd#32)]) with
        | some s' => nextRegEq (step (prog1 (.mfc0 9#32 13#32 0#32)) { s' with pc := textBase }) 9
            0x0300#32
        | none => false)
#guard (match stepState (prog1 (.mtc0 8#32 14#32 0#32)) (setRegs regs0 [(8, 0xabcd#32)]) with
        | some s' => nextRegEq (step (prog1 (.mfc0 9#32 14#32 0#32)) { s' with pc := textBase }) 9
            0xabcd#32
        | none => false)

-- mfc0/mtc0 naming a CP0 register the model does not have (anything but
-- 8/12/13/14/30, sel 0) do not decode, so they raise Reserved Instruction.
#guard raises (step (prog1 (.mfc0 8#32 0#32 0#32)) regs0) excCodeRI
#guard raises (step (prog1 (.mtc0 8#32 0#32 0#32)) (setRegs regs0 [(8, 1#32)])) excCodeRI

-- eret: restores `pc` from `cp0Epc` and clears `Status.EXL` (bit 1, the same
-- bit `takeException` sets) in a *single* `step` call -- no delay-slot
-- scheduling (`pendingBranch` stays `none`, confirming `eret` bypasses
-- `mkNext` entirely rather than landing one instruction later).
private def eretReadyState : State :=
  { regs0 with cp0Epc := 0x3000#32, cp0Status := statusExlMask, pendingBranch := none }
#guard nextPcEq (step (prog1 .eret) eretReadyState) 0x3000#32
#guard (match stepState (prog1 .eret) eretReadyState with
        | some s' => s'.cp0Status == 0#32 && s'.pendingBranch == none
        | none => false)

-- full round trip: `teq` traps from `textBase` to `exceptionVectorAddr`
-- (confirming `cp0Epc`/`pc` land at the expected places, same as the
-- existing teq tests above), then `eret` placed at the vector returns
-- `pc` exactly to the original trapping instruction's address and clears
-- `Status.EXL`.
private def teqEretProg : Program :=
  ((∅ : Program).insert textBase (encode (.teq 8#32 9#32 0#32))).insert exceptionVectorAddr (encode .eret)
#guard (match stepState teqEretProg (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          s1.cp0Epc == textBase && s1.pc == exceptionVectorAddr && s1.cp0Status == (statusCu1Mask ||| statusExlMask) &&
            (match stepState teqEretProg s1 with
             | some s2 => s2.pc == textBase && s2.cp0Status == statusCu1Mask
             | none => false)
        | none => false)

-- ### Exception entry: the general exception sequence (MD00090)

-- Exception in a branch delay slot (taken branch): `EPC` = the *branch's*
-- address, `Cause.BD` = 1, the pending branch is abandoned, and the handler
-- then runs sequentially from the vector (it does not jump to the old
-- branch target).
private def bdProg : Program :=
  ((buildProg textBase [.beq 0#32 0#32 0x10#32, (.break 0#32)]).insert exceptionVectorAddr
      (encode (.addiu 0#32 8#32 1#32))).insert (exceptionVectorAddr + 4#32) (encode (.addiu 0#32 9#32 2#32))
#guard (match stepN bdProg 2 regs0 with
        | some s2 => s2.cp0Epc == textBase && s2.cp0Cause == (causeBdMask ||| (excCodeBp <<< 2))
            && s2.pc == exceptionVectorAddr && s2.pendingBranch == none && s2.cp0Status == (statusCu1Mask ||| statusExlMask)
        | none => false)
#guard (match stepN bdProg 4 regs0 with
        | some s4 => s4.pc == exceptionVectorAddr + 8#32 && readReg s4 8 == 1#32 && readReg s4 9 == 2#32
        | none => false)
-- Same after a *not-taken* branch: the instruction is still in a delay slot.
#guard (match stepN (buildProg textBase [.bne 0#32 0#32 0x10#32, (.break 0#32)]) 2 regs0 with
        | some s2 => s2.cp0Epc == textBase && s2.cp0Cause == (causeBdMask ||| (excCodeBp <<< 2))
            && s2.pendingBranch == none
        | none => false)
-- Not in a delay slot: `EPC = pc`, and `Cause.BD` is *cleared* if it was set.
#guard cp0Eq (step (prog1 (.break 0#32)) { regs0 with cp0Cause := causeBdMask })
  textBase (excCodeBp <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr
-- `Status.EXL = 1` already: `EPC` and `Cause.BD` are left unchanged; only
-- `ExcCode` is updated.
#guard cp0Eq (step (prog1 (.break 0#32)) { regs0 with cp0Status := statusExlMask, cp0Epc := 0x1234#32,
                                                      cp0Cause := causeBdMask ||| (excCodeTr <<< 2) })
  0x1234#32 (causeBdMask ||| (excCodeBp <<< 2)) statusExlMask exceptionVectorAddr
-- Only `ExcCode` (bits 6..2) is written: IV (bit 23) and IP1..0 (bits 9:8)
-- survive. `Cause = 0x00800300` becomes `0x00800324` on `break`.
#guard cp0Eq (step (prog1 (.break 0#32)) { regs0 with cp0Cause := 0x00800300#32 })
  textBase 0x00800324#32 (statusCu1Mask ||| statusExlMask) exceptionVectorAddr
-- `Status.BEV = 1` selects the bootstrap vector `0xBFC00380`.
#guard cp0Eq (step (prog1 (.break 0#32)) { regs0 with cp0Status := statusBevMask })
  textBase (excCodeBp <<< 2) (statusBevMask ||| statusExlMask) exceptionVectorBevAddr

-- ### Integer Overflow / Address Error / Reserved Instruction / Syscall are
-- exceptions, not halts

-- `add` overflow with a handler installed at the vector: the handler runs,
-- `Cause.ExcCode = 12`, `EPC` = the `add`, and `$rd` was not written.
private def ovHandlerProg : Program :=
  (prog1 (.add 8#32 9#32 10#32)).insert exceptionVectorAddr (encode (.mfc0 26#32 13#32 0#32))
private def ovState : State := setRegs regs0 [(8, 0x7fffffff#32), (9, 1#32), (10, 0x55#32)]
#guard (match stepN ovHandlerProg 2 ovState with
        | some s2 => readReg s2 26 == (excCodeOv <<< 2) && s2.cp0Epc == textBase
            && readReg s2 10 == 0x55#32 && s2.pc == exceptionVectorAddr + 4#32
        | none => false)
-- ... and with no handler: `unhandledException 12 EPC BadVAddr`.
#guard (match run (prog1 (.add 8#32 9#32 10#32)) ovState 10 with
        | .halted (.unhandledException c epc _) s steps =>
            c == 12#32 && epc == textBase && steps == 2 && readReg s 10 == 0x55#32
        | _ => false)
-- Address errors report the failing address in the halt when unhandled.
#guard (match run (prog1 (.lw 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)]) 10 with
        | .halted (.unhandledException c epc bad) _ _ => c == 4#32 && epc == textBase && bad == 0x10010001#32
        | _ => false)
#guard (match run (prog1 (.sw 8#32 9#32 2#32)) (setRegs regs0 [(8, 0x10010000#32)]) 10 with
        | .halted (.unhandledException c epc bad) _ _ => c == 5#32 && epc == textBase && bad == 0x10010002#32
        | _ => false)
-- A failed store leaves memory untouched; like every exception entry it
-- clears `llBit`.
#guard (match stepState (prog1 (.sw 8#32 9#32 2#32)) { (setRegs regs0 [(8, 0x10010000#32), (9, 0xff#32)]) with llBit := true } with
        | some s' => s'.llBit == false && readMemWord s' 0x10010000#32 == some 0#32
        | none => false)
-- Undecodable word, unhandled: ExcCode 10.
#guard (match run ((∅ : Program).insert textBase ((0x11#32 <<< 26) ||| (0x1f#32 <<< 21))) regs0 10 with
        | .halted (.unhandledException c epc _) _ _ => c == 10#32 && epc == textBase
        | _ => false)
-- `syscall` outside the environment-call convention: ExcCode 8.
#guard (match run (prog1 (.syscall 0#32)) (setRegs regs0 [(2, 999#32)]) 10 with
        | .halted (.unhandledException c epc _) _ _ => c == 8#32 && epc == textBase
        | _ => false)
-- Misaligned fetch: AdEL with `EPC = BadVAddr = pc`.
#guard (match run (∅ : Program) misalignedState 10 with
        | .halted (.unhandledException c epc bad) _ _ => c == 4#32 && epc == textBase + 1#32 && bad == textBase + 1#32
        | _ => false)

-- ### eret: ERL selects ErrorEPC; LLbit is always cleared

#guard (match stepState (prog1 .eret)
          { regs0 with cp0Epc := 0x3000#32, cp0ErrorEpc := 0x4000#32, cp0Status := statusErlMask ||| statusExlMask } with
        | some s' => s'.pc == 0x4000#32 && s'.cp0Status == statusExlMask
        | none => false)
#guard (match stepState (prog1 .eret) { eretReadyState with llBit := true } with
        | some s' => s'.llBit == false
        | none => false)
-- `ll` / (exception) / `eret` / `sc`: the `sc` fails -- `$rt = 0` and memory
-- is not written.
private def llEretScProg : Program :=
  (buildProg textBase [.ll 8#32 9#32 0#32, (.break 0#32), .sc 8#32 10#32 0#32]).insert exceptionVectorAddr (encode .eret)
#guard (match stepN llEretScProg 2 (setRegs regs0 [(8, llscAddr), (10, 0xdeadbeef#32)]) with
        | some s2 =>
          -- handler: skip the `break` (EPC += 4 by hand), then `eret`, then `sc`
          (match stepN llEretScProg 2 { s2 with cp0Epc := s2.cp0Epc + 4#32 } with
           | some s4 => readReg s4 10 == 0#32 && s4.llBit == false && readMemWord s4 llscAddr == some 0#32
           | none => false)
        | none => false)

-- Exception entry clears `llBit`: `ll` / `break` / (handler returns by a plain
-- `jr`, not `eret`) / `sc` still fails.
#guard (match stepState (prog1 (.break 0#32)) { regs0 with llBit := true } with
        | some s' => s'.llBit == false
        | none => false)
-- `wait` in a delay slot halts, like `eret`.
#guard (match stepState (buildProg textBase [.j 0x100#32, (.wait 0#32)]) regs0 with
        | some s1 => isHaltBranchInDelaySlot (step (buildProg textBase [.j 0x100#32, (.wait 0#32)]) s1)
        | none => false)

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

-- ### Undecodable word → Reserved Instruction exception

-- opcode 0x11 (COP1) is implemented for the fmt/funct combinations decoded
-- in `Instruction.lean`; fmt=0x1f is not one of them, so this word is still
-- genuinely undecodable.
private def badWord : W32 := (0x11#32 <<< 26) ||| (0x1f#32 <<< 21)
private def badProg : Program := (∅ : Program).insert textBase badWord
#guard raises (step badProg regs0) excCodeRI

-- ### Coprocessor 1 (FPU)
--
-- Bit patterns: 1.0 = 0x3f800000, 2.0 = 0x40000000, 2.5 = 0x40200000,
-- 3.0 = 0x40400000, 3.5 = 0x40600000, −2.5 = 0xc0200000, +∞ = 0x7f800000,
-- legacy QNaN 0x7fbfffff (the default), legacy SNaN 0x7fc00000.
-- FCSR fields: Cause V/Z/O/U/I = bits 16/15/14/13/12, Enables = 11..7,
-- Flags = 6..2, RM = 1..0, FCC0 = bit 23, FCC1..7 = bits 25..31.

private def fp1 (instr : Instruction) (fprs : List (Fin 32 × W32)) (fcsr : W32 := 0#32)
    (gprs : List (Fin 32 × W32) := []) : StepResult :=
  step (prog1 instr) { (setFpRegs (setRegs regs0 gprs) fprs) with fcsr := fcsr }

/-- `r` completed normally with `FPR[i] = v` and `FCSR = fcsr`. -/
private def fpIs (r : StepResult) (i : Fin 32) (v fcsr : W32) : Bool :=
  match r with
  | .next s => readFpReg s i == v && s.fcsr == fcsr && s.pc == textBase + 4#32
  | .halt _ => false

/-- `r` is a Floating Point exception entry (ExcCode 15, `CE` = 0) with
`FCSR = fcsr` and `FPR[i]` still `v`. -/
private def fpTraps (r : StepResult) (i : Fin 32) (v fcsr : W32) : Bool :=
  raises r excCodeFPE &&
    (match r with
     | .next s => readFpReg s i == v && s.fcsr == fcsr && s.cp0Cause &&& causeCeMask == 0#32
     | .halt _ => false)

private def nextFcsrEq (r : StepResult) (v : W32) : Bool :=
  match r with
  | .next s => s.fcsr == v
  | .halt _ => false

-- mtc1 then mfc1 round-trips an arbitrary bit pattern through $f3
#guard nextFpRegEq (step (prog1 (.mtc1 8#32 3#32)) (setRegs regs0 [(8, 0x12345678#32)])) 3
  0x12345678#32
#guard nextRegEq (fp1 (.mfc1 9#32 3#32) [(3, 0x12345678#32)]) 9 0x12345678#32
-- mfhc1/mthc1 address the high word of the double in $f4, i.e. FPR[5]
#guard nextRegEq (fp1 (.mfhc1 9#32 4#32) [(4, 0x11111111#32), (5, 0x22222222#32)]) 9 0x22222222#32
#guard nextFpRegEq (fp1 (.mthc1 9#32 4#32) [(4, 0x11111111#32)] 0#32 [(9, 0xabcdef01#32)]) 5
  0xabcdef01#32
#guard nextFpRegEq (fp1 (.mthc1 9#32 4#32) [(4, 0x11111111#32)] 0#32 [(9, 0xabcdef01#32)]) 4
  0x11111111#32

-- #### Arithmetic, rounding modes, flags
-- 1.0 + 2.0 = 3.0, exact: FCSR unchanged (Cause cleared)
#guard fpIs (fp1 (.addS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40000000#32)]) 2 0x40400000#32 0#32
-- an exact operation clears a stale Cause but keeps Flags, RM, FCC
#guard fpIs (fp1 (.addS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40000000#32)] 0xfe81f07f#32) 2
  0x40400000#32 0xfe80007f#32
-- 1.0 / 3.0 in the four rounding modes: Inexact in Cause (bit 12) and Flags (bit 2)
#guard fpIs (fp1 (.divS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40400000#32)] 0#32) 2
  0x3eaaaaab#32 0x00001004#32
#guard fpIs (fp1 (.divS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40400000#32)] 1#32) 2
  0x3eaaaaaa#32 0x00001005#32
#guard fpIs (fp1 (.divS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40400000#32)] 2#32) 2
  0x3eaaaaab#32 0x00001006#32
#guard fpIs (fp1 (.divS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40400000#32)] 3#32) 2
  0x3eaaaaaa#32 0x00001007#32
-- 1.0 / 0.0 = +∞, Divide by Zero (Cause bit 15, Flags bit 5)
#guard fpIs (fp1 (.divS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0#32)]) 2 0x7f800000#32 0x00008020#32
-- invalid operations create the legacy default QNaN 0x7fbfffff (V: bits 16 and 6)
#guard fpIs (fp1 (.divS 2#32 4#32 6#32) [(4, 0#32), (6, 0#32)]) 2 0x7fbfffff#32 0x00010040#32
#guard fpIs (fp1 (.subS 2#32 4#32 6#32) [(4, 0x7f800000#32), (6, 0x7f800000#32)]) 2 0x7fbfffff#32
  0x00010040#32
#guard fpIs (fp1 (.sqrtS 2#32 4#32) [(4, 0xbf800000#32)]) 2 0x7fbfffff#32 0x00010040#32
#guard fpIs (fp1 (.mulS 2#32 4#32 6#32) [(4, 0#32), (6, 0x7f800000#32)]) 2 0x7fbfffff#32 0x00010040#32
-- overflow: largest × 2 → +∞ under RN, largest under RZ (O|I: Cause 14,12; Flags 4,2)
#guard fpIs (fp1 (.mulS 2#32 4#32 6#32) [(4, 0x7f7fffff#32), (6, 0x40000000#32)]) 2 0x7f800000#32
  0x00005014#32
#guard fpIs (fp1 (.mulS 2#32 4#32 6#32) [(4, 0x7f7fffff#32), (6, 0x40000000#32)] 1#32) 2
  0x7f7fffff#32 0x00005015#32
-- underflow: smallest subnormal / 2 → 0 (U|I: Cause 13,12; Flags 3,2)
#guard fpIs (fp1 (.divS 2#32 4#32 6#32) [(4, 1#32), (6, 0x40000000#32)]) 2 0#32 0x0000300c#32
-- sqrt(2), sqrt(4)
#guard fpIs (fp1 (.sqrtS 2#32 4#32) [(4, 0x40000000#32)]) 2 0x3fb504f3#32 0x00001004#32
#guard fpIs (fp1 (.sqrtS 2#32 4#32) [(4, 0x40800000#32)]) 2 0x40000000#32 0#32
-- NaN propagation: a quiet NaN operand is copied, no exception; an SNaN signals Invalid
#guard fpIs (fp1 (.addS 2#32 4#32 6#32) [(4, 0x7f800123#32), (6, 0x3f800000#32)]) 2 0x7f800123#32 0#32
#guard fpIs (fp1 (.addS 2#32 4#32 6#32) [(4, 0x7fc00000#32), (6, 0x3f800000#32)]) 2 0x7fbfffff#32
  0x00010040#32
-- abs/neg are arithmetic: sign-bit only on numbers; any NaN signals Invalid
#guard fpIs (fp1 (.absS 2#32 4#32) [(4, 0xc0200000#32)]) 2 0x40200000#32 0#32
#guard fpIs (fp1 (.negS 2#32 4#32) [(4, 0x40200000#32)]) 2 0xc0200000#32 0#32
#guard fpIs (fp1 (.absS 2#32 4#32) [(4, 0x7fc00000#32)]) 2 0x7fbfffff#32 0x00010040#32   -- SNaN
#guard fpIs (fp1 (.negS 2#32 4#32) [(4, 0xff800123#32)]) 2 0xff800123#32 0x00010040#32   -- QNaN
-- mov.s is non-arithmetic: an SNaN is copied, FCSR untouched
#guard fpIs (fp1 (.movS 2#32 4#32) [(4, 0x7fc00000#32)] 0x0000f07c#32) 2 0x7fc00000#32 0x0000f07c#32
-- recip / rsqrt / madd family
#guard fpIs (fp1 (.recipS 2#32 4#32) [(4, 0x40000000#32)]) 2 0x3f000000#32 0#32
#guard fpIs (fp1 (.rsqrtS 2#32 4#32) [(4, 0x40800000#32)]) 2 0x3f000000#32 0#32
#guard fpIs (fp1 (.rsqrtS 2#32 4#32) [(4, 0#32)]) 2 0x7f800000#32 0x00008020#32
-- madd.s $f2, $f8(fr), $f4, $f6: 2 × 3 + 1 = 7; msub 5; nmadd −7; nmsub −5
#guard fpIs (fp1 (.maddS 2#32 8#32 4#32 6#32)
  [(4, 0x40000000#32), (6, 0x40400000#32), (8, 0x3f800000#32)]) 2 0x40e00000#32 0#32
#guard fpIs (fp1 (.msubS 2#32 8#32 4#32 6#32)
  [(4, 0x40000000#32), (6, 0x40400000#32), (8, 0x3f800000#32)]) 2 0x40a00000#32 0#32
#guard fpIs (fp1 (.nmaddS 2#32 8#32 4#32 6#32)
  [(4, 0x40000000#32), (6, 0x40400000#32), (8, 0x3f800000#32)]) 2 0xc0e00000#32 0#32
#guard fpIs (fp1 (.nmsubS 2#32 8#32 4#32 6#32)
  [(4, 0x40000000#32), (6, 0x40400000#32), (8, 0x3f800000#32)]) 2 0xc0a00000#32 0#32
-- unfused: (1+2^−23)² rounds to 1+2^−22 before −(1+2^−22) is added → +0, Inexact
#guard fpIs (fp1 (.maddS 2#32 8#32 4#32 6#32)
  [(4, 0x3f800001#32), (6, 0x3f800001#32), (8, 0xbf800002#32)]) 2 0#32 0x00001004#32

-- #### Conversions
-- cvt.w.s follows FCSR.RM: 3.5 → 4 (RN, even), 2.5 → 2 (RN), 3 (RP); −2.5 → −3 (RM), −2 (RZ)
#guard fpIs (fp1 (.cvtWS 2#32 4#32) [(4, 0x40600000#32)]) 2 4#32 0x00001004#32
#guard fpIs (fp1 (.cvtWS 2#32 4#32) [(4, 0x40200000#32)]) 2 2#32 0x00001004#32
#guard fpIs (fp1 (.cvtWS 2#32 4#32) [(4, 0x40200000#32)] 2#32) 2 3#32 0x00001006#32
#guard fpIs (fp1 (.cvtWS 2#32 4#32) [(4, 0xc0200000#32)] 3#32) 2 0xfffffffd#32 0x00001007#32
#guard fpIs (fp1 (.cvtWS 2#32 4#32) [(4, 0xc0200000#32)] 1#32) 2 0xfffffffe#32 0x00001005#32
-- round/trunc/ceil/floor ignore FCSR.RM (here RM = 3)
#guard fpIs (fp1 (.roundWS 2#32 4#32) [(4, 0x40200000#32)] 3#32) 2 2#32 0x00001007#32
#guard fpIs (fp1 (.roundWS 2#32 4#32) [(4, 0xc0200000#32)] 3#32) 2 0xfffffffe#32 0x00001007#32
#guard fpIs (fp1 (.roundWS 2#32 4#32) [(4, 0x40600000#32)] 3#32) 2 4#32 0x00001007#32
#guard fpIs (fp1 (.truncWS 2#32 4#32) [(4, 0xc0200000#32)] 3#32) 2 0xfffffffe#32 0x00001007#32
#guard fpIs (fp1 (.ceilWS 2#32 4#32) [(4, 0x40200000#32)] 3#32) 2 3#32 0x00001007#32
#guard fpIs (fp1 (.floorWS 2#32 4#32) [(4, 0xc0200000#32)] 0#32) 2 0xfffffffd#32 0x00001004#32
-- invalid conversions: NaN, ±∞, out of range (either sign) → 0x7fffffff, Invalid
#guard fpIs (fp1 (.cvtWS 2#32 4#32) [(4, 0x7fbfffff#32)]) 2 0x7fffffff#32 0x00010040#32
#guard fpIs (fp1 (.truncWS 2#32 4#32) [(4, 0xff800000#32)]) 2 0x7fffffff#32 0x00010040#32
#guard fpIs (fp1 (.truncWS 2#32 4#32) [(4, 0x4f000000#32)]) 2 0x7fffffff#32 0x00010040#32   -- 2^31
#guard fpIs (fp1 (.truncWS 2#32 4#32) [(4, 0xdf000000#32)]) 2 0x7fffffff#32 0x00010040#32   -- −2^63
#guard fpIs (fp1 (.truncWS 2#32 4#32) [(4, 0xcf000000#32)]) 2 0x80000000#32 0#32            -- −2^31
-- the double forms read the pair ($f4 = low, $f5 = high): 2.5 = 0x4004000000000000
#guard fpIs (fp1 (.roundWD 2#32 4#32) [(4, 0#32), (5, 0x40040000#32)]) 2 2#32 0x00001004#32
#guard fpIs (fp1 (.ceilWD 2#32 4#32) [(4, 0#32), (5, 0x40040000#32)]) 2 3#32 0x00001004#32
#guard fpIs (fp1 (.floorWD 2#32 4#32) [(4, 0#32), (5, 0xc0040000#32)]) 2 0xfffffffd#32 0x00001004#32
#guard fpIs (fp1 (.truncWD 2#32 4#32) [(4, 0#32), (5, 0xc0040000#32)]) 2 0xfffffffe#32 0x00001004#32
#guard fpIs (fp1 (.cvtWD 2#32 4#32) [(4, 0#32), (5, 0x40040000#32)] 2#32) 2 3#32 0x00001006#32
#guard fpIs (fp1 (.cvtWD 2#32 4#32) [(4, 0#32), (5, 0x7ff00000#32)]) 2 0x7fffffff#32 0x00010040#32
-- cvt.s.w: 5 → 5.0; 2^24+1 is inexact (RN down, RP up)
#guard fpIs (fp1 (.cvtSW 2#32 4#32) [(4, 5#32)]) 2 0x40a00000#32 0#32
#guard fpIs (fp1 (.cvtSW 2#32 4#32) [(4, 16777217#32)]) 2 0x4b800000#32 0x00001004#32
#guard fpIs (fp1 (.cvtSW 2#32 4#32) [(4, 16777217#32)] 2#32) 2 0x4b800001#32 0x00001006#32
-- cvt.d.w −1 → −1.0 = 0xbff0000000000000; cvt.d.s 1.0; cvt.s.d of 1+2^−24 (a tie)
#guard (match fp1 (.cvtDW 2#32 4#32) [(4, 0xffffffff#32)] with
        | .next s => readFpD s 2#32 == 0xbff0000000000000#64 && s.fcsr == 0#32
        | .halt _ => false)
#guard (match fp1 (.cvtDS 2#32 4#32) [(4, 0x3f800000#32)] with
        | .next s => readFpD s 2#32 == 0x3ff0000000000000#64 && s.fcsr == 0#32
        | .halt _ => false)
#guard fpIs (fp1 (.cvtSD 2#32 4#32) [(4, 0x10000000#32), (5, 0x3ff00000#32)]) 2 0x3f800000#32
  0x00001004#32
#guard fpIs (fp1 (.cvtSD 2#32 4#32) [(4, 0x10000000#32), (5, 0x3ff00000#32)] 2#32) 2 0x3f800001#32
  0x00001006#32

-- #### Double-precision arithmetic (pairs: low word in $fN, high word in $fN+1)
-- 1.0 + 2.0 = 3.0 (0x4008000000000000)
#guard (match fp1 (.addD 2#32 4#32 6#32) [(5, 0x3ff00000#32), (7, 0x40000000#32)] with
        | .next s => readFpD s 2#32 == 0x4008000000000000#64 && s.fcsr == 0#32
        | .halt _ => false)
-- 1.0 / 3.0 = 0x3fd5555555555555, Inexact
#guard (match fp1 (.divD 2#32 4#32 6#32) [(5, 0x3ff00000#32), (7, 0x40080000#32)] with
        | .next s => readFpD s 2#32 == 0x3fd5555555555555#64 && s.fcsr == 0x00001004#32
        | .halt _ => false)
-- sqrt.d(2) = 0x3ff6a09e667f3bcd; sqrt.d(−1) → default QNaN 0x7ff7ffffffffffff, Invalid
#guard (match fp1 (.sqrtD 2#32 4#32) [(5, 0x40000000#32)] with
        | .next s => readFpD s 2#32 == 0x3ff6a09e667f3bcd#64 && s.fcsr == 0x00001004#32
        | .halt _ => false)
#guard (match fp1 (.sqrtD 2#32 4#32) [(5, 0xbff00000#32)] with
        | .next s => readFpD s 2#32 == 0x7ff7ffffffffffff#64 && s.fcsr == 0x00010040#32
        | .halt _ => false)
-- mov.d / neg.d / abs.d
#guard (match fp1 (.movD 2#32 4#32) [(4, 0x89abcdef#32), (5, 0x7ff80000#32)] 0x7c#32 with
        | .next s => readFpD s 2#32 == 0x7ff8000089abcdef#64 && s.fcsr == 0x7c#32
        | .halt _ => false)
#guard (match fp1 (.negD 2#32 4#32) [(4, 1#32), (5, 0x3ff00000#32)] with
        | .next s => readFpD s 2#32 == 0xbff0000000000001#64 && s.fcsr == 0#32
        | .halt _ => false)
#guard (match fp1 (.absD 2#32 4#32) [(4, 1#32), (5, 0xbff00000#32)] with
        | .next s => readFpD s 2#32 == 0x3ff0000000000001#64
        | .halt _ => false)
-- madd.d: 2 × 3 + 1 = 7 (0x401c000000000000)
#guard (match fp1 (.maddD 2#32 8#32 4#32 6#32)
          [(5, 0x40000000#32), (7, 0x40080000#32), (9, 0x3ff00000#32)] with
        | .next s => readFpD s 2#32 == 0x401c000000000000#64 && s.fcsr == 0#32
        | .halt _ => false)

-- #### Compare, condition codes, FP branches, conditional moves
-- c.eq.s $fcc0: 1.0 = 1.0 sets FCC0 (bit 23); c.lt.s $fcc7: 1.0 < 2.0 sets FCC7 (bit 31)
#guard nextFcsrEq (fp1 (.cCondS 2#32 0#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x3f800000#32)])
  0x00800000#32
#guard nextFcsrEq (fp1 (.cCondS 12#32 7#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40000000#32)])
  0x80000000#32
-- a false compare clears exactly its own condition code (here FCC1 = bit 25)
#guard nextFcsrEq (fp1 (.cCondS 2#32 1#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40000000#32)]
  0xfe800000#32) 0xfc800000#32
-- −0 = +0
#guard nextFcsrEq (fp1 (.cCondS 2#32 0#32 4#32 6#32) [(4, 0x80000000#32), (6, 0#32)]) 0x00800000#32
-- quiet predicates on a QNaN: no exception; c.un true, c.eq false, c.ueq true
#guard nextFcsrEq (fp1 (.cCondS 1#32 0#32 4#32 6#32) [(4, 0x7fbfffff#32), (6, 0x3f800000#32)])
  0x00800000#32
#guard nextFcsrEq (fp1 (.cCondS 2#32 0#32 4#32 6#32) [(4, 0x7fbfffff#32), (6, 0x3f800000#32)]) 0#32
#guard nextFcsrEq (fp1 (.cCondS 3#32 0#32 4#32 6#32) [(4, 0x7fbfffff#32), (6, 0x3f800000#32)])
  0x00800000#32
-- signaling predicates on a QNaN: Invalid (c.seq false; c.ngle true; c.sf false)
#guard nextFcsrEq (fp1 (.cCondS 10#32 0#32 4#32 6#32) [(4, 0x7fbfffff#32), (6, 0x3f800000#32)])
  0x00010040#32
#guard nextFcsrEq (fp1 (.cCondS 9#32 0#32 4#32 6#32) [(4, 0x7fbfffff#32), (6, 0x3f800000#32)])
  0x00810040#32
#guard nextFcsrEq (fp1 (.cCondS 8#32 2#32 4#32 6#32) [(4, 0x7fbfffff#32), (6, 0x3f800000#32)])
  0x00010040#32
-- c.ngt.s (15): true on less, equal, unordered
#guard nextFcsrEq (fp1 (.cCondS 15#32 0#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x3f800000#32)])
  0x00800000#32
#guard nextFcsrEq (fp1 (.cCondS 15#32 0#32 4#32 6#32) [(4, 0x40000000#32), (6, 0x3f800000#32)]) 0#32
-- an SNaN signals Invalid even for a quiet predicate
#guard nextFcsrEq (fp1 (.cCondS 2#32 0#32 4#32 6#32) [(4, 0x7fc00000#32), (6, 0x3f800000#32)])
  0x00010040#32
-- with Invalid enabled (bit 11) the compare traps and FCC is not written
#guard fpTraps (fp1 (.cCondS 9#32 0#32 4#32 6#32) [(4, 0x7fbfffff#32), (6, 0x3f800000#32)]
  0x00000800#32) 4 0x7fbfffff#32 0x00010800#32
-- c.cond.d: 1.0 < 2.0 on pairs, into FCC3 (bit 27)
#guard nextFcsrEq (fp1 (.cCondD 12#32 3#32 4#32 6#32) [(5, 0x3ff00000#32), (7, 0x40000000#32)])
  0x08000000#32

-- bc1t/bc1f test the selected condition code; ordinary delay slot
#guard nextPendingEq (step (prog1 (.bc1t 0#32 4#32)) { regs0 with fcsr := 0x00800000#32 })
  (some (textBase + 4#32 + 16#32))
#guard nextPendingEq (step (prog1 (.bc1t 0#32 4#32)) regs0) (some (textBase + 8#32))
#guard nextPendingEq (step (prog1 (.bc1f 0#32 4#32)) regs0) (some (textBase + 4#32 + 16#32))
#guard nextPendingEq (step (prog1 (.bc1t 7#32 4#32)) { regs0 with fcsr := 0x80000000#32 })
  (some (textBase + 4#32 + 16#32))
#guard nextPendingEq (step (prog1 (.bc1t 7#32 4#32)) { regs0 with fcsr := 0x7e800000#32 })
  (some (textBase + 8#32))
-- bc1tl/bc1fl: taken → as bc1t; not taken → delay slot nullified (pc + 8, nothing pending)
#guard nextPendingEq (step (prog1 (.bc1tl 0#32 4#32)) { regs0 with fcsr := 0x00800000#32 })
  (some (textBase + 4#32 + 16#32))
#guard (match step (prog1 (.bc1tl 0#32 4#32)) regs0 with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch.isNone
        | .halt _ => false)
#guard (match step (prog1 (.bc1fl 1#32 4#32)) { regs0 with fcsr := 0x02000000#32 } with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch.isNone
        | .halt _ => false)
#guard nextPendingEq (step (prog1 (.bc1fl 1#32 4#32)) regs0) (some (textBase + 4#32 + 16#32))
-- an FP branch in a delay slot halts like any other branch
#guard isHaltBranchInDelaySlot
  (step (prog1 (.bc1tl 0#32 4#32)) { regs0 with pendingBranch := some textBase })

-- movf/movt (GPR) and movf.s/movt.s/movn.s/movz.s
#guard nextRegEq (step (prog1 (.movf 8#32 0#32 9#32)) (setRegs regs0 [(8, 0x55#32), (9, 0x11#32)])) 9
  0x55#32
#guard nextRegEq (step (prog1 (.movt 8#32 0#32 9#32)) (setRegs regs0 [(8, 0x55#32), (9, 0x11#32)])) 9
  0x11#32
#guard nextRegEq (step (prog1 (.movt 8#32 5#32 9#32))
  { (setRegs regs0 [(8, 0x55#32), (9, 0x11#32)]) with fcsr := 0x20000000#32 }) 9 0x55#32
#guard fpIs (fp1 (.movfS 2#32 4#32 0#32) [(2, 0x11#32), (4, 0x7fc00000#32)]) 2 0x7fc00000#32 0#32
#guard fpIs (fp1 (.movtS 2#32 4#32 0#32) [(2, 0x11#32), (4, 0x7fc00000#32)]) 2 0x11#32 0#32
#guard fpIs (fp1 (.movnS 2#32 4#32 8#32) [(2, 0x11#32), (4, 0x22#32)] 0#32 [(8, 1#32)]) 2 0x22#32 0#32
#guard fpIs (fp1 (.movzS 2#32 4#32 8#32) [(2, 0x11#32), (4, 0x22#32)] 0#32 [(8, 1#32)]) 2 0x11#32 0#32
#guard (match fp1 (.movtD 2#32 4#32 1#32) [(4, 0x22#32), (5, 0x33#32)] 0x02000000#32 with
        | .next s => readFpD s 2#32 == 0x0000003300000022#64 && s.fcsr == 0x02000000#32
        | .halt _ => false)
#guard (match fp1 (.movzD 2#32 4#32 0#32) [(4, 0x22#32), (5, 0x33#32)] with
        | .next s => readFpD s 2#32 == 0x0000003300000022#64
        | .halt _ => false)

-- #### Control registers: cfc1 / ctc1
-- FIR (0) is a constant; FCSR (31) round-trips its non-reserved bits
#guard nextRegEq (fp1 (.cfc1 9#32 0#32) []) 9 0x00130000#32
#guard fpTraps (fp1 (.ctc1 8#32 31#32) [] 0#32 [(8, 0xffffffff#32)]) 0 0#32 0xff83ffff#32
#guard nextFcsrEq (fp1 (.ctc1 8#32 31#32) [] 0#32 [(8, 0x00800003#32)]) 0x00800003#32
#guard nextRegEq (fp1 (.cfc1 9#32 31#32) [] 0x00800003#32) 9 0x00800003#32
-- views after `ctc1 0x00800003 → $31`: FCCR (25) = 1 (FCC0), FENR (28) = 3 (RM), FEXR (26) = 0
#guard nextRegEq (fp1 (.cfc1 9#32 25#32) [] 0x00800003#32) 9 1#32
#guard nextRegEq (fp1 (.cfc1 9#32 28#32) [] 0x00800003#32) 9 3#32
#guard nextRegEq (fp1 (.cfc1 9#32 26#32) [] 0x00800003#32) 9 0#32
-- FCCR write sets all eight condition codes and nothing else
#guard nextFcsrEq (fp1 (.ctc1 8#32 25#32) [] 0x00000f83#32 [(8, 0xff#32)]) 0xfe800f83#32
-- FENR write: Enables, FS (bit 2 → FCSR bit 24), RM
#guard nextFcsrEq (fp1 (.ctc1 8#32 28#32) [] 0#32 [(8, 0x00000f87#32)]) 0x01000f83#32
-- FEXR write: Cause and Flags
#guard nextFcsrEq (fp1 (.ctc1 8#32 26#32) [] 3#32 [(8, 0x0001f07c#32)]) 0x0001f07f#32
-- CheckFPException: writing a Cause bit whose Enable is set traps, register written first
#guard fpTraps (fp1 (.ctc1 8#32 26#32) [] 0x00000080#32 [(8, 0x00001000#32)]) 0 0#32 0x00001080#32
-- … and so does Cause.E (bit 17), which has no enable
#guard fpTraps (fp1 (.ctc1 8#32 31#32) [] 0#32 [(8, 0x00020000#32)]) 0 0#32 0x00020000#32
-- FIR is read-only; a nonexistent control register reads 0 / ignores writes (pin)
#guard nextFcsrEq (fp1 (.ctc1 8#32 0#32) [] 0x7c#32 [(8, 0xffffffff#32)]) 0x7c#32
#guard nextRegEq (fp1 (.cfc1 9#32 7#32) [] 0x7c#32 [(9, 0x55#32)]) 9 0#32
#guard nextFcsrEq (fp1 (.ctc1 8#32 7#32) [] 0x7c#32 [(8, 0xffffffff#32)]) 0x7c#32

-- #### Floating Point exception (enabled exception): destination not written
-- Inexact enabled (bit 7): 1/3 traps; $f2 keeps 0xdead; Cause.I set, Flags untouched
#guard fpTraps (fp1 (.divS 2#32 4#32 6#32)
  [(2, 0xdead#32), (4, 0x3f800000#32), (6, 0x40400000#32)] 0x00000080#32) 2 0xdead#32 0x00001080#32
-- Divide-by-zero enabled (bit 10)
#guard fpTraps (fp1 (.divS 2#32 4#32 6#32)
  [(2, 0xdead#32), (4, 0x3f800000#32), (6, 0#32)] 0x00000400#32) 2 0xdead#32 0x00008400#32
-- Invalid enabled (bit 11): cvt.w.s of a NaN, abs.s of a NaN
#guard fpTraps (fp1 (.cvtWS 2#32 4#32) [(2, 0xdead#32), (4, 0x7fbfffff#32)] 0x00000800#32) 2
  0xdead#32 0x00010800#32
#guard fpTraps (fp1 (.absS 2#32 4#32) [(2, 0xdead#32), (4, 0x7fbfffff#32)] 0x00000800#32) 2
  0xdead#32 0x00010800#32
-- Underflow enabled (bit 8): an exact tiny result (2^−126 × 0.5) traps
#guard fpTraps (fp1 (.mulS 2#32 4#32 6#32)
  [(2, 0xdead#32), (4, 0x00800000#32), (6, 0x3f000000#32)] 0x00000100#32) 2 0xdead#32 0x00002100#32
#guard fpIs (fp1 (.mulS 2#32 4#32 6#32) [(4, 0x00800000#32), (6, 0x3f000000#32)]) 2 0x00400000#32 0#32
-- a double result is not written either
#guard (match fp1 (.divD 2#32 4#32 6#32)
          [(2, 0xdead#32), (3, 0xbeef#32), (5, 0x3ff00000#32), (7, 0x40080000#32)] 0x00000080#32 with
        | .next s => readFpD s 2#32 == 0x0000beef0000dead#64 && causeExcCode s == excCodeFPE &&
            s.fcsr == 0x00001080#32 && s.cp0Epc == textBase
        | .halt _ => false)
-- FS = 1 (bit 24): a tiny result is flushed to zero with Underflow | Inexact
#guard fpIs (fp1 (.mulS 2#32 4#32 6#32) [(4, 0x00800000#32), (6, 0x3f000000#32)] 0x01000000#32) 2
  0#32 0x0100300c#32

-- #### Coprocessor Unusable: Status.CU1 = 0
private def noCu1 (s : State) : State := { s with cp0Status := 0#32 }

/-- `r` is a Coprocessor Unusable entry with `Cause.CE = ce`, and the FP
registers and FCSR are those of `s`. -/
private def cpuRaised (r : StepResult) (s : State) (ce : W32) : Bool :=
  raises r excCodeCpU &&
    (match r with
     | .next s' => (s'.cp0Cause &&& causeCeMask) == ce <<< 28 && s'.fpRegs == s.fpRegs &&
         s'.fcsr == s.fcsr && s'.regs == s.regs && s'.cp0Epc == s.pc
     | .halt _ => false)

private def cuState : State :=
  noCu1 { (setFpRegs (setRegs regs0 [(8, 0x10010000#32), (9, 0x77#32)])
      [(2, 0x11#32), (4, 0x3f800000#32), (6, 0x40000000#32)]) with fcsr := 0x00800003#32 }

#guard [Instruction.addS 2#32 4#32 6#32, .addD 2#32 4#32 6#32, .mfc1 9#32 4#32, .mtc1 9#32 4#32,
    .mfhc1 9#32 4#32, .mthc1 9#32 4#32, .cfc1 9#32 31#32, .ctc1 9#32 31#32,
    .lwc1 8#32 2#32 0#32, .swc1 8#32 2#32 0#32, .ldc1 8#32 2#32 0#32, .sdc1 8#32 2#32 0#32,
    .lwxc1 2#32 0#32 8#32, .sdxc1 2#32 0#32 8#32, .prefx 0#32 0#32 8#32,
    .movS 2#32 4#32, .absD 2#32 4#32, .cvtWS 2#32 4#32, .cvtDW 2#32 4#32, .sqrtS 2#32 4#32,
    .cCondS 2#32 0#32 4#32 6#32, .cCondD 2#32 0#32 4#32 6#32,
    .movfS 2#32 4#32 0#32, .movnD 2#32 4#32 9#32, .movf 9#32 0#32 10#32, .movt 9#32 0#32 10#32,
    .maddS 2#32 2#32 4#32 6#32, .nmsubD 2#32 2#32 4#32 6#32, .recipS 2#32 4#32, .rsqrtD 2#32 4#32,
    .roundWD 2#32 4#32, .bc1f 0#32 4#32, .bc1t 0#32 4#32, .bc1fl 0#32 4#32, .bc1tl 0#32 4#32].all
  fun i => cpuRaised (step (prog1 i) cuState) cuState 1#32
-- … and none of them raises it when CU1 = 1
#guard !(raises (step (prog1 (.addS 2#32 4#32 6#32)) { cuState with cp0Status := statusCu1Mask })
  excCodeCpU)
-- integer instructions and `pref` are unaffected by CU1
#guard isNext (step (prog1 (.addu 8#32 9#32 10#32)) cuState)
#guard isNext (step (prog1 (.pref 8#32 0#32 0#32)) cuState)
-- a reserved COP1 encoding: Coprocessor Unusable when CU1 = 0, Reserved Instruction when 1
#guard cpuRaised (step ((∅ : Program).insert textBase 0x47e00000#32) cuState) cuState 1#32
#guard raises (step ((∅ : Program).insert textBase 0x47e00000#32) regs0) excCodeRI
-- reserved COP1X (luxc1) and MOVCI (bit 17 set) words likewise
#guard cpuRaised (step ((∅ : Program).insert textBase 0x4c000005#32) cuState) cuState 1#32
#guard cpuRaised (step ((∅ : Program).insert textBase 0x00020001#32) cuState) cuState 1#32
#guard raises (step ((∅ : Program).insert textBase 0x00020001#32) regs0) excCodeRI
-- coprocessor 2 does not exist: COP2 / LWC2 words raise Coprocessor Unusable with CE = 2
#guard cpuRaised (step ((∅ : Program).insert textBase 0x48000000#32) regs0) regs0 2#32
#guard cpuRaised (step ((∅ : Program).insert textBase 0xc8000000#32) regs0) regs0 2#32
-- CpU in a delay slot: EPC = branch, BD set
#guard (match step (prog1 (.addS 2#32 4#32 6#32)) { cuState with pendingBranch := some 0x1000#32 } with
        | .next s => s.cp0Epc == textBase - 4#32 && s.cp0Cause == 0x9000002c#32
        | .halt _ => false)
-- a later exception reloads CE with 0
#guard (match step (prog1 (.break 0#32)) { regs0 with cp0Cause := 0x10000000#32 } with
        | .next s => s.cp0Cause == 0x00000024#32
        | .halt _ => false)

-- #### FP loads/stores
private def fpMemTestState : State :=
  { (setRegs regs0 [(8, 0x10010000#32), (9, 4#32)]) with
      mem := (((∅ : Std.HashMap W32 UInt8).insert 0x10010004#32 0x3f).insert 0x10010005#32 0x80)
               |>.insert 0x10010006#32 0x00 |>.insert 0x10010007#32 0x00 }  -- 1.0 at offset 4
#guard nextFpRegEq (step (prog1 (.lwc1 8#32 9#32 4#32)) fpMemTestState) 9 0x3f800000#32
#guard nextFpRegEq (step (prog1 (.lwxc1 3#32 9#32 8#32)) fpMemTestState) 3 0x3f800000#32
#guard (stepState (prog1 (.swc1 8#32 9#32 4#32))
          (setFpRegs (setRegs regs0 [(8, 0x10010000#32)]) [(9, 0x3f800000#32)])).bind
        (fun s' => readMemWord s' 0x10010004#32) = some 0x3f800000#32
#guard (stepState (prog1 (.swxc1 9#32 10#32 8#32))
          (setFpRegs (setRegs regs0 [(8, 0x10010000#32), (10, 8#32)]) [(9, 0x3f800000#32)])).bind
        (fun s' => readMemWord s' 0x10010008#32) = some 0x3f800000#32
#guard raisesAddr (step (prog1 (.lwc1 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)]))
  excCodeAdEL 0x10010001#32
#guard raisesAddr (step (prog1 (.swxc1 9#32 10#32 8#32))
  (setRegs regs0 [(8, 0x10010000#32), (10, 2#32)])) excCodeAdES 0x10010002#32

-- ldc1/sdc1: big-endian doubleword (high word at the lower address), doubleword-aligned
private def dpMemTestState : State :=
  { (setRegs regs0 [(8, 0x10010000#32), (9, 8#32)]) with
      mem := ((((∅ : Std.HashMap W32 UInt8).insert 0x10010008#32 0x3f).insert 0x10010009#32 0xf0)
               |>.insert 0x1001000f#32 0x01) }  -- 0x3ff0000000000001 at offset 8
#guard (match step (prog1 (.ldc1 8#32 2#32 8#32)) dpMemTestState with
        | .next s => readFpD s 2#32 == 0x3ff0000000000001#64 && readFpReg s 3 == 0x3ff00000#32
        | .halt _ => false)
#guard (match step (prog1 (.ldxc1 2#32 9#32 8#32)) dpMemTestState with
        | .next s => readFpD s 2#32 == 0x3ff0000000000001#64
        | .halt _ => false)
#guard (stepState (prog1 (.sdc1 8#32 2#32 16#32))
          (setFpRegs (setRegs regs0 [(8, 0x10010000#32)]) [(2, 0x89abcdef#32), (3, 0x01234567#32)])).bind
        (fun s' => (readMemWord s' 0x10010010#32).bind fun hi =>
          (readMemWord s' 0x10010014#32).map fun lo => (hi, lo))
      = some (0x01234567#32, 0x89abcdef#32)
#guard (stepState (prog1 (.sdxc1 2#32 9#32 8#32))
          (setFpRegs (setRegs regs0 [(8, 0x10010000#32), (9, 16#32)])
            [(2, 0x89abcdef#32), (3, 0x01234567#32)])).bind
        (fun s' => readMemWord s' 0x10010010#32) = some 0x01234567#32
-- word-aligned but not doubleword-aligned: Address Error
#guard raisesAddr (step (prog1 (.ldc1 8#32 2#32 4#32)) dpMemTestState) excCodeAdEL 0x10010004#32
#guard raisesAddr (step (prog1 (.sdc1 8#32 2#32 4#32)) dpMemTestState) excCodeAdES 0x10010004#32
#guard raisesAddr (step (prog1 (.ldxc1 2#32 9#32 8#32))
  (setRegs regs0 [(8, 0x10010000#32), (9, 12#32)])) excCodeAdEL 0x1001000c#32
#guard raisesAddr (step (prog1 (.sdxc1 2#32 9#32 8#32))
  (setRegs regs0 [(8, 0x10010000#32), (9, 12#32)])) excCodeAdES 0x1001000c#32
-- a store clears LLbit; a failed (misaligned) one does not get that far
#guard nextLlBitEq (step (prog1 (.sdc1 8#32 2#32 8#32)) { dpMemTestState with llBit := true }) false

-- ### CP0 additions: PRId / Config / Config1 / EBase, di / ei, Cause.DC
#guard nextRegEq (step (prog1 (.mfc0 9#32 15#32 0#32)) regs0) 9 0x00010000#32
#guard nextRegEq (step (prog1 (.mfc0 9#32 16#32 0#32)) regs0) 9 0x80008402#32
#guard nextRegEq (step (prog1 (.mfc0 9#32 16#32 1#32)) regs0) 9 0x00000001#32
#guard nextRegEq (step (prog1 (.mfc0 9#32 15#32 1#32)) regs0) 9 0x80000000#32
-- the read-only registers ignore writes
#guard (match step (prog1 (.mtc0 9#32 16#32 0#32)) (setRegs regs0 [(9, 0xffffffff#32)]) with
        | .next s => nextRegEq (step (prog1 (.mfc0 10#32 16#32 0#32)) { s with pc := textBase }) 10
            0x80008402#32
        | .halt _ => false)
-- EBase: only bits 29..12 are writable; bits 31..30 stay `10`
#guard (match step (prog1 (.mtc0 9#32 15#32 1#32)) (setRegs regs0 [(9, 0xffffffff#32)]) with
        | .next s => s.cp0EBase == 0xbffff000#32 && exceptionVector s == 0xbffff180#32
        | .halt _ => false)
#guard (match step (prog1 (.mtc0 9#32 15#32 1#32)) (setRegs regs0 [(9, 0x00012345#32)]) with
        | .next s => s.cp0EBase == 0x80012000#32
        | .halt _ => false)
-- exceptions vector through EBase when BEV = 0, and through 0xBFC00380 when BEV = 1
#guard (match step (prog1 (.break 0#32)) { regs0 with cp0EBase := 0x80012000#32 } with
        | .next s => s.pc == 0x80012180#32
        | .halt _ => false)
#guard (match step (prog1 (.break 0#32))
          { regs0 with cp0EBase := 0x80012000#32, cp0Status := statusBevMask } with
        | .next s => s.pc == 0xbfc00380#32
        | .halt _ => false)
-- di / ei: $rt receives the old Status; IE is cleared / set
#guard (match step (prog1 (.di 9#32)) { regs0 with cp0Status := 0x2000ff01#32 } with
        | .next s => readReg s 9 == 0x2000ff01#32 && s.cp0Status == 0x2000ff00#32
        | .halt _ => false)
#guard (match step (prog1 (.ei 9#32)) regs0 with
        | .next s => readReg s 9 == 0x20000000#32 && s.cp0Status == 0x20000001#32
        | .halt _ => false)
#guard (match step (prog1 (.ei 0#32)) regs0 with
        | .next s => readReg s 0 == 0#32 && s.cp0Status == 0x20000001#32
        | .halt _ => false)
-- Cause.DC (bit 27) is writable, WP (22) is not
#guard (match step (prog1 (.mtc0 9#32 13#32 0#32)) (setRegs regs0 [(9, 0xffffffff#32)]) with
        | .next s => s.cp0Cause == 0x08800300#32
        | .halt _ => false)

-- ### sc compares its address with the preceding ll's
#guard (match stepState (prog1 (.ll 8#32 9#32 0#32)) (setRegs regs0 [(8, 0x10010000#32)]) with
        | some s1 => s1.llBit && s1.llAddr == 0x10010000#32 &&
            (match step (prog1 (.sc 8#32 10#32 4#32))
                (setRegs { s1 with pc := textBase } [(10, 0xdeadbeef#32)]) with
             | .next s2 => readReg s2 10 == 0#32 && !s2.llBit &&
                 readMemWord s2 0x10010004#32 == some 0#32
             | .halt _ => false)
        | none => false)

-- ### `run`: a short program that computes something and exits

-- addi $t0,$zero,5 ; addi $t1,$zero,7 ; add $t2,$t0,$t1 ; add $a0,$t2,$zero ;
-- addi $v0,$zero,1 ; syscall (print 12) ; addi $v0,$zero,10 ; syscall (exit)
private def sumProg : Program :=
  buildProg textBase
    [ .addi 0#32 8#32 5#32
    , .addi 0#32 9#32 7#32
    , .add  8#32 9#32 10#32
    , .add  10#32 0#32 4#32
    , .addi 0#32 2#32 1#32
    , (.syscall 0#32)
    , .addi 0#32 2#32 10#32
    , (.syscall 0#32) ]

#guard (match run sumProg regs0 20 with
        | .halted .exit s steps => s.out == "12" && steps == 8
        | _ => false)

-- `limitReached`: a two-instruction infinite self-loop
-- (`beq $zero,$zero,-1` with a `nop` delay slot) — with delay slots the
-- loop body is the branch *plus* its delay-slot instruction, so each
-- iteration costs 2 steps, but it still never halts.
private def loopProg : Program := buildProg textBase [.beq 0#32 0#32 0xffff#32, nopInstr]
#guard (match run loopProg regs0 5 with
        | .limitReached _ steps => steps == 5
        | _ => false)
