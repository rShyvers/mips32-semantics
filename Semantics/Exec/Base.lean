import Std.Data.HashMap.Basic
import Semantics.Word
import Semantics.Types
import Semantics.State
import Semantics.Instruction
import Semantics.FpOps

/-!
# Exec.Base — the vocabulary of execution

The definitions every instruction family's execution (`Semantics/Exec/<Family>.lean`) and the
instruction cycle (`Step.lean`) share: register indices, the delay-slot exit (`advance`/`mkNext`),
the control-transfer test, the exception entry, the coprocessor usability checks, the FP completion
helpers, the CP0 register values, the timer, interrupts and the hardware registers of `rdhwr`. The
overview of the whole cycle is `Step.lean`'s module documentation.
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

/-- Whether `instr` is a control transfer instruction (CTI) that may not appear in a branch delay
slot: the branches and jumps with a delay slot (`beq`, `bne`, `blez`, `bgtz`, `bltz`, `bgez`, `nal`,
`bal`, `j`, `jal`, `jalr`, `jalr.hb`), `eret`, `wait` and `pause`. "CTIs include all branches and
jumps, NAL, ERET, ERETNC, DERET, WAIT, and PAUSE"; "Release 6: If a control transfer instruction
(CTI) is executed in the delay slot of a branch or jump, Release 6 implementations are required to
signal a Reserved Instruction exception" (MD00086 Vol II-A Rev 6.06, JALR, p.196; MD00082 Vol I-A
Rev 6.01 §5.3.2.1, p.62). `execInstr` raises Reserved Instruction when one of these is reached with
`s.pendingBranch = some _`, i.e. directly after any branch or jump, taken or not.
-- W3: the compact branches and jumps (and their forbidden slots); W2: ERETNC. -/
def isBranchLike (instr : Instruction) : Bool :=
  match instr with
  | .beq _ _ _ | .bne _ _ _ | .blez _ _ | .bgtz _ _ | .bltz _ _ | .bgez _ _ | .nal _ | .bal _
  | .j _ | .jal _ | .jalr _ _ | .jalrHb _ _ | .eret | .wait _ | .pause => true
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
abandoned (`pendingBranch := none`):
the handler runs sequentially from the vector, and `eret` to `EPC` re-executes the branch. `LLbit` is cleared
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

/-- The coprocessor-0 instructions of the model: `mfc0`, `mtc0`, `di`, `ei`, `eret`, `wait`,
`rdpgpr`, `wrpgpr`. Each page lists Coprocessor Unusable among its exceptions (MD00086 Vol II-A
Rev 6.06: MFC0 p.266, MTC0 p.291, DI p.164, EI p.176, ERET p.178, WAIT p.443, RDPGPR p.335,
WRPGPR p.444), which is raised when "A COP0
or Cache instruction was executed while the processor was running in a mode other than Debug
Mode or Kernel Mode, and the CU0 bit in the Status register was a zero" (MD00090 Vol III
Rev 6.02 §6.2.22, p.100). The other COP0 instructions (TLB instructions, `DERET`) and `CACHE`
are not implemented: their words do not decode and are covered by
`isCop0Word`. -/
def usesCop0 (instr : Instruction) : Bool :=
  match instr with
  | .mfc0 _ _ _ | .mtc0 _ _ _ | .di _ | .ei _ | .eret | .wait _ | .rdpgpr _ _ | .wrpgpr _ _ => true
  | _ => false

/-- Whether a word that does **not** decode belongs to coprocessor 0 or is a CACHE instruction:
opcode COP0 (0x10), or SPECIAL3 with the Release 6 CACHE function `100101` (MD00086 Vol II-A Rev
6.06, CACHE, p.114; the pre-Release 6 CACHE opcode 0x2f is "6Rm", Table A.2, p.451, and raises
Reserved Instruction). -- W2: CACHE itself. Outside Kernel Mode with `Status.CU0 = 0` such a word raises
Coprocessor Unusable (`Cause.CE = 0`) instead of Reserved Instruction: "An instruction was
executed that specifies an unimplemented COP0 opcode encoding of the function field when rs is
CO ... assuming that access to coprocessor 0 is allowed. If access to the coprocessor is not
allowed, a Coprocessor Unusable Exception occurs instead" (MD00090 Vol III Rev 6.02 §6.2.21,
p.99), and "If both exceptions occur on the same instruction, the Coprocessor Unusable Exception
takes priority over the Reserved Instruction Exception" (Table 6.6, p.83). -/
def isCop0Word (w : W32) : Bool :=
  opcodeOf w == 0x10#32 || (opcodeOf w == 0x1f#32 && functOf w == 0x25#32)

/-- Raise Coprocessor Unusable for coprocessor 0: `Cause.ExcCode = CpU` (11),
`Cause.CE = 0` ("unit number of the coprocessor being referenced", MD00090 Vol III
Rev 6.02 §6.2.22, p.100). -/
def takeCop0Unusable (s : State) : State :=
  exceptionEntry s excCodeCpU 0#32

/-- The instructions that need `Status.CU1` (MD00090 Vol III Rev 6.02 §6.2.22, p.100: "A COP1,
COP1X, LWC1, SWC1, LDC1, SDC1 or MOVCI (Special opcode function field encoding) instruction was
executed and the CU1 bit in the Status register was a zero"; Release 6 has no COP1X or MOVCI
instruction): every COP1 instruction and the four FP load/stores. -/
def usesCop1 (instr : Instruction) : Bool :=
  match instr with
  | .mfc1 _ _ | .mtc1 _ _ | .mfhc1 _ _ | .mthc1 _ _ | .cfc1 _ _ | .ctc1 _ _
  | .lwc1 _ _ _ | .swc1 _ _ _ | .ldc1 _ _ _ | .sdc1 _ _ _
  | .addS _ _ _ | .subS _ _ _ | .mulS _ _ _ | .divS _ _ _
  | .sqrtS _ _ | .absS _ _ | .movS _ _ | .negS _ _ | .recipS _ _ | .rsqrtS _ _
  | .roundWS _ _ | .truncWS _ _ | .ceilWS _ _ | .floorWS _ _ | .cvtWS _ _
  | .cvtDS _ _ | .cvtSW _ _ | .cvtDW _ _
  | .addD _ _ _ | .subD _ _ _ | .mulD _ _ _ | .divD _ _ _
  | .sqrtD _ _ | .absD _ _ | .movD _ _ | .negD _ _ | .recipD _ _ | .rsqrtD _ _
  | .roundWD _ _ | .truncWD _ _ | .ceilWD _ _ | .floorWD _ _ | .cvtWD _ _ | .cvtSD _ _ => true
  | _ => false

/-- Whether a word that does **not** decode belongs to coprocessor 1's encoding space: opcode COP1
(0x11). For these, Coprocessor Unusable takes precedence over Reserved Instruction when
`Status.CU1 = 0` (MD00090 Vol III Rev 6.02 §6.2.21, p.99: "… assuming that access to the
coprocessor is allowed. If access to the coprocessor is not allowed, a Coprocessor Unusable
Exception occurs instead"). The pre-Release 6 COP1X opcode (0x13) and MOVCI function are removed
("6R", MD00086 Vol II-A Rev 6.06 Table A.2, p.451; Table A.3, p.452) and not reused, so they raise
Reserved Instruction ("6Rm and 6R instructions signal a Reserved Instruction exception when executed
by a Release 6 implementation. If the encoding has been used for a new instruction or coprocessor,
the unusable exception takes priority", Table A.1, p.451). -/
def isCop1Word (w : W32) : Bool :=
  opcodeOf w == 0x11#32

/-- Whether a word belongs to coprocessor 2's encoding space: opcode COP2 (0x12). Release 6 moved
LWC2/SWC2/LDC2/SDC2 under COP2 and reuses their old opcodes for compact branches (MD00086 Vol II-A
Rev 6.06 Table A.2, p.451: `LWC2 6Rm`, `BC 6N`, ...; Table A.20, p.458). The model has no
coprocessor 2 (`Config1.C2 = 0`) and `Status.CU2` always reads 0, so these always raise Coprocessor
Unusable with `Cause.CE = 2` (MD00090 Vol III Rev 6.02 §6.2.22, p.100). -/
def isCop2Word (w : W32) : Bool :=
  opcodeOf w == 0x12#32

/-- The arithmetic environment of the current FCSR (`RM`, `Enables`, `FS`). -/
def fpEnv (s : State) : Mips.Fp.Env := Mips.Fp.envOf s.fcsr


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

/-- Complete one FP operation as a separate instruction that produced `r.1`
with the IEEE exceptions `r.2`: `Mips.Fp.fpUpdate` (Cause ← `r.2`; trap check;
Flags |= `r.2` unless trapping), then the rest `k` on the updated state. The
FP arithmetic completions `fpFinishS`/`fpFinishD` are `fpThen` with the store
as the rest (`Refine.fpFinishS_eq`). -/
def fpThen {α : Type} (s : State) (r : α × Mips.Fp.Flags) (k : State → α → State) : State :=
  let u := Mips.Fp.fpUpdate s.fcsr r.2
  if u.2 then takeException { s with fcsr := u.1 } excCodeFPE
  else k { s with fcsr := u.1 } r.1

/-- `PRId` (CP0 register 15, select 0; MD00090 Vol III Rev 6.02 §9.40,
Table 9.57, p.221): Company ID 1 (nonzero marks a MIPS32 processor),
Company Options, Processor ID and Revision 0 — an environment constant that
names no real product. -/
def prIdValue : W32 := 0x00010000

/-- `Config.AR`, the architecture revision level of each release (MD00090 Vol III Rev 6.02 §9.45,
Table 9.64, p.234: "2 Release 6"; "Encoding 2 is new for Release 6"). -/
def configARFor : Release → W32
  | .r6 => 2#32

/-- `Config` (CP0 register 16, select 0; MD00090 Vol III Rev 6.02 §9.45,
Table 9.64, p.233-235; Appendix A.1.2, Figure A.3 / Table A.2, p.317): `M` = 1 (Config1
present), `BE` = `profile.bigEndianMem` (0, little-endian: "Indicates the endian mode in which the
processor is running", p.234), `AT` = 0 (MIPS32), `AR` = `configARFor profile.release` (2, Release
6), `MT` = 3 (Fixed Mapping MMU, "See “Fixed Mapping MMU” on page 313"), `Impl` = 0, `VI` = 0, and
the three Read/Write cacheability fields: `K23` (bits 30..28, `s.cp0ConfigK23`), `KU` (bits 27..25,
`s.cp0ConfigKU`) and `K0` (bits 2..0, `s.cp0ConfigK0`), reset `K0 = 2` (Uncached, Table 9.12
p.133; "Suggested", §6.2.5 p.90) and `K23 = KU = 2` (their reset state is "Undefined", p.233,
pinned like `K0`). So `configValue` is `0x8000_0980` plus the three fields (`0xA400_0982` after
Reset). `mtc0` stores the written bits 30..28, 27..25 and 2..0 into them unchanged (every 3-bit
value is accepted). The model has no cache, so they have no effect on anything else. The other
fields are read-only.
-- W2: "For Release 6, writes of unsupported values are ignored" (p.233, p.235). -/
def configValue (s : State) : W32 :=
  0x80000180#32 ||| (if profile.bigEndianMem then 0x8000#32 else 0#32) |||
    (configARFor profile.release <<< 10) |||
    (s.cp0ConfigK23.setWidth 32 <<< 28) ||| (s.cp0ConfigKU.setWidth 32 <<< 25) |||
    s.cp0ConfigK0.setWidth 32

/-- `Config1` (CP0 register 16, select 1; MD00090 Vol III Rev 6.02 §9.46,
Table 9.65, p.237-240): `M` = 1 and `FP` = 1 (FPU implemented), nothing else — `MMU Size - 1` = 0,
no caches (`IL` = `DL` = 0), no coprocessor 2, MDMX, performance counters, watch registers,
MIPS16e or EJTAG. `M` (bit 31): "This bit is reserved to indicate that a Config2 register is
present. ... If the Config2 register is implemented, this bit should read as a 1" (p.237); Config2
is implemented (`config2Value`). `MMU Size - 1` is "Number of entries
in the TLB minus one ... The value zero is implied by ConfigMT having a value of ‘none’" (p.237);
the manual says nothing for a Fixed Mapping MMU (`MT = 3`), which has no TLB: 0 is the only value
the field can take that claims no more than one entry (pin). -/
def config1Value : W32 := 0x80000001

/-- `Config2` (CP0 register 16, select 2; MD00090 Vol III Rev 6.02 §9.47, Table 9.66, p.241-243).
Present: "Compliance Level: Required if a level 2 or level 3 cache is implemented, or if the Config3
register is required" (p.241), and Config3 is required (`config3Value`). `M` = 1: "This bit is
reserved to indicate that a Config3 register is present. ... If the Config3 register is implemented,
this bit should read as a 1" (p.241). Every other field is 0: no secondary or tertiary cache
(`SL` = `TL` = 0, "No cache present", p.242-243); the sets-per-way and associativity fields `SS`,
`SA`, `TS`, `TA` ("Preset by hardware") describe no cache and read 0; the implementation-specific
`TU` (30..28) and `SU` (15..12), the only R/W fields, are not implemented: "If this field is not
implemented it should read as zero and be ignored on write" (p.241, p.242). So the register is
`0x8000_0000` and `mtc0` to it is ignored. -/
def config2Value : W32 := 0x80000000

/-- `Config3` (CP0 register 16, select 3; MD00090 Vol III Rev 6.02 §9.48, Table 9.67, p.245-251).
Present: "Compliance Level: Required if any optional feature described by this register is
implemented: Release 2 of the Architecture, the SmartMIPS™ ASE, or trace logic; Optional otherwise"
(p.245), and the model is Release 2 (`Config.AR = 1`). "All fields in the Config3 register are
read-only" (p.245): `mtc0` to it is ignored. Every field is 0 — no feature it describes is
implemented: `M` = 0, no Config4 ("If the Config4 register is not implemented, this bit should read
as a 0", p.245; Rev 2.50 §8.29, p.110: "With the current architectural definition, this bit should
always read as a 0"); `CMGCR`, `MSAP`, `BP`, `BI` (no BadInstr/BadInstrP registers), `SC`, `PW`,
`VZ` (p.245-246); `IPLW`, `MMAR`, `MCU` (no MCU ASE, no microMIPS), `ISAOnExc` = 0 and `ISA` = 0
("Only MIPS32 Instruction Set is implemented", p.247-248); `ULRI` = 0 (no UserLocal: `rdhwr` 29
raises Reserved Instruction, `hwrValue`), `RXI` (p.248); `DSP2P`, `DSPP`, `CTXTC`, `ITL` (p.249);
`LPA` ("For implementations prior to Release 5 of the Architecture, this bit returns zero on read"),
`VEIC`, `VInt` (no EIC or vectored interrupts: interrupt compatibility mode only, §6.1.1, p.72),
p.250; `SP` (no small pages), `CDMM`, `MT`, `SM` (no SmartMIPS), `TL` (no trace logic), p.251. -/
def config3Value : W32 := 0x00000000

/-! ## Timer (Count / Compare) -/

/-- `Count` is counting: `Cause.DC = 0` ("Disable Count register ... 0 Enable counting of Count
register; 1 Disable counting of Count register", MD00090 Vol III Rev 6.02 Table 9.52, p.210). -/
def countEnabled (s : State) : Bool := s.cp0Cause &&& causeDcMask == 0#32

/-- **The timer's part of one instruction time**, applied by `step` to the state the instruction
(or exception) produced:

* `Count` advances by one unless `Cause.DC = 1`. The manual makes the rate implementation-dependent
  ("incrementing at a constant rate, whether or not an instruction is executed, retired, or any
  forward progress is made through the pipeline. The rate at which the counter increments is
  implementation-dependent", MD00090 Vol III Rev 6.02 §9.27, p.183); the model's pin is one
  increment per `step` — every step, whether it completes an instruction or takes an exception — so
  `rdhwr` register 3 (`CCRes`, "the number of cycles between update of the register") reads 1 with
  one step counted as one cycle (`ccResValue`). `Count` wraps modulo 2^32.
* "When the value of the Count register equals the value of the Compare register, an interrupt
  request is made ... the presence of the interrupt is visible to software via the CauseTI bit"
  (§9.30, p.187): `Cause.TI` (`State.cp0TimerInt`) becomes set when the new `Count` equals
  `Compare`, and stays set until software writes `Compare` ("Writing a value to the Compare
  register, as a side effect, clears the timer interrupt", p.187; the `mtc0` arm of `execBody`). The
  comparison is made on every step, also while counting is disabled.

Only `cp0Count` and `cp0TimerInt` change. The interrupt the request may cause (Interrupt exception,
§6.2.26, p.102) is not taken here: `step` checks for it before the fetch (`interruptTaken`,
`takeInterrupt`), on the state this function produced in the previous step. -/
def timerTick (s : State) : State :=
  let c := if countEnabled s then s.cp0Count + 1#32 else s.cp0Count
  { s with cp0Count := c, cp0TimerInt := s.cp0TimerInt || c == s.cp0Compare }

/-- The hardware interrupt lines `HW5..HW0` (`State.hwInt`) in the bit positions of `Cause.IP7..IP2`
(bits 15..10; MD00090 Vol III Rev 6.02 Table 9.52, p.211). -/
def hwIntBits (s : State) : W32 := s.hwInt.setWidth 32 <<< 10

/-- **`Cause` as software reads it** (`mfc0 $rt, $13`): the stored bits (`State.cp0Cause`: BD, CE,
DC, IV, IP1..IP0, ExcCode) with the timer request added. `TI` (bit 30) is `State.cp0TimerInt`
(MD00090 Vol III Rev 6.02 Table 9.52, p.209). In interrupt compatibility mode the timer request is
also seen in an IP bit: "this field specifies the IP number to which the Timer Interrupt request is
merged" (`IntCtl.IPTI`, §9.33, Table 9.48, p.199), and Table 6.2 (§6.1.1.1, p.73) lists "Timer
Interrupt" under source HW5, "CauseIP7 and StatusIM7". **Pin:** `IPTI = 7`, so `IP7` (bit 15) is set
while `TI` is (software reads the pin in `IntCtl`, `intCtlValue`, reads `IPTI = 7`). The six hardware interrupt lines `HW5..HW0`
(`State.hwInt`) are seen in `IP7..IP2` (`hwIntBits`; Table 9.52, p.211: "IP7 Hardware interrupt 5
... IP2 Hardware interrupt 0"): `IP7` is the OR of `HW5` and the timer request. -/
def causeValue (s : State) : W32 :=
  s.cp0Cause ||| hwIntBits s ||| (if s.cp0TimerInt then causeTiMask ||| causeIp7Mask else 0#32)

/-! ## Interrupts (interrupt compatibility mode) -/

/-- **The requests for interrupt service** (MD00090 Vol III Rev 6.02 §6.1.1.1, Table 6.2, p.73,
"Request for Interrupt Service in Interrupt Compatibility Mode"): request `i` is "CauseIPi and
StatusIMi", for `i` = 7 (HW5, merged with the timer) down to 0 (SW0). As a word: `Cause` as read
(`causeValue`: the software requests `IP1..IP0`, the hardware lines and the timer in `IP7..IP2`)
masked by `Status.IM7..IM0`, bits 15..8. Interrupt compatibility mode is the only mode: Vectored
Interrupt and EIC modes are optional and absent ("This mode is optional and its presence is denoted
by the VInt bit in the Config3 register", §6.1.1, p.72; `Config3.VInt = Config3.VEIC = 0`, `config3Value`), and the mode
is compatibility whenever `IntCtl.VS = 0` (Table 6.1, p.72; `intCtlValue`). -/
def interruptRequests (s : State) : W32 := causeValue s &&& s.cp0Status &&& statusImMask

/-- **Interrupts are enabled**: `Status.IE = 1`, `Status.EXL = 0`, `Status.ERL = 0` (MD00090 Vol III
Rev 6.02 §6.1, p.72: "The IE bit in the Status register is a one", "The DM bit in the Debug register
is a zero (for processors implementing EJTAG)" — no EJTAG here, `Config1.EP = 0` — and "The EXL and
ERL bits in the Status register are both zero"). The same function as WAIT's `interrupts_enabled`
(MD00086 Vol II-A Rev 6.06, WAIT, p.443: "StatusIE && !StatusEXL && !StatusERL && !DebugDM"). -/
def interruptsEnabled (s : State) : Bool :=
  s.cp0Status &&& statusIeMask != 0#32 && s.cp0Status &&& statusExlMask == 0#32 &&
    s.cp0Status &&& statusErlMask == 0#32

/-- **An interrupt is taken** in this step: some request is made and interrupts are enabled
(MD00090 Vol III Rev 6.02 §6.1, p.72: "An interrupt is only taken when all of the following are
true: A specific request for interrupt service is made ... The IE bit ... is a one ... The EXL and
ERL bits ... are both zero"; "Logically, the request for interrupt service is ANDed with the IE bit
of the Status register. The final interrupt request is then asserted only if both the EXL and ERL
bits in the Status register are zero"). -/
def interruptTaken (s : State) : Bool := interruptsEnabled s && interruptRequests s != 0#32

/-- **The Interrupt exception's vector** (MD00090 Vol III Rev 6.02 §6.2.26, p.102: "General exception
vector (offset 0x180) if the IV bit in the Cause register is zero. Interrupt vector (offset 0x200) if
the IV bit in the Cause register is one"; §6.2.3 Operation, p.87-88: with `CauseIV = 1`, "if
(StatusBEV = 1) or (IntCtlVS = 0) then vectorOffset ← 0x200", and `IntCtl.VS` is always 0 here;
Table 6.10, p.86). `Cause.IV = 0`: the general vector `exceptionVector`. `Cause.IV = 1`: base + 0x200,
that is `EBase[31..12] ‖ 0x200` with `BEV = 0` (`0x8000_0200` at reset) and `0xBFC0_0400` with
`BEV = 1`. The base's low 12 bits are zero, so the OR is the sum the Operation computes. -/
def interruptVector (s : State) : W32 :=
  if s.cp0Cause &&& causeIvMask == 0#32 then exceptionVector s
  else if s.cp0Status &&& statusBevMask == 0#32 then ebaseValue s ||| interruptVectorOffset
  else interruptVectorBevAddr

/-- **Take the Interrupt exception** from `s`: the general exception processing with `ExcCode = Int`
(0) (MD00090 Vol III Rev 6.02 §6.2.26, p.102; §6.2.3, p.86-88), so `EPC` is the address of the
instruction at `pc`, which has **not** been executed, or of the branch before it when `pc` is a
delay slot (`Cause.BD = 1`; Table 6.11, p.87; the pending branch is abandoned and `eret` re-executes
the branch), `Status.EXL ← 1`; then `PC ← interruptVector s`. "Additional State Saved: CauseIP
indicates the interrupts that are pending" (p.102): `Cause.IP` is not latched, it is the current
requests (`causeValue`; "The current interrupt requests are visible via the IP field in the Cause
register on any read of the register", §6.1.1.1, p.73). A processor in standby restarts (`standby ←
false`, `pc` already the instruction after the `wait`: "If the pipeline restarts as the result of an
enabled interrupt, that interrupt is taken between the WAIT instruction and the following
instruction (EPC for the interrupt points at the instruction following the WAIT instruction)",
MD00086 Vol II-A Rev 6.06, WAIT, p.442). The shadow-set update of §6.2.3 (p.88: "if
(ArchitectureRevision ≥ 2) and (SRSCtlHSS ≠ 0) and (StatusBEV = 0)") does not apply: `SRSCtl.HSS = 0`
(`srsCtlValue`). -/
def takeInterrupt (s : State) : State :=
  { exceptionEntry s excCodeInt with pc := interruptVector s, standby := false }

/-- **A step in standby** without an enabled interrupt: the processor stays stopped unless a
request is pending and not masked out (`Cause.IP & Status.IM ≠ 0`, ignoring `IE`, `EXL`, `ERL`),
which restarts the pipeline: `standby ← false`, and the next step executes the instruction after the
`wait` (MD00086 Vol II-A Rev 6.06, WAIT, p.442: "It is implementation-dependent whether the pipeline
restarts when a non-enabled interrupt is requested. In this case, software must poll for the cause
of the restart"; **pin**: it restarts, the rule Release 6 makes mandatory, `interrupt_pending_and_not_
masked_out`, p.443, and the restart itself takes the step). -/
def standbyStep (s : State) : State :=
  if interruptRequests s != 0#32 then { s with standby := false } else s


/-- **This step executes the instruction at `pc`**: no interrupt is taken and the processor is
not in standby. Every per-instruction theorem about `step`
assumes it (`step_of_executesInstr`, `Specs/Interrupt.lean`). -/
def executesInstr (s : State) : Bool := !interruptTaken s && !s.standby

/-! ## Hardware registers (`rdhwr`) -/

/-- `SYNCI_Step` (`rdhwr` register 1): "Address step size to be used with the SYNCI instruction, or
zero if no caches need be synchronized" (MD00086 Vol II-A Rev 6.06, RDHWR, Table 5.4, p.332; MD00090
Vol III Rev 6.02 Table 9.40, p.176: "this value should be zero if there are no caches in the system
which must be synchronize"). The model has no caches (`Config1.IL = DL = 0`): `0`. -/
def synciStepValue : W32 := 0#32

/-- `CCRes` (`rdhwr` register 3): "Resolution of the CC register. This value denotes the number of
cycles between update of the register" (MD00086 Vol II-A Rev 6.06, RDHWR, Table 5.4, p.332). `Count`
(= `CC`) advances once per `step` (`timerTick`), and one step is the model's cycle: `1` ("CC register
increments every CPU cycle"). -/
def ccResValue : W32 := 1#32

/-- The value of hardware register `rd` (MD00086 Vol II-A Rev 6.06, RDHWR, Table 5.4 and Operation,
p.332-333), or `none` if the model does not implement it: 0 `CPUNum` = `EBase.CPUNum` (bits 9..0 of
`EBase`, which reads 0: one processor), 1 `SYNCI_Step`, 2 `CC` = `Count`, 3 `CCRes`. Not
implemented: 4 (`PerfCtr`) and 5 (`XNP`) are Release 6; 6..28 are "reserved for future architecture
use. Access results in a Reserved Instruction Exception"; 29 (`ULR`) reads UserLocal, "if it is
implemented" (the register is "Pre-Release 6: Recommended", MD00090 Vol III §9.11, p.143, and the
model has none); 30..31 are implementation-dependent, "If they are not implemented, access results in a
Reserved Instruction Exception". -/
def hwrValue (s : State) (rd : W32) : Option W32 :=
  match rd.toNat with
  | 0 => some (ebaseValue s &&& 0x3FF#32)
  | 1 => some synciStepValue
  | 2 => some s.cp0Count
  | 3 => some ccResValue
  | _ => none

/-- **`rdhwr` access to register `rd` is allowed** (MD00086 Vol II-A Rev 6.06, RDHWR, Restrictions,
p.333): "Access to the specified hardware register is enabled if Coprocessor 0 is enabled, or if the
corresponding bit is set in the HWREna register" — `cp0Usable s` (Kernel Mode or `Status.CU0 = 1`,
MD00090 Vol III §3.5.3, p.23), or bit `rd` of `HWREna`. -/
def rdhwrAllowed (s : State) (rd : W32) : Bool :=
  cp0Usable s || (s.cp0HWREna >>> rd) &&& 1#32 != 0#32
