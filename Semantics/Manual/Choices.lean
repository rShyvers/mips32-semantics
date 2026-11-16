import Semantics.Manual.Arch
import Semantics.Instruction
import Semantics.FpOps

/-!
# Manual.Choices — what one implementation fixes, and what the manual leaves open

* `Impl` holds the **implementation-dependent constants and rates** that the manual leaves to the
  implementation but that are then fixed for that implementation (the rate of `Count`, `PRId`, the
  read-only parts of `Config`, `Config1`..`Config5`, `IntCtl`, `SRSCtl`, `CCRes`, `SYNCI_Step`, the
  cacheability attributes `Config.K0`/`KU`/`K23` accept).
* `Oracle` has **one field for each place where the manual allows several outcomes** (UNPREDICTABLE,
  UNDEFINED, "may succeed or may fail", "loaded, but not defined"). The spec takes an oracle as an
  argument; the manual's relation `Manual.Step` quantifies over all of them (`docs/MANUAL-SPEC.md`).

`modelImpl` and `modelOracle` are the model's choices. Each field cites the SPEC-NOTES pin it
corresponds to. Nothing here names a definition of `Step.lean`/`State.lean`.
-/

namespace Manual

/-- An exception, as `SignalException` names it (MD00086 Vol II-A Rev 6.06 §2.2.2.5.1, p.26), with
the exception-dependent argument, and the extra state each one saves (MD00090 Vol III Rev 6.02
§6.2.9-§6.2.26). -/
inductive Exception where
  | Interrupt
  /-- Address Error on a load or an instruction fetch, with the failing address (§6.2.9, p.92-93). -/
  | AddressErrorLoad (badVAddr : W32)
  /-- Address Error on a store (§6.2.9, p.92-93). -/
  | AddressErrorStore (badVAddr : W32)
  | SystemCall
  | Breakpoint
  | ReservedInstruction
  /-- Coprocessor Unusable, with the unit number (§6.2.22, p.100: "CauseCE unit number of the
  coprocessor being referenced"). -/
  | CoprocessorUnusable (unit : Nat)
  | IntegerOverflow
  | Trap
  | FloatingPoint
  deriving Repr, DecidableEq

/-- What the processor does for one UNPREDICTABLE or UNDEFINED operation that the oracle resolves:
signal an exception, execute the instruction as if the condition did not hold, or produce some
other architectural state. The limits on that state (MD00086 Vol II-A Rev 6.06 §1.2, p.3-4) are
`Manual.UnpredictableLimits` (7D). -/
inductive Outcome where
  | signal (e : Exception)
  | proceed
  | arbitrary (a : Arch)

/-- The implementation's constants. -/
structure Impl where
  /-- The amount `Count` advances by in one instruction time while `Cause.DC = 0` (MD00090 Vol III
  Rev 6.02 §9.27, p.183: "The rate at which the counter increments is implementation-dependent"). -/
  CountIncrement : W32
  /-- `PRId` (15, 0; Vol III §9.40, Table 9.57, p.221), read-only. -/
  PRId : W32
  /-- The read-only part of `Config` (16, 0; Vol III §9.45, Table 9.64, p.233-235): every bit but
  the R/W fields `K23` (30..28), `KU` (27..25) and `K0` (2..0), which must be 0 here. -/
  ConfigFixed : W32
  /-- `Config1` (16, 1; Vol III §9.46, Table 9.65, p.237-240), read-only. -/
  Config1 : W32
  /-- `Config2` (16, 2; Vol III §9.47, Table 9.66, p.241-243): read-only here (its R/W fields `TU`,
  `SU` must be unimplemented, `Impl.WF`). -/
  Config2 : W32
  /-- `Config3` (16, 3; Vol III §9.48, Table 9.67, p.245-251): "All fields in the Config3 register
  are read-only" (p.245). -/
  Config3 : W32
  -- BEGIN R6-2
  /-- `Config4` (16, 4; Vol III §9.49, Table 9.68, p.253-258), read-only on this profile (its only
  R/W field, the FTLB page size, needs an FTLB). -/
  Config4 : W32
  /-- The read-only part of `Config5` (16, 5; Vol III §9.50, Table 9.69, p.259-264): every bit but
  the R/W `SBRI` (bit 6), which must be 0 here; the other R/W fields (`K`, `CV`, `MSAEn`, `UFE`,
  `FRE`, `UFR`) belong to features this profile does not have and are 0 (`Impl.WF`). -/
  Config5Fixed : W32
  /-- The cacheability and coherency attributes `Config.K0`, `KU`, `K23` accept: "For Release 6,
  writes of unsupported values are ignored" (Vol III Table 9.64, p.233, 235); which encodings are
  supported is implementation-dependent beyond the "Required" 2 and 3 of Table 9.12 (p.133). -/
  CCASupported : BitVec 3 → Bool
  -- END R6-2
  /-- `IntCtl` (12, 1; Vol III §9.33, Table 9.48, p.199-201), read-only here; `VS` = 0 is required
  by `Impl.WF`. -/
  IntCtl : W32
  /-- `SRSCtl` (12, 2; Vol III §9.34, Table 9.49, p.203-204), read-only here; `HSS` = `PSS` = 0 is
  required by `Impl.WF`. -/
  SRSCtl : W32
  /-- `RDHWR` register 3, `CCRes` (MD00086 Vol II-A Rev 6.06, RDHWR, Table 5.4, p.332). -/
  CCRes : W32
  /-- `RDHWR` register 1, `SYNCI_Step` (RDHWR, Table 5.4, p.332). -/
  SYNCIStep : W32
  -- 7B S2
  /-- `SYNCI` from User Mode with an effective address in kernel address space signals Address Error
  (AdEL): "An Address Error Exception (with cause code equal AdEL) may occur if the effective address
  references a portion of the kernel address space which would normally result in such an exception.
  It is implementation dependent whether such an exception does occur" (MD00086 Vol II-A Rev 6.06,
  SYNCI, p.412). -/
  SynciAddressError : Bool
  -- 7B S4 FPU
  /-- `FIR`, the FP Implementation Register (`CFC1` with `fs = 0`; MD00082 Vol I-A Rev 6.01 §6.5.1,
  Table 6.5 p.87-88), read-only and implementation-dependent. -/
  FIR : W32
  -- 7R: the reciprocal approximations (not part of the IEEE core)
  /-- `RECIP.S`: the approximation of `1.0 / fs` under the FCSR environment, with the IEEE exceptions
  it raises. "The numeric accuracy of this operation is implementation dependent. It does not meet
  the accuracy specified by the IEEE 754 Floating Point standard. The computed result differs from
  the both the exact result and the IEEE-mandated representation of the exact result by no more than
  one unit in the least-significant place (ULP). It is implementation dependent whether the result
  is affected by the current rounding mode in FCSR" (MD00086 Vol II-A Rev 6.06, RECIP.fmt, p.336).
  The 1-ULP bound against the IEEE-mandated representation is `Impl.RecipAccurate`, against the exact
  result `Impl.RecipExact` (`Manual/Accuracy.lean`). -/
  recipS : Mips.Fp.Env → W32 → W32 × Mips.Fp.Flags
  /-- `RECIP.D`, as `recipS` (RECIP.fmt, p.336). -/
  recipD : Mips.Fp.Env → BitVec 64 → BitVec 64 × Mips.Fp.Flags
  /-- `RSQRT.S`: the approximation of `1.0 / sqrt(fs)`. "The numeric accuracy of this operation is
  implementation dependent ... The computed result differs from both the exact result and the
  IEEE-mandated representation of the exact result by no more than two units in the
  least-significant place (ULP). The effect of the current FCSR rounding mode on the result is
  implementation dependent" (MD00086 Vol II-A Rev 6.06, RSQRT.fmt, p.343). The 2-ULP bound is
  `Impl.RsqrtAccurate` (`Manual/Accuracy.lean`). -/
  rsqrtS : Mips.Fp.Env → W32 → W32 × Mips.Fp.Flags
  /-- `RSQRT.D`, as `rsqrtS` (RSQRT.fmt, p.343). -/
  rsqrtD : Mips.Fp.Env → BitVec 64 → BitVec 64 × Mips.Fp.Flags

/-- One resolution of every choice the manual leaves open, as far as the transcribed operations
need it (later sub-waves add fields as they transcribe more pages). -/
structure Oracle where
  /-- A store executed between `LL` and `SC` (by this processor): "A coherent store is executed
  between an LL and SC sequence on the same processor to the block of synchronizable physical memory
  containing the word (if Config5LLB=1; else whether such a store causes the SC to fail is not
  predictable)" (MD00086 Vol II-A Rev 6.06, SC, p.347; there is no `Config5`), and for a store to
  another block "the SC may fail where it could have succeeded, i.e., success is not predictable"
  (SC, p.347-348: "A load or store executed on the processor executing the LL and SC that is not to
  the block of synchronizable physical memory containing the word"). `true`: this store makes the
  `SC` fail (`LLbit ← 0`). -/
  storeClearsLL : Arch → Bool
  /-- `Cause.CE` for an exception other than Coprocessor Unusable: "The CE field is loaded, but not
  defined, for any exception type other than a coprocessor unusable exception" (MD00090 Vol III Rev
  6.02 §6.2.3, p.87). -/
  causeCE : Arch → Exception → BitVec 2
  /-- The registers whose state after a Reset is not defined: "On a Reset Exception, only the
  following registers have defined state" (MD00090 Vol III Rev 6.02 §6.2.5, p.89). The oracle gives
  the state before the listed assignments of the Operation are made (p.89-90). -/
  resetUndefined : Arch → Arch
  -- 7B S3 control + system
  /-- `JALR` with `rs = rd`: "Register specifiers rs and rd must not be equal, because such an
  instruction does not have the same effect when re-executed. The result of executing such an
  instruction is UNPREDICTABLE" (MD00086 Vol II-A Rev 6.06, JALR, p.196). -/
  jalrRsIsRd : Arch → Instruction → Outcome
  -- BEGIN R6-3
  /-- A Release 6 compact branch-and-link with `rt = 31` (BLEZALC, BGEZALC, BGTZALC, BLTZALC,
  BEQZALC, BNEZALC): "Branch-and-link Restartability: GPR 31 must not be used for the source
  registers, because such an instruction does not have the same effect when reexecuted. The result of
  executing such an instruction is UNPREDICTABLE" (MD00086 Vol II-A Rev 6.06,
  B{LE,GE,GT,LT,EQ,NE}ZALC, Restrictions, p.78). -/
  linkSourceIs31 : Arch → Instruction → Outcome
  -- END R6-3
  -- end 7B S3
  -- 7B S4 FPU
  -- BEGIN R6-5
  /-- **The upper 32 bits of a 64-bit FPR after a 32-bit result is stored in it** (`StoreFPR(fpr,
  S/W/UNINTERPRETED_WORD, value)`): "Any FPU instruction that writes a 32-bit result (S or W format)
  to the low 32-bits of a 64-bit FPR leaves the upper bits of the FPR UNPREDICTABLE. This includes
  the 32-bit FPU 32-bit load LWC1, the data transfer instruction MTC1, as well as any instruction
  that computes a 32 bit result" (MD00082 Vol I-A Rev 6.01 §6.6.2, p.98). Arguments: the state
  before the store and the register. -/
  fprUpper : Arch → Fin 32 → W32
  -- END R6-5
  /-- `CFC1 rt, fs` with `fs` = 5 (`FRE`): "if ConfigAR ≤ 2 then temp ← UNPREDICTABLE" (MD00086 Vol
  II-A Rev 6.06, CFC1, Operation, p.130; Release 6 has `ConfigAR = 2`). Gives the value `temp`.
  Arguments: the state and `fs`. -/
  cfc1Unpredictable : Arch → W32 → W32
  /-- `CTC1 rt, fs` where the Operation says `UNPREDICTABLE`: `fs` = 5, 6 (`FRE`, `NFRE`: "if ConfigAR
  ≤ 2 then UNPREDICTABLE"), or the written value has a reserved bit set (MD00086 Vol II-A Rev 6.06,
  CTC1, Restrictions p.149, Operation p.150). Arguments: the state, `fs`, `temp ← GPR[rt]31..0`.
  `.signal e`: an exception (§1.2.1, p.3); `.arbitrary a'`: the state the write leaves (before the
  `CheckFPException()` that follows); `.proceed`: nothing is written. -/
  ctc1Unpredictable : Arch → W32 → W32 → Outcome
  -- 7B S1 integer ALU: begin
  /-- `EXT` with `lsb + msbd > 31`: "The operation is UNPREDICTABLE if lsb+msbd > 31" (EXT,
  Restrictions and Operation, p.183). The model: Reserved Instruction (as `decode` for such words). -/
  extOutOfRange : Arch → Outcome
  /-- `INS` with `lsb > msb`: "The operation is UNPREDICTABLE if lsb > msb" (INS, Restrictions,
  p.193). The model: Reserved Instruction. -/
  insLsbAboveMsb : Arch → Outcome
  -- 7B S1 integer ALU: end
  -- 7R review fixes
  /-- **A word that matches a format diagram but has an UNPREDICTABLE field value**
  (`Manual.UnpredictableEncoding`): a nonzero unnamed field ("Fields that contain zeros but are not
  named are unused fields that are required to be zero ... If such fields are set to non-zero
  values, the operation of the processor is UNPREDICTABLE", MD00086 Vol II-A Rev 6.06 §2.1.1, p.12),
  `EXT` with `lsb + msbd > 31` (p.183), `INS` with `lsb > msb` (p.193), a `JALR` hint that is
  neither 0 nor the hazard barrier (p.196).
  `UNPREDICTABLE` operations "may cause ... arbitrary exceptions" or a result (§1.2.1, p.3):
  `.signal e`; `.arbitrary a'`; `.proceed` = treat the word as matching no diagram
  (`Manual.Undecodable`). The arguments are the state and the word. -/
  unpredictableEncoding : Arch → W32 → Outcome
  /-- `EBase` written with a different Exception Base while `Status.BEV = 0`: "If the value of the
  exception base register is to be changed, this must be done with StatusBEV equal 1. The operation
  of the processor is UNDEFINED if the Exception Base field is written with a different value when
  StatusBEV is 0" (MD00090 Vol III Rev 6.02 §9.41, p.223). Arguments: the state and the data
  written. `.proceed`: the write takes effect as for `BEV = 1`. -/
  ebaseWriteBEV0 : Arch → W32 → Outcome
  /-- A load executed between `LL` and `SC` by this processor: "A load that executes on the
  processor executing the LL/SC sequence to the block of synchronizable physical memory containing
  the word, will not cause the SC to fail (if Config5LLB=1; else such a load may cause the SC to
  fail)" (MD00086 Vol II-A Rev 6.06, SC, p.347; no `Config5` here), and a load to another block
  "may fail where it could have succeeded" (p.347-348). `true`: this load makes the `SC` fail
  (`LLbit ← 0`). -/
  loadClearsLL : Arch → Bool
  /-- The QNaN that `CVT.D.S` delivers for a QNaN operand. "When a floating-point result is to be
  delivered, a QNaN operand causes an arithmetic operation to supply a QNaN result. When possible,
  this QNaN result is one of the operand QNaN values" (MD00082 Vol I-A Rev 6.01 §6.3.1.5, p.82): a
  single QNaN is not a double, so which double QNaN is delivered is not fixed by the manual. The
  value must be a double QNaN (`Manual.QNaNValid`, part of `Oracle.Valid`); no exception is signalled ("QNaN operands do not cause arithmetic
  operations to signal an exception", p.82). -/
  cvtQNaNToD : W32 → BitVec 64
  /-- The QNaN that `CVT.S.D` delivers for a QNaN operand (as `cvtQNaNToD`, §6.3.1.5, p.82). -/
  cvtQNaNToS : BitVec 64 → W32
  -- BEGIN R6-2
  /-- `BadInstr` after a synchronous exception without a valid instruction word: "When a synchronous
  exception occurs for which there is no valid instruction word (for example TLB Refill - Instruction
  Fetch), the value stored in BadInstr is UNPREDICTABLE" (MD00090 Vol III Rev 6.02 §9.25, p.179); on
  this profile, an instruction fetch that signals Address Error. -/
  badInstrNoWord : Arch → W32
  /-- `BadInstrP` after a synchronous exception outside a branch delay slot: "When a synchronous
  exception occurs and the faulting instruction is not in a branch delay slot, then the value stored
  in BadInstrP is UNPREDICTABLE" (MD00090 Vol III Rev 6.02 §9.26, p.181). -/
  badInstrP : Arch → W32
  -- END R6-2
  -- BEGIN R6-4
  /-- `DIV`/`MOD`/`DIVU`/`MODU` with a zero divisor: "If the divisor in GPR rt is zero, the result
  value is UNPREDICTABLE" (MD00086 Vol II-A Rev 6.06, DIV MOD DIVU MODU, Restrictions, p.168;
  Exceptions, p.169: "No arithmetic exceptions occur. Division by zero produces an UNPREDICTABLE
  result"). Arguments: the state, the instruction, and the dividend `s1` as the Operation reads it
  (`GPR[rs]`). Gives the value written to `GPR[rd]`. -/
  divByZero : Arch → Instruction → W32 → W32
  -- END R6-4

/-- **The implementations this profile admits.** The spec's `Arch` has the normal GPRs only, no
caches and none of the features `Config3` describes; an `Impl` describes such a processor when:

* `SRSCtl.HSS = 0` (bits 29..26): "A value of zero in this field indicates that only the normal
  GPRs are implemented" (MD00090 Vol III Rev 6.02, Table 9.49, p.203), and then `SRSCtl.PSS = 0`
  (bits 9..6): "The operation of the processor is UNDEFINED if software writes a value into this
  field that is greater than the value in the HSS field" (p.204). `SGPR[0, r]` is `GPR[r]` ("The
  normal GPRs are logically considered shadow set 0", Vol III Chapter 7, p.103).
* `IntCtl.VS = 0` (bits 9..5): "If neither EIC interrupt mode nor VI mode are implemented
  (Config3VEIC = 0 and Config3VInt = 0), this field is ignored on write and reads as zero" (Table
  9.48, p.201); `Config3.VEIC = Config3.VInt = 0` follows from the next item.
* `Config3 = 0x8C00_3000`: the profile is Release 6, so Config3 exists ("Required if any optional
  feature described by this register is implemented: Release 2 of the Architecture, ...", Vol III
  §9.48, p.245) with the fields Release 6 fixes: `M` = 1 (Config4 present, p.245), `BP` = `BI` = 1
  ("Release 6: BadInstrP/BadInstr is always implemented", p.246), `ULRI` = 1 ("Release 6: UserLocal is
  always implemented", p.248), `RXI` = 1 ("Release 6: The RIE and XIE bits are always implemented",
  p.248); every other field flags a feature the spec does not have (CM GCR space, MSA, Segment
  Control, page table walk, VZ, the MCU ASE, microMIPS (`ISA`, `ISAOnExc`, `MMAR`), DSP,
  ContextConfig, IFlowtrace, XPA, EIC and vectored interrupts, small pages, CDMM, MT, SmartMIPS, trace
  logic) and is 0. Its fields are all read-only (p.245), so `CPRWrite` ignores a write.
* `Config4 = 0x80FC_0000` (§9.49, Table 9.68, p.253-258): `M` = 1 (Config5 present), `KScrExist` =
  `0xFC` ("For Release 6, bits 2-7 are always 1 because KScratch1-6 must be implemented", select 1
  "preset to zero", select 0 zero without EJTAG, p.255), and no TLB fields (`IE`, `AE`, `VTLBSizeExt`,
  FTLB: the Fixed Mapping MMU has no TLB).
* `Config5Fixed = 0x0000_2010` (§9.50, Table 9.69, p.259-264): `XNP` = 1 (no LLX/SCX family, p.261),
  `LLB` = 1 ("In Release 6, Config5LLB is read-only 1", p.264), `DEC` = 0 (little-endian only, p.261),
  `L2C` = 0 (Config2 present), `M` = 0 (p.260); the R/W `SBRI` (bit 6) is state (`Arch.Config5SBRI`),
  and the R/W fields of absent features (`K`, `CV`, `MSAEn`, `UFE`, `FRE`, `UFR`) are 0.
* `CCASupported 2 = CCASupported 3 = true`: the two cacheability attributes Table 9.12 (Vol III p.133)
  marks "Required" are accepted.
* `Config2.M = 1` ("If the Config3 register is implemented, this bit should read as a 1", §9.47,
  Table 9.66, p.241; Config2 is "Required if ... the Config3 register is required", p.241), no level
  2 or 3 cache (`SL` = `TL` = 0, "No cache present", p.242-243), and the implementation-specific R/W
  fields `TU` (30..28), `SU` (15..12) not implemented ("it should read as zero and be ignored on
  write", p.241-242): bits 31..28, 23..20, 15..12, 7..4 are `1000`, `0`, `0`, `0`.
* `Config1.M = 1` ("If the Config2 register is implemented, this bit should read as a 1", §9.46,
  Table 9.65, p.237).
* `FIR` bits 31..28 and 23..16 are `0000` and `1111 0011` (MD00082 Vol I-A Rev 6.01 §6.5.1, Table
  6.5, p.88-89): bits 31..30 "Reserved", `FREP` = 0 (the profile has no `Config5.UFE`/`FRE`, which
  "If FREP=1" are "available"), `UFRP` "R0 (Release 6)"; `Has2008` "1 (Release 6)"; `F64` = 1 (the
  64-bit FPU: "In Release 6, StatusFR is read-only 1"); `L` = `W` = `D` = `S` = 1 ("Release 6 on a
  64-bit FPU requires S, D, W, and L data formats", Table 6.4 note 3, p.85); `3D` and `PS` "R0
  (Release 6)". `Impl`, `ProcessorID` and `Revision` are free. -/
def Impl.WF (i : Impl) : Prop :=
  i.SRSCtl.extractLsb' 26 4 = 0#4 ∧ i.SRSCtl.extractLsb' 6 4 = 0#4 ∧ i.IntCtl.extractLsb' 5 5 = 0#5 ∧
  i.Config3 = 0x8C003000#32 ∧ i.Config2 &&& 0xF0F0F0F0#32 = 0x80000000#32 ∧
  i.Config1.extractLsb' 31 1 = 1#1 ∧
  -- BEGIN R6-2
  i.Config4 = 0x80FC0000#32 ∧ i.Config5Fixed = 0x00002010#32 ∧
  i.CCASupported 2#3 = true ∧ i.CCASupported 3#3 = true ∧
  -- END R6-2
  -- BEGIN R6-5
  i.FIR &&& 0xF0FF0000#32 = 0x00F30000#32
  -- END R6-5

instance (i : Impl) : Decidable i.WF := by unfold Impl.WF; infer_instance

/-- **The distance in units in the last place** between two single-precision values: the number of
steps between them in the order of the representable values (`Mips.Fp.Format.orderKey`: adjacent
finite values of one sign differ by 1, `+0` and `-0` are both 0). -/
def ULPDistS (x y : W32) : Nat :=
  (Mips.Fp.Format.orderKey Mips.Fp.binary32 x.toNat - Mips.Fp.Format.orderKey Mips.Fp.binary32 y.toNat).natAbs

/-- `ULPDistS` for double precision. -/
def ULPDistD (x y : BitVec 64) : Nat :=
  (Mips.Fp.Format.orderKey Mips.Fp.binary64 x.toNat - Mips.Fp.Format.orderKey Mips.Fp.binary64 y.toNat).natAbs

/-- **The accuracy of `RECIP.fmt`** (MD00086 Vol II-A Rev 6.06, RECIP.fmt, p.336): "The computed
result differs from the both the exact result and the IEEE-mandated representation of the exact result
by no more than one unit in the least-significant place (ULP)." Formalized against the IEEE-mandated
representation, which is the IEEE core's correctly rounded `1.0 / fs` under the same environment
(`Mips.Fp.f32Div`/`f64Div`, shared with the model): wherever that is a finite value, the
implementation's result is finite and at most 1 ULP from it. The bound against the exact result and
the 2-ULP bound of `RSQRT.fmt` (p.343) are `Impl.RecipExact` and `Impl.RsqrtAccurate`
(`Manual/Accuracy.lean`; wave 10). -/
def Impl.RecipAccurate (i : Impl) : Prop :=
  (∀ e x, Mips.Fp.binary32.isFinite (Mips.Fp.f32Div e 0x3F800000#32 x).1.toNat = true →
    Mips.Fp.binary32.isFinite (i.recipS e x).1.toNat = true ∧
      ULPDistS (i.recipS e x).1 (Mips.Fp.f32Div e 0x3F800000#32 x).1 ≤ 1) ∧
  (∀ e x, Mips.Fp.binary64.isFinite (Mips.Fp.f64Div e 0x3FF0000000000000#64 x).1.toNat = true →
    Mips.Fp.binary64.isFinite (i.recipD e x).1.toNat = true ∧
      ULPDistD (i.recipD e x).1 (Mips.Fp.f64Div e 0x3FF0000000000000#64 x).1 ≤ 1)

/-- **The model's implementation constants** (SPEC-NOTES §9, the pins listed there): `Count` + 1 per
instruction time (`timerTick` pin); `PRId = 0x0001_0000`; `Config` read-only part `0x8000_0980`
(`M = 1`, `BE = 0` little-endian, `AT = 0`, `AR = 2` Release 6, `MT = 3`; MD00090 Vol III Rev 6.02
§9.45, Table 9.64, p.234: BE "0 Little endian", AR "2 Release 6"); `Config1 = 0x8000_0001` (`M = 1`, `FP = 1`);
`Config2 = 0x8000_0000` (`M = 1`, no L2/L3 cache); `Config3 = 0x8C00_3000`, `Config4 = 0x80FC_0000`,
`Config5` read-only part `0x0000_2010` (the Release 6 fields, `Impl.WF`); `IntCtl`
with `IPTI = 7` (`0xE000_0000`), `SRSCtl = 0`; `CCRes = 1`; `SYNCI_Step = 0`; the cacheability
attributes 2 and 3 only (the "Required" ones of Vol III Table 9.12, p.133). -/
def modelImpl : Impl where
  CountIncrement := 1#32
  PRId := 0x00010000#32
  ConfigFixed := 0x80000980#32
  Config1 := 0x80000001#32
  Config2 := 0x80000000#32
  Config3 := 0x8C003000#32
  -- BEGIN R6-2
  Config4 := 0x80FC0000#32
  Config5Fixed := 0x00002010#32
  CCASupported := fun v => v == 2#3 || v == 3#3
  -- END R6-2
  IntCtl := 0xE0000000#32
  SRSCtl := 0#32
  CCRes := 1#32
  SYNCIStep := 0#32
  SynciAddressError := false   -- 7B S2: SPEC-NOTES §11
  -- 7B S4 FPU
  FIR := 0x00F30000#32
  -- 7R: `RECIP` is `DIV.fmt` of `1.0` and `RSQRT` is `SQRT.fmt` then `DIV.fmt` (Flags ORed), under the
  -- current FCSR environment, over the IEEE core (`Mips.Fp`); SPEC-NOTES §11
  recipS := fun e x => Mips.Fp.f32Div e 0x3F800000#32 x
  recipD := fun e x => Mips.Fp.f64Div e 0x3FF0000000000000#64 x
  rsqrtS := fun e x =>
    let q := Mips.Fp.f32Sqrt e x
    let r := Mips.Fp.f32Div e 0x3F800000#32 q.1
    (r.1, q.2.or r.2)
  rsqrtD := fun e x =>
    let q := Mips.Fp.f64Sqrt e x
    let r := Mips.Fp.f64Div e 0x3FF0000000000000#64 q.1
    (r.1, q.2.or r.2)

/-- **The model's choices** (SPEC-NOTES §9): `DIV`/`DIVU` by zero give the dividend and `MOD`/`MODU`
by zero give 0 (the result of dividing by 1; R6-4, the value QEMU `mips32r6-generic` produces); every
store clears `LLbit`
(the `LLbit` pin); `Cause.CE` is loaded with 0 for every exception other than Coprocessor Unusable;
a Reset keeps every register whose reset state is undefined, except `Config.K23 = Config.KU = 2` and
`LLbit = 0` (SPEC-NOTES, Reset pins); `BadInstr` without an instruction word and `BadInstrP` outside a
delay slot are 0. -/
def modelOracle : Oracle where
  storeClearsLL := fun _ => true
  causeCE := fun _ _ => 0#2
  resetUndefined := fun a => { a with ConfigK23 := 2#3, ConfigKU := 2#3, LLbit := false }
  -- 7B S3 control + system
  jalrRsIsRd := fun _ _ => .proceed
  -- BEGIN R6-3
  -- the Operation as written: the link is written, then `GPR[rt]` (= the link) is compared
  linkSourceIs31 := fun _ _ => .proceed
  -- END R6-3
  -- end 7B S3
  -- 7B S4 FPU
  -- BEGIN R6-5: the upper half of a 32-bit FPR write is unchanged (what QEMU does)
  fprUpper := fun a fpr => (a.FPR fpr).extractLsb' 32 32
  -- END R6-5
  cfc1Unpredictable := fun _ _ => 0#32
  -- R6-5: `FRE`/`NFRE` (5, 6) signal Reserved Instruction (the exception "Release 6 implementations
  -- and later are required to produce" for these aliases, CTC1 p.149); a value with reserved bits set
  -- is written with those bits ignored (`FCSRWrite`)
  ctc1Unpredictable := fun a fs temp =>
    if fs == 25#32 then .arbitrary a
    else if fs == 26#32 then .arbitrary { a with FCSR := FCSRWrite (
      a.FCSR.extractLsb' 18 14 ++ temp.extractLsb' 12 6 ++ a.FCSR.extractLsb' 7 5 ++
        temp.extractLsb' 2 5 ++ a.FCSR.extractLsb' 0 2 : BitVec 32) }
    else if fs == 28#32 then .arbitrary { a with FCSR := FCSRWrite (
      a.FCSR.extractLsb' 25 7 ++ BitVec.ofBool (temp.getLsbD 2) ++ a.FCSR.extractLsb' 12 12 ++
        temp.extractLsb' 7 5 ++ a.FCSR.extractLsb' 2 5 ++ temp.extractLsb' 0 2 : BitVec 32) }
    else if fs == 31#32 then .arbitrary { a with FCSR := FCSRWrite temp }
    else .signal .ReservedInstruction
  -- 7B S1 integer ALU: begin (SPEC-NOTES §11 rows)
  extOutOfRange := fun _ => .signal .ReservedInstruction
  insLsbAboveMsb := fun _ => .signal .ReservedInstruction
  -- 7B S1 integer ALU: end
  -- 7R review fixes (SPEC-NOTES §11 rows)
  unpredictableEncoding := fun _ _ => .signal .ReservedInstruction
  ebaseWriteBEV0 := fun _ _ => .proceed
  loadClearsLL := fun _ => false
  cvtQNaNToD := fun x => (Mips.Fp.f32ToF64 false x).1
  cvtQNaNToS := fun x => (Mips.Fp.f64ToF32 Mips.Fp.Env.RN x).1
  -- BEGIN R6-2
  badInstrNoWord := fun _ => 0#32
  badInstrP := fun _ => 0#32
  -- END R6-2
  -- BEGIN R6-4: a zero divisor acts as a divisor of 1: the quotient is the dividend, the remainder 0
  divByZero := fun _ i s1 =>
    match i with
    | .div .. | .divu .. => s1
    | _ => 0#32
  -- END R6-4

/-- `modelImpl` is an implementation of this profile. -/
theorem modelImpl_WF : modelImpl.WF := by decide

/-- `modelImpl`'s `RECIP` is the correctly rounded `1.0 / fs`: 0 ULP from the IEEE-mandated result. -/
theorem modelImpl_recipAccurate : modelImpl.RecipAccurate :=
  ⟨fun _ _ h => ⟨h, by simp [ULPDistS, modelImpl]⟩, fun _ _ h => ⟨h, by simp [ULPDistD, modelImpl]⟩⟩

end Manual
