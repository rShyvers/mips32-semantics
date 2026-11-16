import Std.Data.HashMap.Basic
import Semantics.Word
import Semantics.Types

/-!
# State — hardware operations on `State`

Initial-state construction, register
read/write (with the `$zero`-is-write-ignored rule), the operating mode (`kernelMode`, `userMode`),
the **Fixed Mapping MMU** (`fixedMappingPA`, `translate`: virtual → physical address with the
User-Mode address check), and byte/halfword/word memory access through it (instruction fetch is a
word read, `Step.lean`'s `step`) with MIPS alignment and the byte order of `profile` (little-endian) (SPEC-NOTES
§1,§4,§7; INSTRUCTION-REF Global rules §2,§4,§5).

Depends only on the foundation (`Word`, `Types`); read-only there.
-/

/-- **Power-on values** of the state the Reset exception leaves undefined (pins). On a Reset
Exception "only the following registers have defined state" (MD00090 Vol III Rev 6.02 §6.2.5,
p.89): the GPRs, `HI`/`LO`, the FPRs, `FCSR`, `EPC`, `BadVAddr`, most of `Status` and `Cause` are
not in that list, so the architecture leaves their reset value undefined. The model pins every
one of them to 0: all GPRs (including `$sp`), `HI`, `LO`, all FPRs, `FCSR` (whose fields have reset
state "Undefined", MD00082 Vol I-A Rev 6.01 Table 6.8, p.92-95), `Status`, `Cause`, `EPC`,
`BadVAddr`, `ErrorEPC`, `LLAddr`, `Count` and `Compare` (MD00090 Vol III Rev 6.02 Table 9.44,
p.183, and Table 9.46, p.187: reset state "Undefined"), `Cause.TI` clear; `LLbit` clear, no pending
branch, empty memory (bytes read 0), and `pc = 0`. `HWREna` is 0, the value the Reset exception gives
it anyway. The hardware interrupt lines `hwInt` are deasserted (the environment connects no device,
`Semantics/Env.lean`) and the processor is not in standby. `EBase` and `Config.K0`/`K23`/`KU` hold the values the Reset exception gives them
anyway.
This is *not* the reset state: `Step.lean`'s `resetState` is `resetException powerOnState`. -/
def powerOnState : State :=
  { pc := 0#32
    regs := Array.replicate 32 (0#32)
    fpRegs := Array.replicate 32 (0#64)
    fcsr := 0#32
    physMem := ∅
    pendingBranch := none
    llBit := false
    cp0Status := 0#32
    cp0Cause := 0#32
    cp0Epc := 0#32
    cp0BadVAddr := 0#32
    cp0ErrorEpc := 0#32
    llAddr := 0#32
    cp0EBase := ebaseFixedBits
    cp0ConfigK0 := 2#3
    cp0ConfigK23 := 2#3
    cp0ConfigKU := 2#3
    cp0Count := 0#32
    cp0Compare := 0#32
    cp0TimerInt := false
    cp0HWREna := 0#32
    hwInt := 0#6
    standby := false
    -- `UserLocal`, `BadInstr`, `BadInstrP`, `KScratch1..6`: reset state "Undefined" (MD00090 Vol III
    -- Rev 6.02 Tables 9.19, 9.42, 9.43, 9.84, p.143, 179, 181, 311), pinned to 0; `Config5.SBRI`:
    -- reset state 0 (Table 9.69, p.263).
    cp0UserLocal := 0#32
    cp0BadInstr := 0#32
    cp0BadInstrP := 0#32
    cp0KScratch := fun _ => 0#32
    cp0Config5SBRI := false
    }

/-- The initial machine state at program counter `pc`: all general-purpose
registers are `0` except `$sp` (register 29), which is seeded with `spInit`;
all 32 64-bit FP registers (`fpRegs`) are `0`; memory is empty
(the loader, `Semantics/Env.lean`'s `load`, then writes the program image into it);
`llBit` is `false` (no `ll` has executed yet); `pendingBranch` is `none` (not in a delay slot).

**Environment conventions** (the state a program finds when it starts, after boot code has
run). `Env.lean` defines the hosted start state as the architectural reset state followed by an
explicit boot convention, `hostedStart = bootConvention textBase resetState`, and proves that it
equals `initialState textBase` (`Specs/Reset.lean`, `hostedStart_is_reset_then_boot`):

* `Status = 0x2000_0000`: only `CU1` set (Kernel Mode, `BEV = ERL = 0`), so programs can use
  the FPU (clear it with `mtc0` to get Coprocessor Unusable exceptions). Reset sets `BEV` and
  `ERL`; the boot convention clears them.
* `FCSR` writable fields 0: round to nearest, no exception enabled, flags and cause
  clear, `FS = 0` (`ABS2008 = NAN2008 = 1` are read-only). The manual makes every
  writable FCSR field's reset state "Undefined" (MD00082 Vol I-A Rev 6.01 Table 6.8,
  p.92-95).
* `Cause`, `EPC`, `BadVAddr`, `ErrorEPC`, `Count`, `Compare`, `HWREna` are `0` and no timer
  interrupt is pending; `EBase` holds its reset
  value `0x8000_0000` (MD00090 Vol III Rev 6.02 §9.41, p.223). -/
def initialState (pc : W32) : State :=
  { pc := pc
    regs := (Array.replicate 32 (0#32)).set! 29 spInit
    fpRegs := Array.replicate 32 (0#64)
    fcsr := 0#32
    physMem := ∅
    pendingBranch := none
    llBit := false
    cp0Status := statusCu1Mask
    cp0Cause := 0#32
    cp0Epc := 0#32
    cp0BadVAddr := 0#32
    cp0ErrorEpc := 0#32
    llAddr := 0#32
    cp0EBase := ebaseFixedBits
    cp0ConfigK0 := 2#3
    cp0ConfigK23 := 2#3
    cp0ConfigKU := 2#3
    cp0Count := 0#32
    cp0Compare := 0#32
    cp0TimerInt := false
    cp0HWREna := 0#32 }

/-- Read general-purpose register `i`. Register `0` (`$zero`) always reads as
`0` by construction of `initialState`/`writeReg`, but this also tolerates any
state built otherwise since it just indexes the register array (out-of-range
indices, which should not occur for `Fin 32`, default to `0`). -/
def readReg (s : State) (i : Fin 32) : W32 :=
  s.regs.getD i.val 0#32

/-- Write `v` into general-purpose register `i`, returning the updated state.
Per the `$zero` hardwiring rule (INSTRUCTION-REF Global rule §2), writes to
register `0` are silently ignored and the state is returned unchanged. -/
def writeReg (s : State) (i : Fin 32) (v : W32) : State :=
  if i == 0 then s else { s with regs := s.regs.set! i.val v }

/-- Read coprocessor-1 (FPU) register `i` as its whole raw 64-bit pattern (a double, a longword, or
an uninterpreted doubleword; `ValueFPR(fpr, D/L)` with `FR = 1`, MD00086 Vol II-A Rev 6.06,
Figure 2.22, p.22: "valueFPR ← FPR[fpr]"). Out-of-range indices, which should not occur for
`Fin 32`, default to `0`, matching `readReg`. -/
def readFpReg64 (s : State) (i : Fin 32) : BitVec 64 :=
  s.fpRegs.getD i.val 0#64

/-- Read coprocessor-1 (FPU) register `i` as a 32-bit pattern: its low 32 bits (a single, a word, or
an uninterpreted word; `ValueFPR(fpr, S/W)`, Figure 2.22, p.22). -/
def readFpReg (s : State) (i : Fin 32) : W32 :=
  (readFpReg64 s i).extractLsb' 0 32

/-- Write the 64-bit pattern `v` into FPU register `i` (`StoreFPR(fpr, D/L, value)` with `FR = 1`,
Figure 2.23, p.23: "FPR[fpr] ← value"). There is no hardwired-zero FP register. -/
def writeFpReg64 (s : State) (i : Fin 32) (v : BitVec 64) : State :=
  { s with fpRegs := s.fpRegs.set! i.val v }

/-- Write the 32-bit pattern `v` into the low 32 bits of FPU register `i` (`StoreFPR(fpr, S/W,
value)`, Figure 2.23, p.22-23). The upper 32 bits are UNPREDICTABLE ("Any FPU instruction that
writes a 32-bit result (S or W format) to the low 32-bits of a 64-bit FPR leaves the upper bits of
the FPR UNPREDICTABLE. This includes ... LWC1, ... MTC1, as well as any instruction that computes a 32
bit result", MD00082 Vol I-A Rev 6.01 §6.6.2, p.98); the model keeps them unchanged (pin,
`Manual.Oracle.fprUpper`; what QEMU `mips32r6-generic` does). -/
def writeFpReg (s : State) (i : Fin 32) (v : W32) : State :=
  writeFpReg64 s i ((readFpReg64 s i).extractLsb' 32 32 ++ v)

/-- `Status` as software reads it: the stored bits and the read-only `FR = 1` (`statusFrMask`). -/
def statusValue (s : State) : W32 := s.cp0Status ||| statusFrMask

/-! ## Operating mode -/

/-- **Kernel Mode** (MD00090 Vol III Rev 6.02 §3.2, p.21): "The processor is in Kernel Mode
when the DM bit in the Debug register is 0 (if the processor implements Debug Mode), and any of
the following is true: The KSU field in the CP0 Status register contains 0b00. The EXL bit in the
Status register is 1. The ERL bit in the Status register is 1." Debug Mode is not implemented
(`Config1.EP = 0`) and neither is Supervisor Mode, so `KSU` is `UM ‖ R0` with `R0` reading 0
(Table 9.47, p.195): `KSU = 0b00` iff `UM = 0`. -/
def kernelMode (s : State) : Bool :=
  s.cp0Status &&& statusUmMask == 0#32 || s.cp0Status &&& statusExlMask != 0#32 ||
    s.cp0Status &&& statusErlMask != 0#32

/-- **User Mode** (MD00090 Vol III Rev 6.02 §3.4, p.22): "The KSU field in the Status register
contains 0b10. The EXL and ERL bits in the Status register are both 0." With `KSU = UM ‖ 0`
this is `UM = 1`, `EXL = 0`, `ERL = 0`, i.e. exactly "not Kernel Mode": there is no third mode. -/
def userMode (s : State) : Bool := !kernelMode s

/-- `Status.ERL` (bit 2) is set. -/
def erlSet (s : State) : Bool := s.cp0Status &&& statusErlMask != 0#32

/-! ## The Fixed Mapping MMU

The model's MMU is the **Fixed Mapping MMU** (`Config.MT = 3`, `configValue`; MD00090 Vol III
Rev 6.02 Appendix A.1, p.313-317): no TLB, a fixed virtual → physical translation, "and no memory
protection beyond what is provided by the address error checks required of all MMUs" (A.1, p.313).
Translation happens in exactly one place, `translate`, which the six `readMem*`/`writeMem*`
functions below call; instruction fetch is `readMemWord s s.pc` (`Step.lean`). `State.physMem` is
physical memory. The loader (`Env.lean`) is not the processor: it writes `physMem` directly, at
`Env.loadAddr`.

The 32-bit virtual address space (Table 4.1, p.28; Table A.1, p.313-314), by `VA31..29`:

| VA range | segment | User Mode | Kernel Mode: physical address |
|---|---|---|---|
| `0x0000_0000`-`0x7FFF_FFFF` | useg/kuseg | legal | `VA + 0x4000_0000` if `ERL = 0`; `VA` if `ERL = 1` |
| `0x8000_0000`-`0x9FFF_FFFF` | kseg0 | Address Error | `VA - 0x8000_0000` (low 512 MB) |
| `0xA000_0000`-`0xBFFF_FFFF` | kseg1 | Address Error | `VA - 0xA000_0000` (low 512 MB) |
| `0xC000_0000`-`0xDFFF_FFFF` | kseg2 (sseg/ksseg) | Address Error | `VA` |
| `0xE000_0000`-`0xFFFF_FFFF` | kseg3 | Address Error | `VA` |

Supervisor Mode does not exist ("Supervisor Mode is not supported with a Fixed Mapping MMU",
A.1.1, p.313), so the 0xC000_0000 segment is only ever referenced from Kernel Mode (as ksseg/kseg2).
Cacheability attributes (`Config.K0`, `K23`, `KU`; A.1.2, p.316-317) select nothing: the model has
no caches (`Config1.IL = DL = 0`). No TLB exception can occur (there is no TLB, Config.MT ≠ 1). -/

/-- The **user segment** useg/kuseg, `VA31 = 0` (`0x0000_0000`-`0x7FFF_FFFF`): the only segment
"legal from" User Mode (MD00090 Vol III Rev 6.02 Table 4.1, p.28; Table 4.2, p.30). -/
def isUseg (va : VAddr) : Bool := va.toNat < 0x80000000

/-- kseg0, `0x8000_0000`-`0x9FFF_FFFF` (`VA31..29 = 0b100`, Table 4.1, p.28). -/
def isKseg0 (va : VAddr) : Bool := 0x80000000 ≤ va.toNat && va.toNat < 0xA0000000

/-- kseg1, `0xA000_0000`-`0xBFFF_FFFF` (`VA31..29 = 0b101`, Table 4.1, p.28). -/
def isKseg1 (va : VAddr) : Bool := 0xA0000000 ≤ va.toNat && va.toNat < 0xC0000000

/-- **Fixed Mapping translation** (MD00090 Vol III Rev 6.02 §A.1.1, p.313; Table A.1,
p.313-314), with `erl` = `Status.ERL`:

* "Kseg0 and Kseg1 addresses are translated in an identical manner to the TLB-based MMU: they both
  map to the low 512MB of physical memory" (kseg0 `0x8000_0000`.. and kseg1 `0xA000_0000`.. both
  generate `0x0000_0000`-`0x1FFF_FFFF`; §4.6, Table 4.3, p.30-31): `VA[28..0]`.
* "Useg/Suseg/Kuseg addresses are mapped by adding 1GB to the virtual address when the ERL bit is
  zero in the Status register, and are mapped using an identity mapping when the ERL bit is one".
* "Sseg/Ksseg/Kseg2/Kseg3 addresses are mapped using an identity mapping."

It is a total function of the address; who may use which address is `translate`'s check. -/
def fixedMappingPA (erl : Bool) (va : VAddr) : PAddr :=
  if va.toNat < 0x80000000 then (if erl then va else va + 0x40000000#32)
  else if va.toNat < 0xC0000000 then va &&& 0x1FFFFFFF#32
  else va

/-- **The address-error check of the MMU**: Kernel Mode may reference every segment, User Mode only
useg (MD00090 Vol III Rev 6.02 Table 4.2, p.30; there is no Supervisor Mode). -/
def accessAllowed (s : State) (va : VAddr) : Bool := kernelMode s || isUseg va

/-- **Address translation with the address-error check** — the one translation point of the model.
`none` means Address Error: "A reference is made to a kernel address space from User Mode"
(MD00090 Vol III Rev 6.02 §6.2.9, p.92); in User Mode every segment except useg is "Address Error"
(Table 4.2, p.30), and "address error checking is still done before the translation process.
Therefore, an attempt to reference kseg0 from User Mode still results in an address error
exception" (§A.1.1, p.313). That check is `accessAllowed`; otherwise the result is
`some (fixedMappingPA ERL va)`. Fetch, load and store are
treated alike (Table 4.2 makes no distinction; the callers raise AdEL for a fetch or load and AdES
for a store, with `BadVAddr` = `va`, §6.2.9, p.93).

Fetching from kuseg while `ERL = 1` is UNDEFINED ("The operation of the processor is UNDEFINED if
the ERL bit is set while the processor is executing instructions from kuseg", §A.1.2, p.316); the
model pins it to the data translation (identity), which neither halts nor hangs (MD00086 Vol II-A
Rev 6.06 §1.2.2, p.4). -/
def translate (s : State) (va : VAddr) : Option PAddr :=
  if accessAllowed s va then some (fixedMappingPA (erlSet s) va) else none

/-! ## Memory access

Every memory access of the processor — instruction fetch (`readMemWord s s.pc`, `Step.lean`),
loads and stores — goes through the six functions
below. Each takes a **virtual** address, checks alignment (halfword, word), translates it with
`translate` (Address Error ⇒ `none`) and reads or writes `State.physMem` at the **physical**
address. An aligned halfword or word never crosses a 512 MB segment boundary, so its bytes are at
consecutive physical addresses `pa`, `pa + 1`, …. A result `none` is an Address Error (misaligned,
or a kernel address from User Mode); the caller raises AdEL or AdES with `BadVAddr` = the virtual
address. -/

/-- Read a single byte at virtual address `addr`. Bytes that have never been written read as `0`
(a pin: what memory holds where nothing was loaded or stored is a property of the system, not of
the processor architecture; MARS and the QEMU harness also zero-fill). Byte access has no
alignment requirement; `none` only for a kernel address from User Mode. -/
def readMemByte (s : State) (addr : VAddr) : Option UInt8 :=
  match translate s addr with
  | none => none
  | some pa => some (s.physMem.get? pa |>.getD 0)

/-- Read a halfword (2 bytes) starting at virtual address `addr`, in the byte order of `profile`
(`join2`; little-endian: the byte at `addr` is the least-significant). Returns `none` if `addr` is
not halfword-aligned (a multiple of 2) or not accessible (`translate`). Unwritten bytes read as `0`. -/
def readMemHalf (s : State) (addr : VAddr) : Option W32 :=
  if addr.toNat % 2 ≠ 0 then none
  else
    match translate s addr with
    | none => none
    | some pa =>
      let b0 := s.physMem.get? pa |>.getD 0
      let b1 := s.physMem.get? (pa + 1#32) |>.getD 0
      some (join2 profile.bigEndianMem b0 b1)

/-- Read a word (4 bytes) starting at virtual address `addr`, in the byte order of `profile`
(`join4`; little-endian: the byte at `addr` is the least-significant, the byte at `addr + 3` the
most-significant). Returns `none` if `addr` is not word-aligned (a multiple of 4) or not accessible
(`translate`). Unwritten bytes read as `0`. Instruction fetch is `readMemWord s s.pc` (`Step.lean`). -/
def readMemWord (s : State) (addr : VAddr) : Option W32 :=
  if addr.toNat % 4 ≠ 0 then none
  else
    match translate s addr with
    | none => none
    | some pa =>
      let b0 := s.physMem.get? pa |>.getD 0
      let b1 := s.physMem.get? (pa + 1#32) |>.getD 0
      let b2 := s.physMem.get? (pa + 2#32) |>.getD 0
      let b3 := s.physMem.get? (pa + 3#32) |>.getD 0
      some (join4 profile.bigEndianMem b0 b1 b2 b3)

/-- Write a single byte `v` at virtual address `addr`. Byte access has no alignment
requirement; `none` only for a kernel address from User Mode (nothing is written). -/
def writeMemByte (s : State) (addr : VAddr) (v : UInt8) : Option State :=
  match translate s addr with
  | none => none
  | some pa => some { s with physMem := s.physMem.insert pa v }

/-- Write the halfword `v` (low 16 bits used) at virtual address `addr`, in the byte order of
`profile` (`byteOfValue`; little-endian: the least-significant byte goes to `addr`). Returns `none`
if `addr` is not halfword-aligned or not accessible. -/
def writeMemHalf (s : State) (addr : VAddr) (v : W32) : Option State :=
  if addr.toNat % 2 ≠ 0 then none
  else
    match translate s addr with
    | none => none
    | some pa =>
      let b0 : UInt8 := byteOfValue profile.bigEndianMem 2 v 0
      let b1 : UInt8 := byteOfValue profile.bigEndianMem 2 v 1
      some { s with physMem := (s.physMem.insert pa b0).insert (pa + 1#32) b1 }

/-- Write the word `v` at virtual address `addr`, in the byte order of `profile` (`byteOfValue`;
little-endian: the least-significant byte goes to `addr`, the most-significant to `addr + 3`).
Returns `none` if `addr` is not word-aligned or not accessible. -/
def writeMemWord (s : State) (addr : VAddr) (v : W32) : Option State :=
  if addr.toNat % 4 ≠ 0 then none
  else
    match translate s addr with
    | none => none
    | some pa =>
      let b0 : UInt8 := byteOfValue profile.bigEndianMem 4 v 0
      let b1 : UInt8 := byteOfValue profile.bigEndianMem 4 v 1
      let b2 : UInt8 := byteOfValue profile.bigEndianMem 4 v 2
      let b3 : UInt8 := byteOfValue profile.bigEndianMem 4 v 3
      some { s with
        physMem := (((s.physMem.insert pa b0).insert (pa + 1#32) b1).insert
                  (pa + 2#32) b2).insert (pa + 3#32) b3 }
