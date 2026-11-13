import Std.Data.HashMap.Basic
import Semantics.Word
import Semantics.Types

/-!
# State — hardware operations on `State`

Initial-state construction, register
read/write (with the `$zero`-is-write-ignored rule), and
byte/halfword/word memory access (instruction fetch is a word read, `Step.lean`'s `step`) with MIPS/MARS alignment and big-endian
composition rules (SPEC-NOTES §1,§4,§7; INSTRUCTION-REF Global rules §2,§4,§5).

Depends only on the foundation (`Word`, `Types`); read-only there.
-/

/-- The initial machine state at program counter `pc`: all general-purpose
registers are `0` except `$sp` (register 29), which is seeded with `spInit`;
`hi`/`lo` are `0`; all 32 FP registers (`fpRegs`) are `0`; memory is empty
(the loader, `Semantics/Env.lean`'s `load`, then writes the program image into it);
`llBit` is `false` (no `ll` has executed yet); `pendingBranch` is `none` (not in a delay slot).

**Environment conventions** (the state a program finds when it starts, as if
boot code / an operating system had set the machine up; none of these is the
architectural reset state, MD00090 Vol III Rev 6.02 §6.2.5, p.89-90; the hosted environment's
start state is `Env.lean`'s `hostedStart`):

* `Status = 0x2000_0000`: only `CU1` set, so user programs can use the FPU
  (clear it with `mtc0` to get Coprocessor Unusable exceptions). Reset would
  set `BEV` and `ERL`; the model starts as if boot code had cleared them.
* `FCSR = 0`: round to nearest, no exception enabled, flags and cause clear,
  all eight condition codes 0, `FS = 0`. The manual makes every FCSR field's
  reset state "Undefined" (MD00082 Vol I-A Rev 6.01 Table 6.8, p.92-95).
* `Cause`, `EPC`, `BadVAddr`, `ErrorEPC` are `0`; `EBase` holds its reset
  value `0x8000_0000` (MD00090 Vol III Rev 6.02 §9.41, p.223). -/
def initialState (pc : W32) : State :=
  { pc := pc
    regs := (Array.replicate 32 (0#32)).set! 29 spInit
    hi := 0#32
    lo := 0#32
    fpRegs := Array.replicate 32 (0#32)
    fcsr := 0#32
    mem := ∅
    pendingBranch := none
    llBit := false
    cp0Status := statusCu1Mask
    cp0Cause := 0#32
    cp0Epc := 0#32
    cp0BadVAddr := 0#32
    cp0ErrorEpc := 0#32
    llAddr := 0#32
    cp0EBase := ebaseFixedBits }

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

/-- Read coprocessor-1 (FPU) register `i`, as its raw 32-bit bit pattern (no
conversion to `Float32` — see `Types.lean`'s `fpRegs` docstring for the
storage convention). Out-of-range indices, which should not occur for
`Fin 32`, default to `0`, matching `readReg`. -/
def readFpReg (s : State) (i : Fin 32) : W32 :=
  s.fpRegs.getD i.val 0#32

/-- Write `v` (a raw 32-bit bit pattern) into FPU register `i`, returning the
updated state. Unlike `writeReg`, there is no hardwired-zero FP register in
MIPS32 — `$f0` is an ordinary read/write register — so this never ignores
the write. -/
def writeFpReg (s : State) (i : Fin 32) (v : W32) : State :=
  { s with fpRegs := s.fpRegs.set! i.val v }

/-! ## Memory access

Every memory access of the processor — instruction fetch (`readMemWord s s.pc`, `Step.lean`),
loads and stores, including `lwl`/`lwr`/`swl`/`swr` byte by byte — goes through the six functions
below, which index `State.mem` by the virtual address directly (no MMU: the model has no address
translation, `Config.MT = 0`, `configValue`). An address translation (e.g. the Fixed Mapping MMU)
would be inserted in these six functions and nowhere else. (The loader, `Env.lean`, writes `mem`
directly: it places the image, it is not the processor.) -/

/-- Read a single byte from memory at `addr`. Bytes that have never been
written read as `0` (a pin: what memory holds where nothing was loaded or
stored is a property of the system, not of the processor architecture; MARS
and the QEMU harness also zero-fill); byte access has no alignment requirement. -/
def readMemByte (s : State) (addr : W32) : Option UInt8 :=
  some (s.mem.get? addr |>.getD 0)

/-- Read a big-endian halfword (2 bytes) starting at `addr`. The byte at
`addr` is the most-significant byte, the byte at `addr + 1` the
least-significant. Returns `none` if `addr` is not halfword-aligned
(a multiple of 2). Unwritten bytes read as `0`. -/
def readMemHalf (s : State) (addr : W32) : Option W32 :=
  if addr.toNat % 2 ≠ 0 then none
  else
    let hi := s.mem.get? addr |>.getD 0
    let lo := s.mem.get? (addr + 1#32) |>.getD 0
    some ((BitVec.ofNat 32 hi.toNat <<< 8) ||| BitVec.ofNat 32 lo.toNat)

/-- Read a big-endian word (4 bytes) starting at `addr`. The byte at `addr`
is the most-significant byte, down to `addr + 3` as the least-significant.
Returns `none` if `addr` is not word-aligned (a multiple of 4). Unwritten
bytes read as `0`. Instruction fetch is `readMemWord s s.pc` (`Step.lean`). -/
def readMemWord (s : State) (addr : W32) : Option W32 :=
  if addr.toNat % 4 ≠ 0 then none
  else
    let b0 := s.mem.get? addr |>.getD 0
    let b1 := s.mem.get? (addr + 1#32) |>.getD 0
    let b2 := s.mem.get? (addr + 2#32) |>.getD 0
    let b3 := s.mem.get? (addr + 3#32) |>.getD 0
    some ((BitVec.ofNat 32 b0.toNat <<< 24) ||| (BitVec.ofNat 32 b1.toNat <<< 16) |||
          (BitVec.ofNat 32 b2.toNat <<< 8) ||| BitVec.ofNat 32 b3.toNat)

/-- Write a single byte `v` to memory at `addr`. Byte access has no alignment
requirement, so this always succeeds. -/
def writeMemByte (s : State) (addr : W32) (v : UInt8) : Option State :=
  some { s with mem := s.mem.insert addr v }

/-- Write a big-endian halfword `v` (low 16 bits used) to memory at `addr`:
the most-significant byte goes to `addr`, the least-significant to
`addr + 1`. Returns `none` if `addr` is not halfword-aligned. -/
def writeMemHalf (s : State) (addr : W32) (v : W32) : Option State :=
  if addr.toNat % 2 ≠ 0 then none
  else
    let hi : UInt8 := ((v >>> 8) &&& 0xff#32).toNat.toUInt8
    let lo : UInt8 := (v &&& 0xff#32).toNat.toUInt8
    some { s with mem := (s.mem.insert addr hi).insert (addr + 1#32) lo }

/-- Write a big-endian word `v` to memory at `addr`: the most-significant
byte goes to `addr`, down to the least-significant byte at `addr + 3`.
Returns `none` if `addr` is not word-aligned. -/
def writeMemWord (s : State) (addr : W32) (v : W32) : Option State :=
  if addr.toNat % 4 ≠ 0 then none
  else
    let b0 : UInt8 := ((v >>> 24) &&& 0xff#32).toNat.toUInt8
    let b1 : UInt8 := ((v >>> 16) &&& 0xff#32).toNat.toUInt8
    let b2 : UInt8 := ((v >>> 8) &&& 0xff#32).toNat.toUInt8
    let b3 : UInt8 := (v &&& 0xff#32).toNat.toUInt8
    some { s with
      mem := (((s.mem.insert addr b0).insert (addr + 1#32) b1).insert
                (addr + 2#32) b2).insert (addr + 3#32) b3 }
