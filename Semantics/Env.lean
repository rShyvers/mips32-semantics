import Std.Data.HashMap.Basic
import Semantics.Word
import Semantics.Types
import Semantics.State
import Semantics.Instruction
import Semantics.Step

/-!
# Env — the environment around the processor (NOT part of the architecture)

`Step.lean`'s `step` is one instruction time of the processor and nothing else. Everything in this
file is a convention of this model's *environment* — what a loader, an operating system or a test
bench does around the processor — and has no counterpart in the MIPS32 manuals:

* **Start state.** The machine starts at the architectural reset state (`Step.lean`'s
  `resetState`: `pc = 0xBFC0_0000`, `Status.BEV = ERL = 1`). The hosted environment then applies
  a named **boot convention** (`bootConvention`): what a boot ROM would do before handing control
  to a loaded program. That boot code is not part of the architecture; `hostedStart` is
  `bootConvention textBase resetState`. `MipsRun --reset` skips the boot convention and starts at
  the reset vector (`loadAtReset`).
* **Loader.** `load p` writes the assembled image `p` (text, data, `.ktext`, `.kdata`; a
  `Program`, keyed by **virtual** address) into the **physical** memory of `hostedStart`: each
  word at `loadAddr va`, the physical address the Fixed Mapping MMU gives `va` while
  `Status.ERL = 0` (kuseg `+ 0x4000_0000`, kseg0/kseg1 the low 512 MB, kseg2/kseg3 identity).
  That is the translation a loaded program runs under (the hosted start has `ERL = 0`; a reset-time
  program must clear `ERL` before it runs kuseg code, since executing from kuseg with `ERL = 1` is
  UNDEFINED, MD00090 Vol III Rev 6.02 §A.1.2, p.316). `Specs/Loader.lean` proves that a fetch or
  load of an image address then returns the image word. From then on the processor fetches from
  memory; the `Program` is no longer consulted by the machine.
* **Hosted services.** MARS/SPIM-style `syscall` services 1 (print int), 4 (print string),
  10 (exit) and 11 (print char), selected by `$v0`. The hosted run performs one *instead of*
  stepping when the instruction at `pc` is a `syscall` selecting it, as if an operating system's
  handler had served the System Call exception and returned. Any other `$v0` is not intercepted:
  the processor then takes the architectural System Call exception (`step`). The output buffer
  (`Hosted.out`) is environment state, not processor state. A served `syscall` is not a processor
  step, so it does not advance the timer (`Count`).
* **Stopping conventions.** The processor never halts. The hosted run *stops observing* it when
  `pc` is word-aligned and outside the loaded image (`stopReason`): `unhandledException code epc
  badVAddr` when an exception was just taken to a vector the image does not cover (`Status.EXL =
  1` and `pc` is the general exception vector), `noInstruction pc` otherwise; and on service 10
  (`exit`).

`runHosted env fuel h` iterates `hostStep`. With `env.services = false` it performs no service
(the `MipsRun --bare` mode): every instruction, `syscall` included, is executed by `step`.
`Specs/Hosted.lean` proves that `hostStep` *is* `step` whenever no service is selected and the
run is not stopped, and that `runHosted` then agrees with the bare `run`.
-/

/-! ## Loader -/

/-- **Where the loader puts the image word with virtual address `va`**: its physical address under
the Fixed Mapping MMU with `Status.ERL = 0` (`fixedMappingPA false`, MD00090 Vol III Rev 6.02
Table A.1, p.313-314), the translation every loaded program runs under (`hostedStart` has
`ERL = 0`; see the module docstring for `loadAtReset`). Text `0x0040_0000` → `0x4040_0000`, data
`0x1001_0000` → `0x5001_0000`, `.ktext 0x8000_0180` → `0x0000_0180`, `.kdata 0x9000_0000` →
`0x1000_0000`, boot code `0xBFC0_0000` → `0x1FC0_0000`. -/
def loadAddr (va : VAddr) : PAddr := fixedMappingPA false va

/-- **The virtual name an observer gives a physical address** (environment convention, used by
`MipsRun`'s `memory` JSON field): the inverse of `loadAddr` — kuseg for `0x4000_0000`-`0xBFFF_FFFF`
(`PA - 0x4000_0000`), kseg0 for the low 512 MB (`PA + 0x8000_0000`), identity for kseg2/kseg3
(`0xC000_0000`-), and identity for `0x2000_0000`-`0x3FFF_FFFF`, which only kuseg with `ERL = 1`
reaches (Table A.1, p.314: "inaccessible when the ERL bit is off"). -/
def canonicalVAddr (pa : PAddr) : VAddr :=
  if pa.toNat < 0x20000000 then pa + 0x80000000#32
  else if pa.toNat < 0x40000000 then pa
  else if pa.toNat < 0xC0000000 then pa - 0x40000000#32
  else pa

/-- The big-endian word of physical memory `m` at physical address `pa` (no translation, no
alignment check: an observer's read, not the processor's). -/
def physWord (m : Std.HashMap PAddr UInt8) (pa : PAddr) : W32 :=
  let b (a : PAddr) : W32 := BitVec.ofNat 32 ((m.get? a).getD 0).toNat
  (b pa <<< 24) ||| (b (pa + 1#32) <<< 16) ||| (b (pa + 2#32) <<< 8) ||| b (pa + 3#32)

/-- Write the 32-bit word `w` big-endian at physical address `pa` (the byte layout of
`writeMemWord`), without an alignment check: the loader's own memory write. -/
def loadWord (m : Std.HashMap PAddr UInt8) (pa : PAddr) (w : W32) : Std.HashMap PAddr UInt8 :=
  let b0 : UInt8 := ((w >>> 24) &&& 0xff#32).toNat.toUInt8
  let b1 : UInt8 := ((w >>> 16) &&& 0xff#32).toNat.toUInt8
  let b2 : UInt8 := ((w >>> 8) &&& 0xff#32).toNat.toUInt8
  let b3 : UInt8 := (w &&& 0xff#32).toNat.toUInt8
  (((m.insert pa b0).insert (pa + 1#32) b1).insert (pa + 2#32) b2).insert (pa + 3#32) b3

/-- Write every word of the image `p` (virtual addresses) into the physical memory of `s`, each at
`loadAddr` of its address. -/
def loadImage (p : Program) (s : State) : State :=
  { s with physMem := p.fold (fun m va w => loadWord m (loadAddr va) w) s.physMem }

/-- **The boot convention** of the hosted environment: what boot code at the reset vector does
before it jumps to a loaded program whose entry point is `entry`. Written as the instructions
a boot ROM would execute in Kernel Mode:

1. `mtc0 Status ← 0x2000_0000`: `CU1 = 1` (the FPU is usable), `BEV = 0` (normal exception
   vectors, `EBase`), `ERL = 0`, `EXL = 0`, `UM = 0` (the program runs in Kernel Mode, as MARS and
   SPIM programs expect), `IE = 0`, `IM = 0`, `CU0 = 0`.
2. `$sp ← spInit` (`0x7FFF_EFFC`, the MARS stack pointer).
3. Jump to `entry` (a ROM would `jr` there, or set `ErrorEPC` and `eret`; the model just sets
   `pc`, and no branch is pending).

Every other register keeps its reset value. This is an environment convention, not an
architectural requirement. -/
def bootConvention (entry : W32) (s : State) : State :=
  { (writeReg s 29 spInit) with cp0Status := statusCu1Mask, pc := entry, pendingBranch := none }

/-- **The hosted start state**: the architectural reset state (`resetState`, MD00090 Vol III
Rev 6.02 §6.2.5, p.89-90) followed by the boot convention with entry point `textBase`
(`0x0040_0000`). It equals `initialState textBase` (`Specs/Reset.lean`,
`hostedStart_is_reset_then_boot`). -/
def hostedStart : State := bootConvention textBase resetState

/-- **The loader.** The state a program starts in: `hostedStart` with the image `p` written into
memory. -/
def load (p : Program) : State := loadImage p hostedStart

/-- **The reset loader** (`MipsRun --reset`): the image `p` written into the physical memory of
`resetState`, with no boot convention, at the same physical addresses as `load` (`loadAddr`).
Execution begins at the reset vector `0xBFC0_0000` (kseg1, physical `0x1FC0_0000`), so the image
must place boot code there (e.g. `.ktext 0xBFC00000`); otherwise the hosted run stops at once
(`noInstruction 0xBFC0_0000`). kuseg words are placed for `ERL = 0`: the boot code must clear
`ERL` (e.g. by `eret`) before it runs or reads them through kuseg — with `ERL = 1` kuseg is the
identity map (§4.7, p.31) and executing from it is UNDEFINED (§A.1.2, p.316). -/
def loadAtReset (p : Program) : State := loadImage p resetState

/-! ## Hosted run -/

/-- Why the hosted run stopped observing the processor. None of these is a processor state. -/
inductive HaltReason where
  /-- Hosted service 10 (`exit`): a `syscall` with `$v0 = 10`. -/
  | exit
  /-- The machine has just entered the general exception vector (`Status.EXL = 1`, `pc` = the
  vector) and the loaded image has no word there: no handler was loaded. Carries `Cause.ExcCode`,
  `EPC` and `BadVAddr` (meaningful for address errors, `code` 4 or 5). -/
  | unhandledException (code epc badVAddr : W32)
  /-- The word-aligned `pc` is outside the loaded image (control left the program) and the machine
  is not at the exception vector with `EXL = 1`. The processor itself would go on fetching (memory
  that was never written reads as 0, `sll $0, $0, 0`). -/
  | noInstruction (pc : W32)
  deriving Repr, DecidableEq

/-- The environment of a hosted run: the loaded image (its addresses are the region the run
observes) and whether the hosted `syscall` services are provided. -/
structure HostEnv where
  /-- The image the loader wrote (`load`); `image.contains a` is "a word was loaded at `a`". -/
  image : Program
  /-- Whether the MARS-style `syscall` services are performed (`false`: the bare machine). -/
  services : Bool := true

/-- The state of a hosted run: the processor and the environment's output buffer. -/
structure Hosted where
  /-- The processor. -/
  machine : State
  /-- Everything the hosted print services have written so far. -/
  out : String := ""

/-- The result of one hosted step. -/
inductive HostStep where
  | next (h : Hosted)
  | halt (r : HaltReason)

/-- "An exception was just taken": `Status.EXL = 1` and `pc` is the general exception vector. -/
def atUnhandledVector (s : State) : Bool :=
  s.cp0Status &&& statusExlMask != 0#32 && s.pc == exceptionVector s

/-- The stopping convention: `pc` is word-aligned and no word was loaded there. (A misaligned `pc`
is not a stop: the processor raises Address Error, `step`.) -/
def stopReason (env : HostEnv) (s : State) : Option HaltReason :=
  if s.pc.toNat % 4 = 0 && !env.image.contains s.pc then
    some (if atUnhandledVector s then .unhandledException (causeExcCode s) s.cp0Epc s.cp0BadVAddr
          else .noInstruction s.pc)
  else none

/-- The hosted services. -/
inductive Service where
  | printInt | printString | exit | printChar
  deriving Repr, DecidableEq

/-- The service the instruction at `pc` selects: it must be a `syscall` and `$v0` must be 1, 4,
10 or 11. Any other `$v0` selects nothing (the processor then takes the System Call exception). -/
def selectedService (s : State) : Option Service :=
  match readMemWord s s.pc with
  | none => none
  | some w =>
    match decode w with
    | some (.syscall _) =>
      match (readReg s 2).toNat with
      | 1 => some .printInt
      | 4 => some .printString
      | 10 => some .exit
      | 11 => some .printChar
      | _ => none
    | _ => none

/-- Maximum number of bytes scanned by service 4 (print string): an environment limit that keeps
the service total. -/
def printStringFuel : Nat := 65536

/-- Scan up to `fuel` bytes from the virtual address `addr` (read with `readMemByte`, i.e. through
the MMU in the current mode, as the program itself would), stopping before the first `0x00` or the
first byte the program could not read (a kernel address from User Mode), each byte one character.
Memory that was never written reads as 0, so the scan ends there. -/
def readCString (s : State) (addr : VAddr) : Nat → String
  | 0 => ""
  | fuel + 1 =>
    match readMemByte s addr with
    | none => ""
    | some b =>
      if b == 0 then ""
      else String.singleton (Char.ofNat b.toNat) ++ readCString s (addr + 1#32) fuel

/-- Perform a hosted service on behalf of the `syscall` at `pc`. A print service appends to the
output and then completes the `syscall` like any non-control-flow instruction (`advance`: `pc + 4`,
or the pending branch target if the `syscall` is in a delay slot); no register changes. `exit`
stops the run. -/
def performService (svc : Service) (h : Hosted) : HostStep :=
  let s := h.machine
  match svc with
  | .printInt => .next { machine := advance s s, out := h.out ++ toString (asSigned (readReg s 4)) }
  | .printString =>
    .next { machine := advance s s, out := h.out ++ readCString s (readReg s 4) printStringFuel }
  | .exit => .halt .exit
  | .printChar =>
    .next { machine := advance s s,
            out := h.out ++ String.singleton (Char.ofNat ((readReg s 4 &&& 0xff#32).toNat)) }

/-- One hosted step: stop if the stopping convention applies; else perform the selected hosted
service, if services are on and one is selected; else one processor step. -/
def hostStep (env : HostEnv) (h : Hosted) : HostStep :=
  match stopReason env h.machine with
  | some r => .halt r
  | none =>
    match (if env.services then selectedService h.machine else none) with
    | some svc => performService svc h
    | none => .next { h with machine := step h.machine }

/-- Outcome of a hosted run: stopped (the reason, the hosted state when it stopped, and the number
of hosted steps including the stopping one), or the fuel ran out. -/
inductive HostedResult where
  | halted (r : HaltReason) (h : Hosted) (steps : Nat)
  | limitReached (h : Hosted) (steps : Nat)

/-- The hosted run: `hostStep` iterated at most `fuel` times. -/
def runHosted (env : HostEnv) (fuel : Nat) (h : Hosted) : HostedResult :=
  let rec go : Nat → Hosted → Nat → HostedResult
    | 0, h, steps => .limitReached h steps
    | fuel + 1, h, steps =>
      match hostStep env h with
      | .halt r => .halted r h (steps + 1)
      | .next h' => go fuel h' (steps + 1)
  go fuel h 0

/-- The hosted state a run ended in. -/
def HostedResult.final : HostedResult → Hosted
  | .halted _ h _ => h
  | .limitReached h _ => h

/-- Load `p` and run it hosted (services on), as `MipsRun` does by default. -/
def runProgram (p : Program) (fuel : Nat) (services : Bool := true) : HostedResult :=
  runHosted { image := p, services } fuel { machine := load p }

/-- Load `p` into the reset state and run it hosted from the reset vector (`MipsRun --reset`). -/
def runProgramAtReset (p : Program) (fuel : Nat) (services : Bool := true) : HostedResult :=
  runHosted { image := p, services } fuel { machine := loadAtReset p }
