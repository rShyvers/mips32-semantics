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

* **Loader.** `load p` writes the assembled image `p` (text, data, `.ktext`, `.kdata`; a
  `Program`) into the memory of `initialState textBase`. From then on the processor fetches
  from memory; the `Program` is no longer consulted by the machine.
* **Hosted services.** MARS/SPIM-style `syscall` services 1 (print int), 4 (print string),
  10 (exit) and 11 (print char), selected by `$v0`. The hosted run performs one *instead of*
  stepping when the instruction at `pc` is a `syscall` selecting it, as if an operating system's
  handler had served the System Call exception and returned. Any other `$v0` is not intercepted:
  the processor then takes the architectural System Call exception (`step`). The output buffer
  (`Hosted.out`) is environment state, not processor state.
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

/-- Write the 32-bit word `w` big-endian at `addr` (the byte layout of `writeMemWord`), without
an alignment check: the loader's own memory write. -/
def loadWord (m : Std.HashMap W32 UInt8) (addr w : W32) : Std.HashMap W32 UInt8 :=
  let b0 : UInt8 := ((w >>> 24) &&& 0xff#32).toNat.toUInt8
  let b1 : UInt8 := ((w >>> 16) &&& 0xff#32).toNat.toUInt8
  let b2 : UInt8 := ((w >>> 8) &&& 0xff#32).toNat.toUInt8
  let b3 : UInt8 := (w &&& 0xff#32).toNat.toUInt8
  (((m.insert addr b0).insert (addr + 1#32) b1).insert (addr + 2#32) b2).insert (addr + 3#32) b3

/-- Write every word of the image `p` into the memory of `s`. -/
def loadImage (p : Program) (s : State) : State :=
  { s with mem := p.fold (fun m addr w => loadWord m addr w) s.mem }

/-- **The hosted start state**: the processor state a loaded program finds, as if boot code had
already run. It is a convention of the hosted environment, NOT the architectural reset state: on a
Reset Exception "PC is loaded with 0xBFC0 0000", `Status.BEV ← 1`, `Status.ERL ← 1`, the restart
PC goes to `ErrorEPC`, and only a few registers have a defined state (MD00090 Vol III Rev 6.02
§6.2.5 Reset Exception, p.89-90). Here instead `pc = textBase` (`0x0040_0000`), `$sp = spInit`,
`Status = CU1` only (`BEV = ERL = 0`), `EBase` at its reset value, everything else 0
(`initialState`, `State.lean`). A later reset model + boot convention replaces exactly this
definition. -/
def hostedStart : State := initialState textBase

/-- **The loader.** The state a program starts in: `hostedStart` with the image `p` written into
memory. -/
def load (p : Program) : State := loadImage p hostedStart

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

/-- Scan up to `fuel` bytes from `addr`, stopping before the first `0x00`, each byte one
character. Memory that was never written reads as 0, so the scan ends there. -/
def readCString (s : State) (addr : W32) : Nat → String
  | 0 => ""
  | fuel + 1 =>
    let b := (s.mem.get? addr).getD 0
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
