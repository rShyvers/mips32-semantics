import Std.Data.HashMap.Basic
import Semantics.Word
import Semantics.Types
import Semantics.State
import Semantics.Instruction
import Semantics.Asm
import Semantics.Step
import Semantics.Env

/-!
# MipsRun — thin "assemble and run one `.asm` program" executable

Issue #1: the VibeCheck demo (`rShyvers/VibeCheck`) lets a user paste MIPS
assembly into a web page; a small server there shells out to this binary and
renders its output. Everything this needs already exists as pure functions
(`Asm.assemble`, `Env.load`, `Env.runHosted`) — this file is only the CLI/IO
wrapper and JSON emission around them, in `DiffHarness.lean`'s style of
composing strings directly (no external JSON-library dependency; none is
present in `lake-manifest.json`'s packages to reuse).

## CLI

```
MipsRun [--max-steps N] [--bare] [--reset] [path.asm]
```
`--max-steps N` bounds the run (default 1000000). The program is loaded (`Env.load`) and run
*hosted* (`Env.runHosted`): the MARS-style `syscall` services 1/4/10/11 are performed by the
environment, and the run stops by the environment's conventions (exit, an exception vector the
image does not cover, `pc` outside the image). `--bare` turns the services off: every
instruction, `syscall` included, is executed by the processor (`step`), so a `syscall` is the
System Call exception; the stopping conventions still apply (they are how this observer decides
the run is over; the processor itself never halts). `--reset` starts from the architectural
reset state (`resetState`: `pc = 0xBFC0_0000`, `Status.BEV = ERL = 1`) instead of the hosted
boot convention (`Env.loadAtReset`): the program must provide boot code at the reset vector
(`.ktext 0xBFC00000`), otherwise the run stops at once with `no_instruction` at `0xBFC0_0000`.
The JSON shape is the same; its `initial` field is then the reset state. Reads `.asm` source from `path.asm` if given, else from stdin. Prints exactly
one JSON object to stdout and nothing else. Exit codes:
- `0` — assembled and ran to completion or to the step limit (a *program*
  runtime error, e.g. an illegal instruction, is reported as data in the
  JSON, not a nonzero exit).
- `1` — assembly failed.
- `2` — usage/IO error (unreadable file, etc.) — no JSON is printed (there is
  nothing to report: we never even got a `.asm` to try).

## Loading (issue #12)

`Asm.assemble` returns the whole image (text, `.data`, `.ktext`, `.kdata`) as one `Program`; the
loader `Env.load` writes all of it into `State.physMem`, from which the processor fetches
instructions and loads data. (This replaces the former `materializeSpec` copy, which had the same
byte layout.)
-/

/-- Convert a word to its full-width (zero-padded), lowercase hex digits,
without the `0x` prefix. Used for `illegal_instruction`/`address_error`
payloads in the JSON `halt_reason` string. -/
def toHexDigits (w : W32) : String :=
  let hexChar (d : Nat) : Char :=
    if d < 10 then Char.ofNat (d + '0'.toNat) else Char.ofNat (d - 10 + 'a'.toNat)
  let rec go : Nat → Nat → List Char → List Char
    | 0, _, acc => acc
    | fuel + 1, n, acc => go fuel (n / 16) (hexChar (n % 16) :: acc)
  String.ofList (go 8 w.toNat [])

/-- JSON-escape a string's contents (without the surrounding quotes). -/
def jsonEscape (s : String) : String :=
  let escChar (c : Char) : String :=
    match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c =>
      if c.toNat < 0x20 then
        let hexChar (d : Nat) : Char :=
          if d < 10 then Char.ofNat (d + '0'.toNat) else Char.ofNat (d - 10 + 'a'.toNat)
        let rec go : Nat → Nat → List Char → List Char
          | 0, _, acc => acc
          | fuel + 1, n, acc => go fuel (n / 16) (hexChar (n % 16) :: acc)
        s!"\\u{String.ofList (go 4 c.toNat [])}"
      else String.singleton c
  String.join (s.toList.map escChar)

/-- A JSON string literal, including surrounding quotes. -/
def jsonStr (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

/-- Canonical MIPS register names, indexed `0..31`, matching `Asm.lean`'s
`regTable` (the same source of truth `Asm.assemble` itself accepts register
names against) — duplicated here since `regTable` is `private` to `Asm.lean`
and so not visible across files. -/
def regNames : Array String :=
  #["zero", "at", "v0", "v1", "a0", "a1", "a2", "a3",
    "t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7",
    "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7",
    "t8", "t9", "k0", "k1", "gp", "sp", "fp", "ra"]

/-- All 32 general-purpose registers of `s`, as a JSON object, canonical
names to unsigned decimal values. -/
def registersJson (s : State) : String :=
  let pairs := (List.range 32).map (fun i =>
    s!"{jsonStr (regNames[i]!)}: {(s.regs.getD i 0#32).toNat}")
  "{" ++ String.intercalate ", " pairs ++ "}"

/-- Render an `AsmError` as the human-readable string the `error` field
carries when assembly fails, including the 1-based source line number. -/
def renderAsmError (e : AsmError) : String :=
  match e with
  | .unknownMnemonic msg line => s!"unknown mnemonic: {msg} (line {line})"
  | .badRegister msg line => s!"bad register: {msg} (line {line})"
  | .undefinedLabel msg line => s!"undefined label: {msg} (line {line})"
  | .badImmediate msg line => s!"bad immediate: {msg} (line {line})"
  | .badDirective msg line => s!"bad directive: {msg} (line {line})"
  | .badOperand msg line => s!"bad operand: {msg} (line {line})"
  | .duplicateLabel msg line => s!"duplicate label: {msg} (line {line})"

/-- Short name of a `Cause.ExcCode` value, for `halt_reason`. -/
def excCodeName (code : W32) : String :=
  match code.toNat with
  | 4 => "address_error_load"
  | 5 => "address_error_store"
  | 8 => "syscall"
  | 9 => "breakpoint"
  | 10 => "reserved_instruction"
  | 11 => "coprocessor_unusable"
  | 12 => "arithmetic_overflow"
  | 13 => "trap"
  | n => s!"exccode_{n}"

/-- Render a `HaltReason` as the `halt_reason` string.

* `exit` — clean exit (environment call 10).
* `unhandled_exception:<name>:epc=0x<EPC>` — an architectural exception was
  taken and no handler is installed at the exception vector. `<name>` is
  `excCodeName` of `Cause.ExcCode` (`arithmetic_overflow`,
  `reserved_instruction`, `syscall`, `breakpoint`, `trap`, …). Address errors
  (`address_error_load`/`address_error_store`) append
  `:badvaddr=0x<BadVAddr>`.
* `no_instruction:0x<pc>` — control reached an aligned address outside the
  loaded image (ran off the program).

(The former `branch_in_delay_slot` no longer occurs: a control transfer in a
delay slot is now the Reserved Instruction exception, reported as
`unhandled_exception:reserved_instruction:…` when no handler is loaded.) -/
def renderHaltReason (r : HaltReason) : String :=
  match r with
  | .exit => "exit"
  | .unhandledException code epc badVAddr =>
    let base := s!"unhandled_exception:{excCodeName code}:epc=0x{toHexDigits epc}"
    if code == excCodeAdEL || code == excCodeAdES then s!"{base}:badvaddr=0x{toHexDigits badVAddr}"
    else base
  | .noInstruction pc => s!"no_instruction:0x{toHexDigits pc}"

/-- Raw FCSR as the model holds it (`State.fcsr`). `scripts/oracle.py` compares
exactly the bits in `fcsrMask` and nothing else. -/
def fcsrOf (s : State) : W32 := s.fcsr

/-- The FCSR bits the model implements: RM (1..0), Flags (6..2), Enables
(11..7), Cause (17..12), FS (24), FCC0 (23), FCC1..7 (31..25); bits 22..18 are
reserved and read as zero (`fcsrWritableMask` in `Semantics/FpOps.lean`). -/
def fcsrMask : W32 := Mips.Fp.fcsrWritableMask

/-- A JSON array of decimal numbers. -/
def jsonNums (xs : List Nat) : String :=
  "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

/-- Sorted `[addr, word]` pairs as a JSON array. -/
def jsonPairs (xs : Array (Nat × Nat)) : String :=
  let ys := xs.qsort (fun a b => a.1 < b.1)
  "[" ++ String.intercalate ", " (ys.toList.map (fun (a, w) => s!"[{a}, {w}]")) ++ "]"

/-- The assembled program image: every `Program` entry (text, data, `.ktext`,
`.kdata`), address -> 32-bit word, sorted by address. -/
def imageJson (p : Program) : String :=
  jsonPairs (p.toArray.map (fun (a, w) => (a.toNat, w.toNat)))

/-- The nonzero aligned words of the final state's **physical** memory, `[physical address,
word]`, sorted (every byte the loader or a store wrote; `Env.physWord`). -/
def physWords (s : State) : Array (Nat × Nat) :=
  let addrs : Std.HashMap Nat Unit :=
    s.physMem.fold (fun acc a _ => acc.insert (a.toNat / 4 * 4) ()) {}
  addrs.fold (fun (acc : Array (Nat × Nat)) a _ =>
    let w := physWord s.physMem (BitVec.ofNat 32 a)
    if w == 0#32 then acc else acc.push (a, w.toNat)) #[]

/-- The `memory` field: every nonzero aligned word of physical memory, reported at its **virtual**
address `Env.canonicalVAddr pa` (kuseg for the loaded text/data/stack, kseg0 for the low 512 MB,
identity for kseg2/kseg3), sorted. It inverts the loader: `canonicalVAddr (loadAddr va) = va` for
every `va` outside kseg1 (`canonicalVAddr_loadAddr`, `Specs/Loader.lean`), so `memory` speaks the
same (virtual) addresses as `image` and the registers. Words reachable through several virtual
names (kseg0/kseg1 aliases) appear once, under the kseg0 name (`canonicalVAddr_loadAddr_kseg1`). -/
def memoryJson (s : State) : String :=
  jsonPairs ((physWords s).map (fun (a, w) => ((canonicalVAddr (BitVec.ofNat 32 a)).toNat, w)))

/-- The `physical_memory` field: the same words keyed by physical address. -/
def physicalMemoryJson (s : State) : String :=
  jsonPairs (physWords s)

/-- The FPU control registers as `cfc1` reads them (`Mips.Fp.readControl`): FIR (0), FCCR (25),
FEXR (26), FENR (28), FCSR (31). Derived from `State.fcsr`; FIR is a constant. -/
def fcrJson (s : State) : String :=
  "{" ++
  s!"\"fir\": {Mips.Fp.firValue.toNat}, " ++
  s!"\"fccr\": {(Mips.Fp.readFCCR s.fcsr).toNat}, " ++
  s!"\"fexr\": {(Mips.Fp.readFEXR s.fcsr).toNat}, " ++
  s!"\"fenr\": {(Mips.Fp.readFENR s.fcsr).toNat}, " ++
  s!"\"fcsr\": {(Mips.Fp.readFCSR s.fcsr).toNat}" ++
  "}"

/-- Every coprocessor-0 register the model has (the `(rd, sel)` pairs of `mfc0`), each as
`mfc0` reads it (the same functions `Step.lean`'s `mfc0` arm uses), plus the stored fields where
they differ from the read value (`_raw` suffix; `ebase` keeps its original meaning, the stored
field, and `ebase_read` is the read value). A read-out only: computed outside `step`. -/
def cp0Json (s : State) : String :=
  "{" ++
  s!"\"status\": {s.cp0Status.toNat}, \"cause\": {(causeValue s).toNat}, " ++
  s!"\"epc\": {s.cp0Epc.toNat}, \"badvaddr\": {s.cp0BadVAddr.toNat}, " ++
  s!"\"errorepc\": {s.cp0ErrorEpc.toNat}, \"ebase\": {s.cp0EBase.toNat}, " ++
  s!"\"count\": {s.cp0Count.toNat}, \"compare\": {s.cp0Compare.toNat}, " ++
  s!"\"hwrena\": {s.cp0HWREna.toNat}, " ++
  s!"\"cause_raw\": {s.cp0Cause.toNat}, \"timer_int\": {s.cp0TimerInt}, " ++
  s!"\"ebase_read\": {(ebaseValue s).toNat}, " ++
  s!"\"intctl\": {intCtlValue.toNat}, \"srsctl\": {srsCtlValue.toNat}, " ++
  s!"\"prid\": {prIdValue.toNat}, " ++
  s!"\"config\": {(configValue s).toNat}, \"config1\": {config1Value.toNat}, " ++
  s!"\"config_k0_raw\": {s.cp0ConfigK0.toNat}, \"config_k23_raw\": {s.cp0ConfigK23.toNat}, " ++
  s!"\"config_ku_raw\": {s.cp0ConfigKU.toNat}" ++
  "}"

/-- **The JSON render of a `State`** (`initial` and `final`): every field of `State` except
`physMem` (rendered separately as `memory`/`physical_memory`), plus read-outs derived from it
(`fcr`, the CP0 read values, `kernel_mode`, `interrupt_requests`). Every value is computed
outside `step` and changes nothing; it exists so that a front end can show the machine as other
simulators do. Emitted for the *initial* state too, so that other executors (QEMU harness) are
data-driven from this binary rather than hard-coding its conventions. Field list:
`scripts/README.md`, "JSON render". -/
def stateJson (s : State) : String :=
  "{" ++
  s!"\"pc\": {s.pc.toNat}, " ++
  s!"\"gpr\": {jsonNums (s.regs.toList.map (·.toNat))}, " ++
  s!"\"hi\": {s.hi.toNat}, \"lo\": {s.lo.toNat}, " ++
  s!"\"fpr\": {jsonNums (s.fpRegs.toList.map (·.toNat))}, " ++
  s!"\"fcsr\": {(fcsrOf s).toNat}, " ++
  s!"\"fp_cond_flag\": {(fcsrOf s).getLsbD 23}, " ++
  s!"\"ll_bit\": {s.llBit}, " ++
  s!"\"ll_addr\": {s.llAddr.toNat}, " ++
  s!"\"pending_branch\": {match s.pendingBranch with | some t => toString t.toNat | none => "null"}, " ++
  s!"\"standby\": {s.standby}, " ++
  s!"\"nullified\": {s.nullified}, " ++
  s!"\"hw_int\": {s.hwInt.toNat}, " ++
  s!"\"fir\": {Mips.Fp.firValue.toNat}, " ++
  s!"\"fcr\": {fcrJson s}, " ++
  s!"\"kernel_mode\": {kernelMode s}, " ++
  s!"\"interrupt_requests\": {(interruptRequests s).toNat}, " ++
  s!"\"cp0\": {cp0Json s}" ++
  "}"

/-- Structured halt reason (`halt` field). -/
def haltJson (r : Option HaltReason) : String :=
  match r with
  | none => "{\"kind\": \"limit\"}"
  | some .exit => "{\"kind\": \"exit\"}"
  | some (.unhandledException code epc bad) =>
    s!"\{\"kind\": \"unhandled_exception\", \"code\": {code.toNat}, \"epc\": {epc.toNat}, \"badvaddr\": {bad.toNat}}"
  | some (.noInstruction pc) => s!"\{\"kind\": \"no_instruction\", \"pc\": {pc.toNat}}"

/-- The full success-path JSON object (`assembled: true`), for either a
`halted` or `limitReached` `HostedResult`. The first block of fields is the
original contract (unchanged); the second block is the oracle extension. -/
def renderRunResult (prog : Program) (init : State) (r : HostedResult) : String :=
  let (halted, haltReasonJson, haltObj, steps, h) :=
    match r with
    | .halted reason h steps =>
      (true, jsonStr (renderHaltReason reason), haltJson (some reason), steps, h)
    | .limitReached h steps => (false, "null", haltJson none, steps, h)
  let s := h.machine
  "{\"assembled\": true, " ++
  s!"\"halted\": {halted}, " ++
  s!"\"halt_reason\": {haltReasonJson}, " ++
  s!"\"steps\": {steps}, " ++
  s!"\"output\": {jsonStr h.out}, " ++
  s!"\"registers\": {registersJson s}, " ++
  "\"error\": null, " ++
  -- oracle extension
  s!"\"halt\": {haltObj}, " ++
  s!"\"final\": {stateJson s}, " ++
  s!"\"fcsr_mask\": {fcsrMask.toNat}, " ++
  s!"\"initial\": {stateJson init}, " ++
  s!"\"image\": {imageJson prog}, " ++
  s!"\"memory\": {memoryJson s}, " ++
  s!"\"physical_memory\": {physicalMemoryJson s}" ++
  "}"

/-- The failure-path JSON object (`assembled: false`): every field besides
`assembled`/`error` is `null`, per the issue's field rules. -/
def renderAsmFailure (e : AsmError) : String :=
  "{\"assembled\": false, \"halted\": null, \"halt_reason\": null, " ++
  "\"steps\": null, \"output\": null, \"registers\": null, " ++
  s!"\"error\": {jsonStr (renderAsmError e)}}"

/-- Read the `.asm` source: from the file at `path` if given, else from
stdin. `Except.error` carries a human message for a `2`-exit usage/IO error
(no JSON is printed in that case — there is no program to report on). -/
def readSource (path : Option String) : IO (Except String String) := do
  try
    match path with
    | some p => pure (Except.ok (← IO.FS.readFile p))
    | none => pure (Except.ok (← (← IO.getStdin).readToEnd))
  catch e => pure (Except.error (toString e))

/-- Command line: `MipsRun [--max-steps N] [--bare] [--reset] [path.asm]`. -/
structure Cli where
  path : Option String := none
  maxSteps : Nat := 1000000
  /-- `--bare`: no hosted `syscall` services. -/
  bare : Bool := false
  /-- `--reset`: start at the reset vector from `resetState` (no boot convention). -/
  reset : Bool := false

def parseArgs : List String → Except String Cli
  | [] => .ok {}
  | "--max-steps" :: n :: rest =>
    match n.toNat?, parseArgs rest with
    | some k, .ok c => .ok { c with maxSteps := k }
    | none, _ => .error s!"--max-steps expects a number, got '{n}'"
    | _, .error e => .error e
  | ["--max-steps"] => .error "--max-steps expects a number"
  | "--bare" :: rest =>
    match parseArgs rest with
    | .ok c => .ok { c with bare := true }
    | .error e => .error e
  | "--reset" :: rest =>
    match parseArgs rest with
    | .ok c => .ok { c with reset := true }
    | .error e => .error e
  | p :: rest =>
    match parseArgs rest with
    | .ok c => .ok { c with path := some p }
    | .error e => .error e

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error msg =>
    IO.eprintln s!"MipsRun: {msg}"
    return 2
  | .ok cli =>
  match ← readSource cli.path with
  | .error msg =>
    IO.eprintln s!"MipsRun: {msg}"
    return 2
  | .ok src =>
    match assemble src with
    | .error e =>
      IO.println (renderAsmFailure e)
      return 1
    | .ok prog =>
      if cli.reset then
        let result := runProgramAtReset prog cli.maxSteps (services := !cli.bare)
        IO.println (renderRunResult prog resetState result)
      else
        let result := runProgram prog cli.maxSteps (services := !cli.bare)
        IO.println (renderRunResult prog hostedStart result)
      return 0

-- ====================================================================
-- ## In-file tests (DESIGN.md §5 / CLAUDE.md §5)
--
-- `#guard`-checked, hand-crafted `.asm` programs (inline string literals,
-- in the style of `DiffHarness.lean`'s embedded corpus copies) exercising
-- the same `assemble`/`run` pipeline `main` drives, covering the four
-- cases the issue calls out: a clean exit with output, an assembly error,
-- an illegal-instruction halt, and the step-limit-exhausted case. These
-- check the underlying `HostedResult`/`AsmResult` classification (what
-- `renderRunResult`/`renderAsmFailure` then render into JSON); the actual
-- rendered JSON shape for each of these four cases was additionally
-- eyeballed against the issue's example by running the built binary
-- directly (see the task report — not reproducible inside `#guard`, since
-- that only sees pure values, not stdout/exit codes).
-- ====================================================================

section GoldenTests

/-- Clean exit with non-empty output: print `$a0` as an int (syscall 1),
then exit (syscall 10). -/
private def cleanExitSrc : String :=
"main:\n" ++
"    li   $v0, 1\n" ++
"    li   $a0, 42\n" ++
"    syscall\n" ++
"    li   $v0, 10\n" ++
"    syscall\n"

private def cleanExitResult : HostedResult :=
  match assemble cleanExitSrc with
  | .ok prog => runProgram prog 1000000
  | .error _ => .limitReached { machine := hostedStart } 0 -- unreachable: assembles fine

#guard (match cleanExitResult with | .halted .exit _ _ => true | _ => false)
#guard (match cleanExitResult with | .halted .exit h _ => h.out == "42" | _ => false)

/-- Regression test for issue #12: a `.data`-declared string, loaded via
`la` + `syscall 4` (print string), must read the declared bytes rather
than all-zero memory: the loader writes the `.data` image (before issue #12
this produced an empty/garbage output instead of `"hi"`). -/
private def dataSegmentSrc : String :=
".data\n" ++
"msg: .asciiz \"hi\"\n" ++
".text\n" ++
"    la   $a0, msg\n" ++
"    li   $v0, 4\n" ++
"    syscall\n" ++
"    li   $v0, 10\n" ++
"    syscall\n"

private def dataSegmentResult : HostedResult :=
  match assemble dataSegmentSrc with
  | .ok prog => runProgram prog 1000000
  | .error _ => .limitReached { machine := hostedStart } 0 -- unreachable: assembles fine

#guard (match dataSegmentResult with | .halted .exit h _ => h.out == "hi" | _ => false)

/-- Not MIPS at all — `assemble` must reject it with an error, not throw. -/
private def notMipsSrc : String := "not mips at all"

#guard (match assemble notMipsSrc with | .error _ => true | .ok _ => false)

/-- A `syscall` whose `$v0` (99) selects no hosted service is executed by the
processor: the System Call exception (ExcCode 8); with no handler loaded the
hosted run stops with `unhandledException 8 …`. -/
private def illegalInstrSrc : String :=
"main:\n" ++
"    li   $v0, 99\n" ++
"    syscall\n"

private def illegalInstrResult : HostedResult :=
  match assemble illegalInstrSrc with
  | .ok prog => runProgram prog 1000000
  | .error _ => .limitReached { machine := hostedStart } 0 -- unreachable: assembles fine

#guard (match illegalInstrResult with | .halted (.unhandledException c _ _) _ _ => c == excCodeSys | _ => false)
#guard renderHaltReason (.unhandledException 12#32 0x00400008#32 0#32)
  = "unhandled_exception:arithmetic_overflow:epc=0x00400008"
#guard renderHaltReason (.unhandledException 4#32 0x00400008#32 0x10010001#32)
  = "unhandled_exception:address_error_load:epc=0x00400008:badvaddr=0x10010001"
#guard renderHaltReason (.noInstruction 0x00400010#32) = "no_instruction:0x00400010"

/-- Step-limit-exhausted: an unconditional self-jump never halts, so a small
fuel budget is exhausted (kept small here for test speed; `main` itself
uses the full `1_000_000`-step budget).

Includes an explicit `nop` delay-slot instruction after the `j`: real MIPS32
branches/jumps never transfer control immediately (SPEC-NOTES §9 item 1) --
`j main`'s own step falls through to `pc + 4` and only *schedules* `main` as
the target (`State.pendingBranch`), which is committed by whichever
instruction retires next. Without a delay-slot instruction in the loaded
image at `pc + 4` (this program's only assembled word is the `j` itself),
the hosted run stops there with `noInstruction` instead of ever reaching
the step limit. The `nop` fills that
slot so the loop is genuinely infinite (2 steps per iteration: the `j`, then
its delay slot, which is where the jump actually lands), matching this
test's intent of exercising the step-limit/`"halted": false` path -- it
still runs for exactly `maxSteps` steps since it never halts on its own. -/
private def infiniteLoopSrc : String :=
"main:\n" ++
"    j main\n" ++
"    nop\n"

private def infiniteLoopResult : HostedResult :=
  match assemble infiniteLoopSrc with
  | .ok prog => runProgram prog 50
  | .error _ => .halted .exit { machine := hostedStart } 0 -- unreachable: assembles fine

#guard (match infiniteLoopResult with | .limitReached _ steps => steps == 50 | _ => false)

end GoldenTests

/-- `--bare`: the same `syscall 1` is the System Call exception (no hosted services); with no
handler loaded the observer stops with `unhandledException 8`, and nothing is printed. -/
private def bareResult : HostedResult :=
  match assemble cleanExitSrc with
  | .ok prog => runProgram prog 1000000 (services := false)
  | .error _ => .limitReached { machine := hostedStart } 0 -- unreachable: assembles fine

#guard (match bareResult with
        | .halted (.unhandledException c _ _) h _ => c == excCodeSys && h.out == ""
        | _ => false)

/-- `--reset`: boot code at the reset vector (`.ktext 0xBFC00000`) reads the reset `Status`
(`BEV | ERL` = `0x0040_0004`), leaves the reset state with `eret` (`ERL = 1`: `pc ← ErrorEPC`,
`ERL ← 0`) into the program, which prints that value and exits. -/
private def resetBootSrc : String :=
".ktext 0xBFC00000\n" ++
"    mfc0 $t0, $12\n" ++
"    la   $t1, main\n" ++
"    mtc0 $t1, $30\n" ++
"    eret\n" ++
".text\n" ++
"main:\n" ++
"    li   $v0, 1\n" ++
"    move $a0, $t0\n" ++
"    syscall\n" ++
"    li   $v0, 10\n" ++
"    syscall\n"

private def resetBootResult : HostedResult :=
  match assemble resetBootSrc with
  | .ok prog => runProgramAtReset prog 1000
  | .error _ => .limitReached { machine := resetState } 0 -- unreachable: assembles fine

#guard (match resetBootResult with
        | .halted .exit h _ => h.out == "4194308" && h.machine.cp0Status == statusBevMask
        | _ => false)

/-- `--reset` without boot code at the reset vector: the run stops at once at `0xBFC0_0000`. -/
private def resetNoBootResult : HostedResult :=
  match assemble cleanExitSrc with
  | .ok prog => runProgramAtReset prog 1000
  | .error _ => .limitReached { machine := resetState } 0 -- unreachable: assembles fine

#guard (match resetNoBootResult with
        | .halted (.noInstruction pc) _ 1 => pc == 0xBFC00000#32
        | _ => false)
