import Semantics.Asm.Operands

/-!
# Asm.System — SYSCALL, BREAK, register traps, SIGRIE, SYNC, PAUSE, Coprocessor 0, CACHE

Optional code operands in GNU as syntax: `syscall [code]` (0..0xFFFFF), `break [code[, code2]]`
(each 0..1023: `code` to bits 25..16, `code2` to bits 15..6 of the 20-bit field), `teq rs, rt[,
code]` (0..1023), `sync [stype]` (0..31), `wait [code]` (0..0x7FFFF), `mfc0`/`mtc0 rt, rd[, sel]`
(sel 0..7), `di`/`ei`/`dvp`/`evp [rt]`, `sigrie [code]` (0..0xFFFF), `cache op, offset(base)` (op 0..31, 9-bit
offset -256..255, as `pref`). Release 6 removed the trap-immediate forms (TEQI ... TLTIU).
-/

namespace Asm

/-- `break [code[, code2]]` (GNU as: `code` in bits 25..16, `code2` in bits 15..6). -/
def breakOp : Enc := fun c ops => do
  let code (t : String) : Except AsmError Nat := parseCode c.name "code" 1023 t c.line
  match ops with
  | [] => pure (.break 0#32)
  | [a] => do pure (.break (fld ((← code a) * 1024)))
  | [a, b] => do pure (.break (fld ((← code a) * 1024 + (← code b))))
  | _ => badShape c "[code[, code2]]"

/-- System calls, breakpoints, traps, barriers, PAUSE and the Coprocessor 0 instructions. -/
def systemTable : EncTable :=
  [ ("syscall", optOp "code" 1048575 .syscall),
    ("break",   breakOp),
    ("teq",  trapOp .teq),
    ("tne",  trapOp .tne),
    ("tlt",  trapOp .tlt),
    ("tge",  trapOp .tge),
    ("tltu", trapOp .tltu),
    ("tgeu", trapOp .tgeu),
    ("sync",  optOp "stype" 31 .sync),
    ("pause", none0 .pause),
    -- Coprocessor 0
    ("mfc0", copSel "CP0" .mfc0),
    ("mtc0", copSel "CP0" .mtc0),
    ("di",   optGpr .di),
    ("ei",   optGpr .ei),
    ("eret", none0 .eret),
    ("wait", optOp "code" 524287 .wait),
    ("rdpgpr", gpr2 "rd, rt" .rdpgpr),
    ("wrpgpr", gpr2 "rd, rt" .wrpgpr),
    ("eretnc", none0 .eretnc),
    ("sigrie", optOp "code" 65535 .sigrie),
    ("cache", hintMem 9 .cache),
    ("dvp", optGpr .dvp),
    ("evp", optGpr .evp)
    ]

end Asm
