import Semantics.Asm.Int
import Semantics.Asm.Memory
import Semantics.Asm.Branch
import Semantics.Asm.System
import Semantics.Asm.Fpu
import Semantics.Asm.Pseudo

/-!
# Asm.Table — the mnemonic dispatch

The union of the family tables (`intTable`, `memoryTable`, `branchTable`, `systemTable`,
`fpuTable`), the macros and the idioms. A table-level statement (after `expandIdiom`) is either a
machine instruction (one word, `encode` of its `Instruction`) or a macro.
-/

namespace Asm

/-- Every machine-instruction mnemonic and its encoder. -/
def instrTable : EncTable :=
  intTable ++ memoryTable ++ branchTable ++ systemTable ++ fpuTable

/-- The machine-instruction mnemonics (for tests and documentation). -/
def instrMnemonics : List String := instrTable.map (·.1)

/-- Pre-Release 6 mnemonics whose instructions Release 6 removed (MD00086 Vol II-A Rev 6.06,
Table A.1, p.451: "6R"/"6Rm"); they are assembler errors with a specific message. Where Release 6
reuses a mnemonic for a new instruction (`mul`, `div`, `divu` in their three-operand forms),
the mnemonic is that instruction's (`intTable`). -/
def removedMnemonics : List String :=
  ["movn", "movz", "mult", "multu", "mfhi", "mflo", "mthi", "mtlo",  -- div, divu, mul reused
   "madd", "maddu", "msub", "msubu", "addi", "lwl", "lwr", "swl", "swr",
   "beql", "bnel", "blezl", "bgtzl", "bltzl", "bgezl", "bltzall", "bgezall", "bltzal", "bgezal",
   "teqi", "tnei", "tgei", "tgeiu", "tlti", "tltiu",
   "lwxc1", "ldxc1", "swxc1", "sdxc1", "prefx", "movf", "movt", "bc1f", "bc1t", "bc1fl", "bc1tl"] ++
  (["s", "d"].flatMap fun f =>
    ["movf.", "movt.", "movn.", "movz.", "madd.", "msub.", "nmadd.", "nmsub."].map (· ++ f) ++
    ["f", "un", "eq", "ueq", "olt", "ult", "ole", "ule",
     "sf", "ngle", "seq", "ngl", "lt", "nge", "le", "ngt"].map fun c => "c." ++ c ++ "." ++ f)

/-- Mnemonics a Release 6 assembler rejects although no table removes them, with the reason:
"Release 6: the special no-operation instruction SSNOP is deprecated: it behaves the same as a
conventional NOP ... Assemblers targeting specifically Release 6 should reject the SSNOP instruction with
an error" (MD00086 Vol II-A Rev 6.06, SSNOP, p.387). The word `sll $0, $0, 1` still executes as a
`sll` (a no-op). -/
def rejectedMnemonics : List (String × String) :=
  [("ssnop", "'ssnop': Release 6 assemblers reject SSNOP (MD00086 Vol II-A Rev 6.06, SSNOP, p.387); use 'nop' or 'ehb'")]

/-- A mnemonic this assembler accepts (instruction, macro or idiom). -/
def isKnownMnemonic (m : String) : Bool :=
  instrTable.any (·.1 == m) || macroTable.any (·.1 == m) || idiomTable.any (·.1 == m)

/-- Words emitted by one table-level statement, from its text alone (pass 1). -/
def stmtWords (m : String) (ops : List String) (line : Nat) : Except AsmError Nat :=
  match macroTable.find? (·.1 == m) with
  | some (_, mac) => mac.size ops line
  | none => pure 1

/-- The instructions of one table-level statement (pass 2). -/
def encodeStmt (c : Ctx) (ops : List String) : Except AsmError (List Instruction) :=
  match instrTable.find? (·.1 == c.name) with
  | some (_, enc) => do pure [← enc c ops]
  | none =>
    match macroTable.find? (·.1 == c.name) with
    | some (_, mac) => mac.gen c ops
    | none => throw (.unknownMnemonic s!"unknown mnemonic '{c.name}'" c.line)

/-- The error for a mnemonic no table knows. -/
def unknownMnemonicError (m : String) (line : Nat) : AsmError :=
  match rejectedMnemonics.find? (·.1 == m) with
  | some (_, msg) => .unknownMnemonic msg line
  | none =>
  if removedMnemonics.contains m then
    .unknownMnemonic s!"'{m}': the pre-Release 6 instruction is removed in Release 6 (MD00086 Vol II-A Rev 6.06, Table A.1)" line
  else .unknownMnemonic s!"unknown mnemonic '{m}'" line

end Asm
