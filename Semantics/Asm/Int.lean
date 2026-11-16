import Semantics.Asm.Operands

/-!
# Asm.Int — integer arithmetic, logic, shifts, bit operations, immediates

Release 6 forms only (MD00086 Vol II-A Rev 6.06; the encodings are `encode`'s). `lui rt, imm` is
the Release 6 idiom `aui rt, $0, imm` ("In Release 6, LUI is an assembly idiom for AUI with rs=0",
AUI, p.47); it assembles to the same word as the pre-Release 6 LUI.
-/

namespace Asm

/-- `aui rt, rs, imm`: the immediate is a 16-bit pattern (0..65535) or its signed reading. -/
def auiImm (c : Ctx) (t : String) : Except AsmError W32 := immIn c "immediate" 16 (-32768) 65535 t

/-- `lui rt, imm` = `aui rt, $0, imm` (imm 0..65535). -/
def luiOp : Enc := fun c ops =>
  match ops with
  | [t, i] => do pure (.aui 0#32 (← gpr c t) (← uimm16 c i))
  | _ => badShape c "rt, imm"

/-- `rdhwr rt, rd[, sel]` (Release 6 adds `sel`, RDHWR p.332). -/
def rdhwrOp : Enc := copSel "hardware" .rdhwr

/-- Integer arithmetic, logic, shifts, bit operations and immediates. -/
def intTable : EncTable :=
  [ -- three-register arithmetic and logic: `rd, rs, rt`
    ("add",  rdRsRt fun rd rs rt => .add rs rt rd),
    ("addu", rdRsRt fun rd rs rt => .addu rs rt rd),
    ("sub",  rdRsRt fun rd rs rt => .sub rs rt rd),
    ("subu", rdRsRt fun rd rs rt => .subu rs rt rd),
    ("and",  rdRsRt fun rd rs rt => .and rs rt rd),
    ("or",   rdRsRt fun rd rs rt => .or rs rt rd),
    ("xor",  rdRsRt fun rd rs rt => .xor rs rt rd),
    ("nor",  rdRsRt fun rd rs rt => .nor rs rt rd),
    ("slt",  rdRsRt fun rd rs rt => .slt rs rt rd),
    ("sltu", rdRsRt fun rd rs rt => .sltu rs rt rd),
    -- shifts and rotates
    ("sll",   rdRtSa .sll),
    ("srl",   rdRtSa .srl),
    ("sra",   rdRtSa .sra),
    ("rotr",  rdRtSa .rotr),
    ("sllv",  rdRtRs .sllv),
    ("srlv",  rdRtRs .srlv),
    ("srav",  rdRtRs .srav),
    ("rotrv", rdRtRs .rotrv),
    -- bit operations
    ("clo",  gpr2 "rd, rs" fun rd rs => .clo rs rd),
    ("clz",  gpr2 "rd, rs" fun rd rs => .clz rs rd),
    ("seb",  gpr2 "rd, rt" .seb),
    ("seh",  gpr2 "rd, rt" .seh),
    ("wsbh", gpr2 "rd, rt" .wsbh),
    ("ext",  bitField .ext),
    ("ins",  bitField .ins),
    ("rdhwr", rdhwrOp),
    -- immediates: `rt, rs, imm`
    ("addiu", rtRsImm simm16 .addiu),
    ("slti",  rtRsImm simm16 .slti),
    ("sltiu", rtRsImm simm16 .sltiu),
    ("andi",  rtRsImm uimm16 .andi),
    ("ori",   rtRsImm uimm16 .ori),
    ("xori",  rtRsImm uimm16 .xori),
    ("aui",   rtRsImm auiImm .aui),
    ("lui",   luiOp) ]

end Asm
