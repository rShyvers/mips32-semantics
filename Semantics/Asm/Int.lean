import Semantics.Asm.Operands

/-!
# Asm.Int — integer arithmetic, logic, shifts, bit operations, immediates

Release 6 forms only (MD00086 Vol II-A Rev 6.06; the encodings are `encode`'s). The Release 6
`mul`/`div`/`divu` are the three-register forms (MUL p.300, DIV p.168); `lwpc` (a load) is here with
the other PC-relative forms. `lui rt, imm` is
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

/-- `rd, rs, rt, k` with `k` in `lo..hi`, encoded as the 2-bit field `k - lo` (`lsa`: shift 1..4, field
`sa` = shift - 1, LSA p.232; `align`: `bp` 0..3, ALIGN p.39). -/
def rdRsRtK (what : String) (lo : Int) (mk : (rs rt rd k : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [d, s, t, k] => do
      let v ← parseImmediate k c.line
      checkRange s!"{c.name} {what}" lo (lo + 3) v c.line
      pure (mk (← gpr c s) (← gpr c t) (← gpr c d) (immField 2 (v - lo)))
  | _ => badShape c s!"rd, rs, rt, {what}"

/-- `rs, offset` of `addiupc`/`lwpc` (ADDIUPC p.37, LWPC p.246): the byte offset from the
instruction's address, a multiple of 4 in -2^20 .. 2^20 - 4 (as `llvm-mc` writes it), encoded as the
19-bit field `offset >> 2`. -/
def pcRel19 (mk : (rs imm : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [s, o] => do
      let v ← parseImmediate o c.line
      checkRange s!"{c.name} offset" (-1048576) 1048572 v c.line
      if v % 4 != 0 then throw (.badImmediate s!"{c.name} offset must be a multiple of 4" c.line)
      pure (mk (← gpr c s) (immField 19 (v / 4)))
  | _ => badShape c "rs, offset"

/-- `rs, imm` of `auipc`/`aluipc` (p.48, p.43): a 16-bit pattern or its signed reading. -/
def pcRel16 (mk : (rs imm : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [s, i] => do pure (mk (← gpr c s) (← auiImm c i))
  | _ => badShape c "rs, imm"

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
    ("lui",   luiOp),
    -- Release 6 multiply/divide, select, LSA, ALIGN, BITSWAP, PC-relative
    ("mul",  rdRsRt fun rd rs rt => .mul rs rt rd),
    ("muh",  rdRsRt fun rd rs rt => .muh rs rt rd),
    ("mulu", rdRsRt fun rd rs rt => .mulu rs rt rd),
    ("muhu", rdRsRt fun rd rs rt => .muhu rs rt rd),
    ("div",  rdRsRt fun rd rs rt => .div rs rt rd),
    ("mod",  rdRsRt fun rd rs rt => .mod rs rt rd),
    ("divu", rdRsRt fun rd rs rt => .divu rs rt rd),
    ("modu", rdRsRt fun rd rs rt => .modu rs rt rd),
    ("seleqz", rdRsRt fun rd rs rt => .seleqz rs rt rd),
    ("selnez", rdRsRt fun rd rs rt => .selnez rs rt rd),
    ("lsa",   rdRsRtK "sa" 1 .lsa),
    ("align", rdRsRtK "bp" 0 .align),
    ("bitswap", gpr2 "rd, rt" .bitswap),
    ("addiupc", pcRel19 .addiupc),
    ("lwpc",    pcRel19 .lwpc),
    ("auipc",   pcRel16 .auipc),
    ("aluipc",  pcRel16 .aluipc) ]

end Asm
