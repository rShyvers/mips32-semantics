import Semantics.Manual.Pseudocode

/-!
# Manual.Encoding — the format diagrams

One line per instruction page: the 32-bit word its format diagram describes, built from the fields
of the `Instruction` constructor (MD00086 Vol II-A Rev 6.06, the diagram at the top of each page).
The spec decodes a fetched word as the instruction whose diagram it matches
(`Manual.DecoderCorrect`, `Manual/Cycle.lean`); the model's `decode`/`encode` are not used here.

Sub-wave 7A transcribes the diagrams of the pilot instructions; `enc` is `none` for the rest until
7B (`docs/MANUAL-SPEC.md`). The encoding spaces of the coprocessors, which decide the exception for a
word that matches no diagram, are at the end.
-/

namespace Manual

/-- A field of `width` bits at position `lsb` of an instruction word (the low `width` bits of the
raw field value). -/
def fld (width lsb : Nat) (v : W32) : W32 := (v &&& ((1#32 <<< width) - 1#32)) <<< lsb

/-- `opcode | rs | rt | rd | sa | function` (R format). -/
def rFormat (op rs rt rd sa fn : W32) : W32 :=
  fld 6 26 op ||| fld 5 21 rs ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 5 6 sa ||| fld 6 0 fn

/-- `opcode | rs | rt | immediate` (I format). -/
def iFormat (op rs rt imm : W32) : W32 :=
  fld 6 26 op ||| fld 5 21 rs ||| fld 5 16 rt ||| fld 16 0 imm

/-- **The format diagram of each transcribed instruction** (MD00086 Vol II-A Rev 6.06, printed
page of the diagram):

* `ADD rd, rs, rt`: SPECIAL `000000` | rs | rt | rd | `00000` | ADD `100000` (ADD, p.33).
* `LW rt, offset(base)`: LW `100011` | base | rt | offset (LW, p.235).
* `SW rt, offset(base)`: SW `101011` | base | rt | offset (SW, p.392).
* `LWL rt, offset(base)`: LWL `100010` | base | rt | offset (LWL, p.240; image-only page, read from
  the PDF).
* `BEQ rs, rt, offset`: BEQ `000100` | rs | rt | offset (BEQ, p.72).
* `BEQL rs, rt, offset`: BEQL `010100` | rs | rt | offset (BEQL, p.73).
* `ADD.S fd, fs, ft`: COP1 `010001` | fmt | ft | fs | fd | ADD `000000` (ADD.fmt, p.34), fmt S =
  16 (`10000`; Table A.22, p.459).
* 7B S1 integer ALU (all MD00086 Vol II-A Rev 6.06, printed page of the diagram):
  SPECIAL `000000` R-format, `00000` in the unused fields: ADDU p.38 (`100001`), SUB p.388 (`100010`),
  SUBU p.390 (`100011`), AND p.44 (`100100`), OR p.314 (`100101`), XOR p.446 (`100110`), NOR p.313
  (`100111`), SLT p.378 (`101010`), SLTU p.381 (`101011`), MOVN p.279 (`001011`), MOVZ p.284 (`001010`);
  shifts: SLL p.376 (`000000`), SRL p.385 (`000010`, `R = 0` is bit 21), SRA p.383 (`000011`), SLLV p.377
  (`000100`), SRLV p.386 (`000110`, `R = 0` is bit 6), SRAV p.384 (`000111`), ROTR p.339 (SRL function,
  `R = 1`), ROTRV p.340 (SRLV function, `R = 1`); MULT p.303 (`011000`), MULTU p.304 (`011001`), DIV p.165
  (`011010`), DIVU p.171 (`011011`), MFHI p.273 (`010000`), MTHI p.297 (`010001`), MFLO p.274 (`010010`),
  MTLO p.298 (`010011`); SPECIAL2 `011100`: MUL p.299 (`000010`), MADD p.255 (`000000`), MADDU p.261
  (`000001`), MSUB p.286 (`000100`), MSUBU p.289 (`000101`), CLZ p.135 (`100000`) and CLO p.134 (`100001`)
  with `rt = rd` (their Restrictions); SPECIAL3 `011111`: SEB p.365, SEH p.366, WSBH p.445 (BSHFL `100000`
  with sub-function `10000`, `11000`, `00010`), EXT p.183 (`000000`, `msbd = size-1`, `lsb = pos`), INS
  p.192 (`000100`, `msb = pos+size-1`, `lsb = pos`); I-format: ADDI p.35 (`001000`), ADDIU p.36
  (`001001`), SLTI p.379 (`001010`), SLTIU p.380 (`001011`), ANDI p.45 (`001100`), ORI p.315 (`001101`),
  XORI p.447 (`001110`), LUI p.233 (`001111`, `rs = 00000`).
* `MTC0 rt, rd, sel`: COP0 `010000` | MT `00100` | rt | rd | `0000 0000` | sel (MTC0, p.290). -/
def enc : Instruction → Option W32
  | .add rs rt rd => some (rFormat 0#32 rs rt rd 0#32 0x20#32)
  | .lw base rt off => some (iFormat 0x23#32 base rt off)
  | .sw base rt off => some (iFormat 0x2B#32 base rt off)
  | .lwl base rt off => some (iFormat 0x22#32 base rt off)
  | .beq rs rt off => some (iFormat 0x04#32 rs rt off)
  | .beql rs rt off => some (iFormat 0x14#32 rs rt off)
  | .addS fd fs ft => some (rFormat 0x11#32 0x10#32 ft fs fd 0#32)
  | .mtc0 rt rd sel => some (fld 6 26 0x10#32 ||| fld 5 21 0x04#32 ||| fld 5 16 rt ||| fld 5 11 rd |||
      fld 3 0 sel)
  -- 7B S1 integer ALU: begin
  | .addu rs rt rd => some (rFormat 0#32 rs rt rd 0#32 0x21#32)
  | .sub rs rt rd => some (rFormat 0#32 rs rt rd 0#32 0x22#32)
  | .subu rs rt rd => some (rFormat 0#32 rs rt rd 0#32 0x23#32)
  | .and rs rt rd => some (rFormat 0#32 rs rt rd 0#32 0x24#32)
  | .or rs rt rd => some (rFormat 0#32 rs rt rd 0#32 0x25#32)
  | .xor rs rt rd => some (rFormat 0#32 rs rt rd 0#32 0x26#32)
  | .nor rs rt rd => some (rFormat 0#32 rs rt rd 0#32 0x27#32)
  | .slt rs rt rd => some (rFormat 0#32 rs rt rd 0#32 0x2A#32)
  | .sltu rs rt rd => some (rFormat 0#32 rs rt rd 0#32 0x2B#32)
  | .movn rs rt rd => some (rFormat 0#32 rs rt rd 0#32 0x0B#32)
  | .movz rs rt rd => some (rFormat 0#32 rs rt rd 0#32 0x0A#32)
  | .sll rd rt shamt => some (rFormat 0#32 0#32 rt rd shamt 0x00#32)
  | .srl rd rt shamt => some (rFormat 0#32 0#32 rt rd shamt 0x02#32)
  | .sra rd rt shamt => some (rFormat 0#32 0#32 rt rd shamt 0x03#32)
  | .sllv rd rt rs => some (rFormat 0#32 rs rt rd 0#32 0x04#32)
  | .srlv rd rt rs => some (rFormat 0#32 rs rt rd 0#32 0x06#32)
  | .srav rd rt rs => some (rFormat 0#32 rs rt rd 0#32 0x07#32)
  | .rotr rd rt sa => some (rFormat 0#32 1#32 rt rd sa 0x02#32)
  | .rotrv rd rt rs => some (rFormat 0#32 rs rt rd 1#32 0x06#32)
  | .mult rs rt => some (rFormat 0#32 rs rt 0#32 0#32 0x18#32)
  | .multu rs rt => some (rFormat 0#32 rs rt 0#32 0#32 0x19#32)
  | .div rs rt => some (rFormat 0#32 rs rt 0#32 0#32 0x1A#32)
  | .divu rs rt => some (rFormat 0#32 rs rt 0#32 0#32 0x1B#32)
  | .mfhi rd => some (rFormat 0#32 0#32 0#32 rd 0#32 0x10#32)
  | .mthi rs => some (rFormat 0#32 rs 0#32 0#32 0#32 0x11#32)
  | .mflo rd => some (rFormat 0#32 0#32 0#32 rd 0#32 0x12#32)
  | .mtlo rs => some (rFormat 0#32 rs 0#32 0#32 0#32 0x13#32)
  | .mul rs rt rd => some (rFormat 0x1C#32 rs rt rd 0#32 0x02#32)
  | .madd rs rt => some (rFormat 0x1C#32 rs rt 0#32 0#32 0x00#32)
  | .maddu rs rt => some (rFormat 0x1C#32 rs rt 0#32 0#32 0x01#32)
  | .msub rs rt => some (rFormat 0x1C#32 rs rt 0#32 0#32 0x04#32)
  | .msubu rs rt => some (rFormat 0x1C#32 rs rt 0#32 0#32 0x05#32)
  | .clz rs rd => some (rFormat 0x1C#32 rs rd rd 0#32 0x20#32)
  | .clo rs rd => some (rFormat 0x1C#32 rs rd rd 0#32 0x21#32)
  | .seb rd rt => some (rFormat 0x1F#32 0#32 rt rd 0x10#32 0x20#32)
  | .seh rd rt => some (rFormat 0x1F#32 0#32 rt rd 0x18#32 0x20#32)
  | .wsbh rd rt => some (rFormat 0x1F#32 0#32 rt rd 0x02#32 0x20#32)
  | .ext rt rs pos size => some (rFormat 0x1F#32 rs rt (size - 1#32) pos 0x00#32)
  | .ins rt rs pos size => some (rFormat 0x1F#32 rs rt (pos + size - 1#32) pos 0x04#32)
  | .addi rs rt imm => some (iFormat 0x08#32 rs rt imm)
  | .addiu rs rt imm => some (iFormat 0x09#32 rs rt imm)
  | .slti rs rt imm => some (iFormat 0x0A#32 rs rt imm)
  | .sltiu rs rt imm => some (iFormat 0x0B#32 rs rt imm)
  | .andi rs rt imm => some (iFormat 0x0C#32 rs rt imm)
  | .ori rs rt imm => some (iFormat 0x0D#32 rs rt imm)
  | .xori rs rt imm => some (iFormat 0x0E#32 rs rt imm)
  | .lui rt imm => some (iFormat 0x0F#32 0#32 rt imm)
  -- 7B S1 integer ALU: end
  | _ => none

/-- The `opcode` field (bits 31..26). -/
def opcode (w : W32) : W32 := w >>> 26

/-- **COP0 encoding space** (MD00090 Vol III Rev 6.02 §6.2.22, p.100: "A COP0 or Cache instruction"):
opcode COP0 `010000` or CACHE `101111` (MD00086 Vol II-A Rev 6.06 Table A.2 "MIPS32 Encoding of the
Opcode Field", p.451, an image-only page read from the PDF; the opcode values of the other spaces
below are from the same table). For an encoding assigned to a coprocessor "the Coprocessor Unavailable
exception takes priority over the Reserved Instruction exception" (Table A.1, p.449). -/
def InCop0Space (w : W32) : Bool := opcode w == 0x10#32 || opcode w == 0x2F#32

/-- **COP1 encoding space** (§6.2.22, p.100: "A COP1, COP1X, LWC1, SWC1, LDC1, SDC1 or MOVCI (Special
opcode function field encoding) instruction"): opcodes COP1 `010001`, COP1X `010011`, LWC1 `110001`,
SWC1 `111001`, LDC1 `110101`, SDC1 `111101`, and SPECIAL with function MOVCI `000001`. -/
def InCop1Space (w : W32) : Bool :=
  opcode w == 0x11#32 || opcode w == 0x13#32 || opcode w == 0x31#32 || opcode w == 0x39#32 ||
    opcode w == 0x35#32 || opcode w == 0x3D#32 || (opcode w == 0#32 && (w &&& 0x3F#32) == 1#32)

/-- **COP2 encoding space** (§6.2.22, p.100: "A COP2, LWC2, SWC2, LDC2, or SDC2 instruction"):
opcodes COP2 `010010`, LWC2 `110010`, SWC2 `111010`, LDC2 `110110`, SDC2 `111110`. -/
def InCop2Space (w : W32) : Bool :=
  opcode w == 0x12#32 || opcode w == 0x32#32 || opcode w == 0x3A#32 || opcode w == 0x36#32 ||
    opcode w == 0x3E#32

end Manual
