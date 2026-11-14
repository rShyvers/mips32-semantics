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

/-- 7B S2: `SPECIAL | rs | rt | code (10 bits) | function` (the trap-on-condition pages, e.g. TEQ
p.416: `000000 | rs | rt | code | 110100`). -/
def trapFormat (rs rt code fn : W32) : W32 :=
  fld 6 26 0#32 ||| fld 5 21 rs ||| fld 5 16 rt ||| fld 10 6 code ||| fld 6 0 fn

/-- 7B S2: `SPECIAL | code (20 bits) | function` (SYSCALL p.415, BREAK p.109). -/
def codeFormat (code fn : W32) : W32 := fld 6 26 0#32 ||| fld 20 6 code ||| fld 6 0 fn

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
* `MTC0 rt, rd, sel`: COP0 `010000` | MT `00100` | rt | rd | `0000 0000` | sel (MTC0, p.290).
* 7B S3 control + system (printed pages of the diagrams; opcode `000001` is REGIMM):
  BNE `000101` rs rt offset (p.103); BLEZ `000110`, BGTZ `000111` with `rt = 00000` (p.94, p.88);
  BLTZ `00000`, BGEZ `00001`, BLTZAL `10000`, BGEZAL `10001` in the REGIMM `rt` field (p.97, p.75,
  p.98, p.76); BNEL `010101`, BLEZL `010110`, BGTZL `010111` (p.104, p.95, p.89); BLTZL `00010`,
  BGEZL `00011`, BLTZALL `10010`, BGEZALL `10011` (p.101, p.86, p.99, p.80); J `000010`, JAL
  `000011` with the 26-bit `instr_index` (p.194, p.195); JR SPECIAL, `rs`, 0, hint 0, `001000` (p.206,
  pre-Release 6 diagram); JALR SPECIAL, `rs`, 0, `rd`, hint 0, `001001` (p.196, pre-Release 6
  diagram); MFC0 COP0 `010000` | MF `00000` | rt | rd | 0 | sel (p.266); DI/EI COP0 | MFMC0 `01011` |
  rt | 12 `01100` | 0 | sc (0: DI, 1: EI) | `00` | `000` (p.164, p.176); ERET COP0 | CO 1 | 0^19 |
  `011000` (p.177); WAIT COP0 | CO 1 | code (19 bits) | `100000` (p.442); RDPGPR COP0 | `01010` |
  rt | rd | 0^11 (p.335); WRPGPR COP0 | `01110` | rt | rd | 0^11 (p.444); RDHWR SPECIAL3 `011111` |
  0 | rt | rd | 0 | `111011` (p.332; the `sel` of the Release 6 diagram is zero here).
 -/
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
  -- 7B S3 control + system
  | .bne rs rt off => some (iFormat 0x05#32 rs rt off)
  | .blez rs off => some (iFormat 0x06#32 rs 0#32 off)
  | .bgtz rs off => some (iFormat 0x07#32 rs 0#32 off)
  | .bltz rs off => some (iFormat 0x01#32 rs 0x00#32 off)
  | .bgez rs off => some (iFormat 0x01#32 rs 0x01#32 off)
  | .bltzal rs off => some (iFormat 0x01#32 rs 0x10#32 off)
  | .bgezal rs off => some (iFormat 0x01#32 rs 0x11#32 off)
  | .bnel rs rt off => some (iFormat 0x15#32 rs rt off)
  | .blezl rs off => some (iFormat 0x16#32 rs 0#32 off)
  | .bgtzl rs off => some (iFormat 0x17#32 rs 0#32 off)
  | .bltzl rs off => some (iFormat 0x01#32 rs 0x02#32 off)
  | .bgezl rs off => some (iFormat 0x01#32 rs 0x03#32 off)
  | .bltzall rs off => some (iFormat 0x01#32 rs 0x12#32 off)
  | .bgezall rs off => some (iFormat 0x01#32 rs 0x13#32 off)
  | .j target => some (fld 6 26 0x02#32 ||| fld 26 0 target)
  | .jal target => some (fld 6 26 0x03#32 ||| fld 26 0 target)
  | .jr rs => some (rFormat 0#32 rs 0#32 0#32 0#32 0x08#32)
  | .jalr rs rd => some (rFormat 0#32 rs 0#32 rd 0#32 0x09#32)
  | .mfc0 rt rd sel => some (fld 6 26 0x10#32 ||| fld 5 21 0x00#32 ||| fld 5 16 rt ||| fld 5 11 rd |||
      fld 3 0 sel)
  | .di rt => some (fld 6 26 0x10#32 ||| fld 5 21 0x0B#32 ||| fld 5 16 rt ||| fld 5 11 12#32 |||
      fld 1 5 0#32)
  | .ei rt => some (fld 6 26 0x10#32 ||| fld 5 21 0x0B#32 ||| fld 5 16 rt ||| fld 5 11 12#32 |||
      fld 1 5 1#32)
  | .eret => some (fld 6 26 0x10#32 ||| fld 1 25 1#32 ||| fld 6 0 0x18#32)
  | .wait code => some (fld 6 26 0x10#32 ||| fld 1 25 1#32 ||| fld 19 6 code ||| fld 6 0 0x20#32)
  | .rdpgpr rd rt => some (fld 6 26 0x10#32 ||| fld 5 21 0x0A#32 ||| fld 5 16 rt ||| fld 5 11 rd)
  | .wrpgpr rd rt => some (fld 6 26 0x10#32 ||| fld 5 21 0x0E#32 ||| fld 5 16 rt ||| fld 5 11 rd)
  | .rdhwr rt rd => some (fld 6 26 0x1F#32 ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 6 0 0x3B#32)
  -- end 7B S3
  -- 7B S2 memory/atomic/trap/syscall: the diagram of each page (printed page in parentheses)
  | .lb base rt off => some (iFormat 0x20#32 base rt off)            -- LB `100000` (p.211)
  | .lbu base rt off => some (iFormat 0x24#32 base rt off)           -- LBU `100100` (p.213)
  | .lh base rt off => some (iFormat 0x21#32 base rt off)            -- LH `100001` (p.219)
  | .lhu base rt off => some (iFormat 0x25#32 base rt off)           -- LHU `100101` (p.221)
  | .sb base rt off => some (iFormat 0x28#32 base rt off)            -- SB `101000` (p.344)
  | .sh base rt off => some (iFormat 0x29#32 base rt off)            -- SH `101001` (p.373)
  | .pref base hint off => some (iFormat 0x33#32 base hint off)      -- PREF `110011` (p.321)
  | .sync stype => some (rFormat 0#32 0#32 0#32 0#32 stype 0x0F#32)  -- SYNC `001111` (p.407)
  | .synci base off => some (iFormat 0x01#32 base 0x1F#32 off)       -- REGIMM, SYNCI `11111` (p.412)
  | .ll base rt off => some (iFormat 0x30#32 base rt off)            -- LL `110000` (p.223)
  | .sc base rt off => some (iFormat 0x38#32 base rt off)            -- SC `111000` (p.347)
  | .lwr base rt off => some (iFormat 0x26#32 base rt off)           -- LWR `100110` (p.247)
  | .swl base rt off => some (iFormat 0x2A#32 base rt off)           -- SWL `101010` (p.397)
  | .swr base rt off => some (iFormat 0x2E#32 base rt off)           -- SWR `101110` (p.401)
  | .teq rs rt code => some (trapFormat rs rt code 0x34#32)          -- TEQ `110100` (p.416)
  | .tne rs rt code => some (trapFormat rs rt code 0x36#32)          -- TNE `110110` (p.438)
  | .tlt rs rt code => some (trapFormat rs rt code 0x32#32)          -- TLT `110010` (p.434)
  | .tge rs rt code => some (trapFormat rs rt code 0x30#32)          -- TGE `110000` (p.418)
  | .tltu rs rt code => some (trapFormat rs rt code 0x33#32)         -- TLTU `110011` (p.437)
  | .tgeu rs rt code => some (trapFormat rs rt code 0x31#32)         -- TGEU `110001` (p.421)
  | .teqi rs imm => some (iFormat 0x01#32 rs 0x0C#32 imm)            -- REGIMM, TEQI `01100` (p.417)
  | .tnei rs imm => some (iFormat 0x01#32 rs 0x0E#32 imm)            -- REGIMM, TNEI `01110` (p.439)
  | .tgei rs imm => some (iFormat 0x01#32 rs 0x08#32 imm)            -- REGIMM, TGEI `01000` (p.419)
  | .tgeiu rs imm => some (iFormat 0x01#32 rs 0x09#32 imm)           -- REGIMM, TGEIU `01001` (p.420)
  | .tlti rs imm => some (iFormat 0x01#32 rs 0x0A#32 imm)            -- REGIMM, TLTI `01010` (p.435)
  | .tltiu rs imm => some (iFormat 0x01#32 rs 0x0B#32 imm)           -- REGIMM, TLTIU `01011` (p.436)
  | .syscall code => some (codeFormat code 0x0C#32)                  -- SYSCALL `001100` (p.415)
  | .break code => some (codeFormat code 0x0D#32)                    -- BREAK `001101` (p.109)
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
