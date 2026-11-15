import Semantics.Manual.Pseudocode

/-!
# Manual.Encoding — the format diagrams

One line per instruction page: the 32-bit word its format diagram describes, built from the fields
of the `Instruction` constructor (MD00086 Vol II-A Rev 6.06, the diagram at the top of each page).
The spec decodes a fetched word as the instruction whose diagram it matches
(`Manual.DecoderSound`, `Manual/Cycle.lean`); the model's `decode`/`encode` are not used here.

Since 7B every `Instruction` constructor has a diagram line (`docs/MANUAL-SPEC.md`). The encoding spaces of the coprocessors, which decide the exception for a
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
  | .jrHb rs => some (rFormat 0#32 rs 0#32 0#32 0x10#32 0x08#32)
  | .jalrHb rs rd => some (rFormat 0#32 rs 0#32 rd 0x10#32 0x09#32)
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
  -- 7B S4 FPU
  | .mfc1 rt fs => some (rFormat 0x11#32 0x00#32 rt fs 0#32 0#32)
  | .mtc1 rt fs => some (rFormat 0x11#32 0x04#32 rt fs 0#32 0#32)
  | .mfhc1 rt fs => some (rFormat 0x11#32 0x03#32 rt fs 0#32 0#32)
  | .mthc1 rt fs => some (rFormat 0x11#32 0x07#32 rt fs 0#32 0#32)
  | .cfc1 rt fs => some (rFormat 0x11#32 0x02#32 rt fs 0#32 0#32)
  | .ctc1 rt fs => some (rFormat 0x11#32 0x06#32 rt fs 0#32 0#32)
  | .lwc1 rs ft imm => some (iFormat 0x31#32 rs ft imm)
  | .swc1 rs ft imm => some (iFormat 0x39#32 rs ft imm)
  | .ldc1 rs ft imm => some (iFormat 0x35#32 rs ft imm)
  | .sdc1 rs ft imm => some (iFormat 0x3D#32 rs ft imm)
  | .lwxc1 fd index base => some (rFormat 0x13#32 base index 0#32 fd 0x00#32)
  | .ldxc1 fd index base => some (rFormat 0x13#32 base index 0#32 fd 0x01#32)
  | .swxc1 fs index base => some (rFormat 0x13#32 base index fs 0#32 0x08#32)
  | .sdxc1 fs index base => some (rFormat 0x13#32 base index fs 0#32 0x09#32)
  | .prefx hint index base => some (rFormat 0x13#32 base index hint 0#32 0x0F#32)
  | .subS fd fs ft => some (rFormat 0x11#32 0x10#32 ft fs fd 0x01#32)
  | .mulS fd fs ft => some (rFormat 0x11#32 0x10#32 ft fs fd 0x02#32)
  | .divS fd fs ft => some (rFormat 0x11#32 0x10#32 ft fs fd 0x03#32)
  | .sqrtS fd fs => some (rFormat 0x11#32 0x10#32 0#32 fs fd 0x04#32)
  | .absS fd fs => some (rFormat 0x11#32 0x10#32 0#32 fs fd 0x05#32)
  | .movS fd fs => some (rFormat 0x11#32 0x10#32 0#32 fs fd 0x06#32)
  | .negS fd fs => some (rFormat 0x11#32 0x10#32 0#32 fs fd 0x07#32)
  | .recipS fd fs => some (rFormat 0x11#32 0x10#32 0#32 fs fd 0x15#32)
  | .rsqrtS fd fs => some (rFormat 0x11#32 0x10#32 0#32 fs fd 0x16#32)
  | .roundWS fd fs => some (rFormat 0x11#32 0x10#32 0#32 fs fd 0x0C#32)
  | .truncWS fd fs => some (rFormat 0x11#32 0x10#32 0#32 fs fd 0x0D#32)
  | .ceilWS fd fs => some (rFormat 0x11#32 0x10#32 0#32 fs fd 0x0E#32)
  | .floorWS fd fs => some (rFormat 0x11#32 0x10#32 0#32 fs fd 0x0F#32)
  | .cvtWS fd fs => some (rFormat 0x11#32 0x10#32 0#32 fs fd 0x24#32)
  | .addD fd fs ft => some (rFormat 0x11#32 0x11#32 ft fs fd 0x00#32)
  | .subD fd fs ft => some (rFormat 0x11#32 0x11#32 ft fs fd 0x01#32)
  | .mulD fd fs ft => some (rFormat 0x11#32 0x11#32 ft fs fd 0x02#32)
  | .divD fd fs ft => some (rFormat 0x11#32 0x11#32 ft fs fd 0x03#32)
  | .sqrtD fd fs => some (rFormat 0x11#32 0x11#32 0#32 fs fd 0x04#32)
  | .absD fd fs => some (rFormat 0x11#32 0x11#32 0#32 fs fd 0x05#32)
  | .movD fd fs => some (rFormat 0x11#32 0x11#32 0#32 fs fd 0x06#32)
  | .negD fd fs => some (rFormat 0x11#32 0x11#32 0#32 fs fd 0x07#32)
  | .recipD fd fs => some (rFormat 0x11#32 0x11#32 0#32 fs fd 0x15#32)
  | .rsqrtD fd fs => some (rFormat 0x11#32 0x11#32 0#32 fs fd 0x16#32)
  | .roundWD fd fs => some (rFormat 0x11#32 0x11#32 0#32 fs fd 0x0C#32)
  | .truncWD fd fs => some (rFormat 0x11#32 0x11#32 0#32 fs fd 0x0D#32)
  | .ceilWD fd fs => some (rFormat 0x11#32 0x11#32 0#32 fs fd 0x0E#32)
  | .floorWD fd fs => some (rFormat 0x11#32 0x11#32 0#32 fs fd 0x0F#32)
  | .cvtWD fd fs => some (rFormat 0x11#32 0x11#32 0#32 fs fd 0x24#32)
  | .cvtDS fd fs => some (rFormat 0x11#32 0x10#32 0#32 fs fd 0x21#32)
  | .cvtSW fd fs => some (rFormat 0x11#32 0x14#32 0#32 fs fd 0x20#32)
  | .cvtDW fd fs => some (rFormat 0x11#32 0x14#32 0#32 fs fd 0x21#32)
  | .cvtSD fd fs => some (rFormat 0x11#32 0x11#32 0#32 fs fd 0x20#32)
  | .cCondS cond cc fs ft => some (fld 6 26 0x11#32 ||| fld 5 21 0x10#32 ||| fld 5 16 ft ||| fld 5 11 fs ||| fld 3 8 cc ||| fld 2 4 3#32 ||| fld 4 0 cond)
  | .cCondD cond cc fs ft => some (fld 6 26 0x11#32 ||| fld 5 21 0x11#32 ||| fld 5 16 ft ||| fld 5 11 fs ||| fld 3 8 cc ||| fld 2 4 3#32 ||| fld 4 0 cond)
  | .movfS fd fs cc => some (fld 6 26 0x11#32 ||| fld 5 21 0x10#32 ||| fld 3 18 cc ||| fld 1 16 0#32 ||| fld 5 11 fs ||| fld 5 6 fd ||| fld 6 0 0x11#32)
  | .movtS fd fs cc => some (fld 6 26 0x11#32 ||| fld 5 21 0x10#32 ||| fld 3 18 cc ||| fld 1 16 1#32 ||| fld 5 11 fs ||| fld 5 6 fd ||| fld 6 0 0x11#32)
  | .movnS fd fs rt => some (rFormat 0x11#32 0x10#32 rt fs fd 0x13#32)
  | .movzS fd fs rt => some (rFormat 0x11#32 0x10#32 rt fs fd 0x12#32)
  | .movfD fd fs cc => some (fld 6 26 0x11#32 ||| fld 5 21 0x11#32 ||| fld 3 18 cc ||| fld 1 16 0#32 ||| fld 5 11 fs ||| fld 5 6 fd ||| fld 6 0 0x11#32)
  | .movtD fd fs cc => some (fld 6 26 0x11#32 ||| fld 5 21 0x11#32 ||| fld 3 18 cc ||| fld 1 16 1#32 ||| fld 5 11 fs ||| fld 5 6 fd ||| fld 6 0 0x11#32)
  | .movnD fd fs rt => some (rFormat 0x11#32 0x11#32 rt fs fd 0x13#32)
  | .movzD fd fs rt => some (rFormat 0x11#32 0x11#32 rt fs fd 0x12#32)
  | .movf rs cc rd => some (fld 6 26 0#32 ||| fld 5 21 rs ||| fld 3 18 cc ||| fld 1 16 0#32 ||| fld 5 11 rd ||| fld 6 0 1#32)
  | .movt rs cc rd => some (fld 6 26 0#32 ||| fld 5 21 rs ||| fld 3 18 cc ||| fld 1 16 1#32 ||| fld 5 11 rd ||| fld 6 0 1#32)
  | .maddS fd fr fs ft => some (rFormat 0x13#32 fr ft fs fd 0x20#32)
  | .maddD fd fr fs ft => some (rFormat 0x13#32 fr ft fs fd 0x21#32)
  | .msubS fd fr fs ft => some (rFormat 0x13#32 fr ft fs fd 0x28#32)
  | .msubD fd fr fs ft => some (rFormat 0x13#32 fr ft fs fd 0x29#32)
  | .nmaddS fd fr fs ft => some (rFormat 0x13#32 fr ft fs fd 0x30#32)
  | .nmaddD fd fr fs ft => some (rFormat 0x13#32 fr ft fs fd 0x31#32)
  | .nmsubS fd fr fs ft => some (rFormat 0x13#32 fr ft fs fd 0x38#32)
  | .nmsubD fd fr fs ft => some (rFormat 0x13#32 fr ft fs fd 0x39#32)
  | .bc1f cc imm => some (fld 6 26 0x11#32 ||| fld 5 21 0x08#32 ||| fld 3 18 cc ||| fld 1 17 0#32 ||| fld 1 16 0#32 ||| fld 16 0 imm)
  | .bc1t cc imm => some (fld 6 26 0x11#32 ||| fld 5 21 0x08#32 ||| fld 3 18 cc ||| fld 1 17 0#32 ||| fld 1 16 1#32 ||| fld 16 0 imm)
  | .bc1fl cc imm => some (fld 6 26 0x11#32 ||| fld 5 21 0x08#32 ||| fld 3 18 cc ||| fld 1 17 1#32 ||| fld 1 16 0#32 ||| fld 16 0 imm)
  | .bc1tl cc imm => some (fld 6 26 0x11#32 ||| fld 5 21 0x08#32 ||| fld 3 18 cc ||| fld 1 17 1#32 ||| fld 1 16 1#32 ||| fld 16 0 imm)
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

/-! ## Words with an UNPREDICTABLE field value (7R) -/

/-- Bits `hi..lo` of an instruction word, as a number. -/
def fldOf (w : W32) (hi lo : Nat) : Nat := (w.extractLsb' lo (hi + 1 - lo)).toNat

/-- **A word that matches a format diagram in its opcode and function fields but has an
UNPREDICTABLE value in another field.** With two exceptions such a word matches no `enc` image (the
`enc` lines put the defined values there), so the decoder of `Manual.DecoderSound` may return `none`
for it; it is not "a word that matches no format diagram" either. The exceptions are `EXT` with
`lsb + msbd > 31` and `INS` with `lsb > msb`: their fields `lsb`, `msbd`/`msb` are the instruction's
own operands, so such a word is an `enc` image of an `ext`/`ins` with out-of-range operands, and the
spec's decoder `Manual.Decode` returns that instruction (the Operation then reaches
`Oracle.extOutOfRange`/`insLsbAboveMsb`, wave 12b). Its outcome is `Oracle.unpredictableEncoding`
(`Manual.FetchExecute`). The cases (MD00086 Vol II-A Rev 6.06, printed page of each diagram):

* **A nonzero unnamed field** ("Fields that contain zeros but are not named are unused fields that
  are required to be zero ... If such fields are set to non-zero values, the operation of the
  processor is UNPREDICTABLE", §2.1.1, p.12): bits 10..6 of the SPECIAL three-register ALU
  functions ADD p.33, ADDU p.38, SUB p.388, SUBU p.390, AND p.44, OR p.314, XOR p.446, NOR p.313,
  SLT p.378, SLTU p.381, MOVN p.279, MOVZ p.284, SLLV p.377, SRAV p.384; bits 10..7 of SRLV/ROTRV
  (p.386, p.340); bits 25..21 of SLL p.376 and SRA p.383; bits 25..22 of SRL/ROTR (p.385, p.339);
  bits 15..6 of MULT p.303, MULTU p.304, DIV p.165, DIVU p.171; bits 25..16 and 10..6 of MFHI
  p.273, MFLO p.274; bits 20..6 of MTHI p.297, MTLO p.298; bits 20..11 of JR p.206; bits 20..16 of
  JALR p.196; bits 25..11 of SYNC p.407; bit 17 and bits 10..6 of MOVF/MOVT p.276, p.281; bits
  10..6 of MUL p.299; bits 15..6 of MADD p.255, MADDU p.261, MSUB p.286, MSUBU p.289; bits 10..6
  of CLZ p.135, CLO p.134; bits 25..21 of SEB p.365, SEH p.366, WSBH p.445; bits 25..21 and 10..6
  of RDHWR p.332; bits 25..21 of LUI p.233; bits 20..16 of BLEZ p.94, BGTZ p.88, BLEZL p.95,
  BGTZL p.89; bits 24..6 of ERET p.177; bits 10..3 of MFC0 p.266, MTC0 p.290; bits 10..6 and 4..0
  of DI p.164, EI p.176; bits 10..0 of RDPGPR p.335, WRPGPR p.444; bits 10..0 of MFC1 p.267, MTC1
  p.292, MFHC1 p.271, MTHC1 p.295, CFC1 p.129, CTC1 p.149; bits 20..16 of the one-operand COP1
  functions (SQRT p.382, ABS p.32, MOV p.275, NEG p.307, ROUND.W p.342, TRUNC.W p.441, CEIL.W
  p.128, FLOOR.W p.186, RECIP p.336, RSQRT p.343, CVT.D p.153, CVT.S p.159, CVT.W p.160); bit 17
  of MOVF.fmt p.277, MOVT.fmt p.282; bit 7 of C.cond.fmt p.110; bits 15..11 of LWXC1 p.254, LDXC1
  p.218; bits 10..6 of SWXC1 p.406, SDXC1 p.364, PREFX p.329.
* **`CLO`/`CLZ` with `rt ≠ rd`**: "The operation of the instruction is UNPREDICTABLE if the rt and rd
  fields of the instruction contain different values" (p.134, p.135).
* **`EXT` with `lsb + msbd > 31`** (p.183) and **`INS` with `lsb > msb`** (p.193).
* **A `JR`/`JALR` hint other than `00000` and `10000`**: "In release 1 of the architecture, the only
  defined hint field value is 0 ... In Release 2 of the architecture, bit 10 of the hint field is
  used to encode an instruction hazard barrier" (JR p.207; JALR p.196); the JR.HB/JALR.HB diagrams
  (p.208, p.198) put "Any other legal hint value" in bits 9..6, and no other value is defined. -/
def UnpredictableEncoding (w : W32) : Bool :=
  let op := fldOf w 31 26
  let rs := fldOf w 25 21
  let rt := fldOf w 20 16
  let rd := fldOf w 15 11
  let sa := fldOf w 10 6
  let fn := fldOf w 5 0
  let nz (hi lo : Nat) : Bool := fldOf w hi lo != 0
  match op with
  | 0x00 =>  -- SPECIAL
    if [0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x2A, 0x2B, 0x0B, 0x0A, 0x04, 0x07].contains fn
    then nz 10 6
    else if fn == 0x06 then nz 10 7
    else if fn == 0x00 || fn == 0x03 then nz 25 21
    else if fn == 0x02 then nz 25 22
    else if [0x18, 0x19, 0x1A, 0x1B].contains fn then nz 15 6
    else if fn == 0x10 || fn == 0x12 then nz 25 16 || nz 10 6
    else if fn == 0x11 || fn == 0x13 then nz 20 6
    else if fn == 0x08 then nz 20 11 || (sa != 0 && sa != 16)
    else if fn == 0x09 then nz 20 16 || (sa != 0 && sa != 16)
    else if fn == 0x0F then nz 25 11
    else if fn == 0x01 then nz 17 17 || nz 10 6
    else false
  | 0x1C =>  -- SPECIAL2
    if fn == 0x02 then nz 10 6
    else if [0x00, 0x01, 0x04, 0x05].contains fn then nz 15 6
    else if fn == 0x20 || fn == 0x21 then nz 10 6 || rt != rd
    else false
  | 0x1F =>  -- SPECIAL3
    if fn == 0x20 && [0x10, 0x18, 0x02].contains sa then nz 25 21
    else if fn == 0x00 then sa + rd > 31          -- EXT: lsb + msbd > 31
    else if fn == 0x04 then sa > rd               -- INS: lsb > msb
    else if fn == 0x3B then nz 25 21 || nz 10 6
    else false
  | 0x0F => nz 25 21                               -- LUI
  | 0x06 | 0x07 | 0x16 | 0x17 => nz 20 16          -- BLEZ, BGTZ, BLEZL, BGTZL
  | 0x10 =>  -- COP0
    if fldOf w 25 25 == 1 then fn == 0x18 && nz 24 6   -- ERET
    else if rs == 0x00 || rs == 0x04 then nz 10 3      -- MFC0, MTC0
    else if rs == 0x0B && rd == 12 then nz 10 6 || nz 4 0   -- DI, EI
    else if rs == 0x0A || rs == 0x0E then nz 10 0      -- RDPGPR, WRPGPR
    else false
  | 0x11 =>  -- COP1
    if [0x00, 0x04, 0x03, 0x07, 0x02, 0x06].contains rs then nz 10 0
    else if rs == 0x10 || rs == 0x11 then
      if fldOf w 5 4 == 3 then nz 7 7 && fldOf w 6 6 == 0   -- C.cond.fmt (A = 0)
      else if fn == 0x11 then nz 17 17                       -- MOVF.fmt, MOVT.fmt
      else if [0x04, 0x05, 0x06, 0x07, 0x0C, 0x0D, 0x0E, 0x0F, 0x15, 0x16, 0x24].contains fn then
        nz 20 16
      else if (rs == 0x10 && fn == 0x21) || (rs == 0x11 && fn == 0x20) then nz 20 16  -- CVT.D.S, CVT.S.D
      else false
    else if rs == 0x14 then (fn == 0x20 || fn == 0x21) && nz 20 16                 -- CVT.S.W, CVT.D.W
    else false
  | 0x13 =>  -- COP1X
    if fn == 0x00 || fn == 0x01 then nz 15 11
    else if [0x08, 0x09, 0x0F].contains fn then nz 10 6
    else false
  | _ => false

end Manual
