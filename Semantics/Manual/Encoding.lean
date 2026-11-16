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

/-- 7B S2 / R6-1: `SPECIAL3 | base | rt | offset (9 bits) | 0 | function`, the Release 6 diagrams of
`LL` (p.223), `SC` (p.347) and `PREF` (p.321): offset in bits 15..7, bit 6 zero. -/
def off9Format (base rt off fn : W32) : W32 :=
  fld 6 26 0x1F#32 ||| fld 5 21 base ||| fld 5 16 rt ||| fld 9 7 off ||| fld 6 0 fn

/-- **The format diagram of each transcribed instruction** (MD00086 Vol II-A Rev 6.06, the Release 6
diagram of each page, printed page of the diagram):

* SPECIAL `000000` R-format with `00000` in the unused fields: ADD p.33 (`100000`), ADDU p.38
  (`100001`), SUB p.388 (`100010`), SUBU p.390 (`100011`), AND p.44 (`100100`), OR p.314 (`100101`),
  XOR p.446 (`100110`), NOR p.313 (`100111`), SLT p.378 (`101010`), SLTU p.381 (`101011`); shifts:
  SLL p.376 (`000000`), SRL p.385 (`000010`, `R = 0` is bit 21), SRA p.383 (`000011`), SLLV p.377
  (`000100`), SRLV p.386 (`000110`, `R = 0` is bit 6), SRAV p.384 (`000111`), ROTR p.339 (SRL
  function, `R = 1`), ROTRV p.340 (SRLV function, `R = 1`); PAUSE p.317 (`0 0 0 5 SLL`); CLZ p.135
  (`rs 00000 rd 00001 010000`) and CLO p.134 (`... 010001`), the Release 6 diagrams; JALR p.196
  (`rs 00000 rd hint=0 001001`) and JALR.HB p.198 (hint `10000`); JR is JALR with `rd = 0` in
  Release 6 (JR p.207), no diagram of its own here; SYNC p.407 (`001111`); SYSCALL p.415, BREAK p.109
  (20-bit code); the register traps TEQ p.416, TNE p.438, TLT p.434, TGE p.418, TLTU p.437, TGEU p.421
  (10-bit code).
* I-format: ADDIU p.36 (`001001`), SLTI p.379, SLTIU p.380, ANDI p.45, ORI p.315, XORI p.447, AUI p.47
  (`001111`, any `rs`; LUI is AUI with `rs = 0`, p.47); LB p.211, LH p.219, LW p.235, LBU p.213, LHU
  p.221, SB p.344, SH p.373, SW p.392; LWC1 p.236, SWC1 p.393, LDC1 p.215, SDC1 p.362; BEQ p.72, BNE
  p.103, BLEZ p.94 and BGTZ p.88 (`rt = 00000`); J p.194, JAL p.195 (26-bit `instr_index`).
* REGIMM `000001`, keyed by the `rt` field: BLTZ `00000` p.97, BGEZ `00001` p.75, NAL `10000` with
  `rs = 00000` p.306, BAL `10001` with `rs = 00000` p.50 (Release 6 diagram), SYNCI `11111` p.412.
* SPECIAL3 `011111`: SEB p.365, SEH p.366, WSBH p.445 (BSHFL `100000` with sub-function `10000`,
  `11000`, `00010`), EXT p.183 (`000000`, `msbd = size-1`, `lsb = pos`), INS p.192 (`000100`, `msb =
  pos+size-1`, `lsb = pos`), RDHWR p.332 (`00000 rt rd 00 sel 111011`), and the 9-bit-offset diagrams
  (`off9Format`) LL p.223 (`110110`), SC p.347 (`100110`), PREF p.321 (`110101`).
* COP0 `010000`: MFC0 p.266 (MF `00000` | rt | rd | `0^8` | sel), MTC0 p.290 (MT `00100`), DI p.164
  and EI p.176 (MFMC0 `01011` | rt | `01100` | 0 | sc | `00` | `000`), ERET p.177 (CO 1 | `0^19` |
  `011000`), WAIT p.442 (CO 1 | code | `100000`), RDPGPR p.335 (`01010`), WRPGPR p.444 (`01110`).
* COP1 `010001`: MFC1 p.267, MTC1 p.292, MFHC1 p.271, MTHC1 p.295, CFC1 p.129, CTC1 p.149; the
  arithmetic pages with fmt S = `10000`, D = `10001`, W = `10100` (Table A.22, p.459): ADD p.34, SUB
  p.387, MUL p.300, DIV p.170, SQRT p.382, ABS p.32, MOV p.275, NEG p.307, RECIP p.336, RSQRT p.343,
  ROUND.W p.342, TRUNC.W p.441, CEIL.W p.128, FLOOR.W p.186, CVT.W p.160, CVT.D p.153, CVT.S p.159.
  -- W5/W6: the Release 6 FPU pages (CMP.condn, SEL, MADDF, ..., the L-format conversions).
-/
def enc : Instruction → Option W32
  | .add rs rt rd => some (rFormat 0#32 rs rt rd 0#32 0x20#32)
  | .lw base rt off => some (iFormat 0x23#32 base rt off)
  | .sw base rt off => some (iFormat 0x2B#32 base rt off)
  | .beq rs rt off => some (iFormat 0x04#32 rs rt off)
  | .addS fd fs ft => some (rFormat 0x11#32 0x10#32 ft fs fd 0#32)
  | .mtc0 rt rd sel => some (fld 6 26 0x10#32 ||| fld 5 21 0x04#32 ||| fld 5 16 rt ||| fld 5 11 rd |||
      fld 3 0 sel)
  -- 7B S3 control + system
  | .bne rs rt off => some (iFormat 0x05#32 rs rt off)
  | .blez rs off => some (iFormat 0x06#32 rs 0#32 off)
  | .bgtz rs off => some (iFormat 0x07#32 rs 0#32 off)
  | .bltz rs off => some (iFormat 0x01#32 rs 0x00#32 off)
  | .bgez rs off => some (iFormat 0x01#32 rs 0x01#32 off)
  | .j target => some (fld 6 26 0x02#32 ||| fld 26 0 target)
  | .jal target => some (fld 6 26 0x03#32 ||| fld 26 0 target)
  | .jalr rs rd => some (rFormat 0#32 rs 0#32 rd 0#32 0x09#32)
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
  | .rdhwr rt rd sel => some (fld 6 26 0x1F#32 ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 3 6 sel |||
      fld 6 0 0x3B#32)
  -- end 7B S3
  -- 7B S2 memory/atomic/trap/syscall: the diagram of each page (printed page in parentheses)
  | .lb base rt off => some (iFormat 0x20#32 base rt off)            -- LB `100000` (p.211)
  | .lbu base rt off => some (iFormat 0x24#32 base rt off)           -- LBU `100100` (p.213)
  | .lh base rt off => some (iFormat 0x21#32 base rt off)            -- LH `100001` (p.219)
  | .lhu base rt off => some (iFormat 0x25#32 base rt off)           -- LHU `100101` (p.221)
  | .sb base rt off => some (iFormat 0x28#32 base rt off)            -- SB `101000` (p.344)
  | .sh base rt off => some (iFormat 0x29#32 base rt off)            -- SH `101001` (p.373)
  | .pref base hint off => some (off9Format base hint off 0x35#32)   -- SPECIAL3, PREF `110101` (p.321)
  | .sync stype => some (rFormat 0#32 0#32 0#32 0#32 stype 0x0F#32)  -- SYNC `001111` (p.407)
  | .synci base off => some (iFormat 0x01#32 base 0x1F#32 off)       -- REGIMM, SYNCI `11111` (p.412)
  | .ll base rt off => some (off9Format base rt off 0x36#32)         -- SPECIAL3, LL `110110` (p.223)
  | .sc base rt off => some (off9Format base rt off 0x26#32)         -- SPECIAL3, SC `100110` (p.347)
  | .teq rs rt code => some (trapFormat rs rt code 0x34#32)          -- TEQ `110100` (p.416)
  | .tne rs rt code => some (trapFormat rs rt code 0x36#32)          -- TNE `110110` (p.438)
  | .tlt rs rt code => some (trapFormat rs rt code 0x32#32)          -- TLT `110010` (p.434)
  | .tge rs rt code => some (trapFormat rs rt code 0x30#32)          -- TGE `110000` (p.418)
  | .tltu rs rt code => some (trapFormat rs rt code 0x33#32)         -- TLTU `110011` (p.437)
  | .tgeu rs rt code => some (trapFormat rs rt code 0x31#32)         -- TGEU `110001` (p.421)
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
  | .sll rd rt shamt => some (rFormat 0#32 0#32 rt rd shamt 0x00#32)
  | .srl rd rt shamt => some (rFormat 0#32 0#32 rt rd shamt 0x02#32)
  | .sra rd rt shamt => some (rFormat 0#32 0#32 rt rd shamt 0x03#32)
  | .sllv rd rt rs => some (rFormat 0#32 rs rt rd 0#32 0x04#32)
  | .srlv rd rt rs => some (rFormat 0#32 rs rt rd 0#32 0x06#32)
  | .srav rd rt rs => some (rFormat 0#32 rs rt rd 0#32 0x07#32)
  | .rotr rd rt sa => some (rFormat 0#32 1#32 rt rd sa 0x02#32)
  | .rotrv rd rt rs => some (rFormat 0#32 rs rt rd 1#32 0x06#32)
  | .clz rs rd => some (rFormat 0#32 rs 0#32 rd 1#32 0x10#32)
  | .clo rs rd => some (rFormat 0#32 rs 0#32 rd 1#32 0x11#32)
  | .seb rd rt => some (rFormat 0x1F#32 0#32 rt rd 0x10#32 0x20#32)
  | .seh rd rt => some (rFormat 0x1F#32 0#32 rt rd 0x18#32 0x20#32)
  | .wsbh rd rt => some (rFormat 0x1F#32 0#32 rt rd 0x02#32 0x20#32)
  | .ext rt rs pos size => some (rFormat 0x1F#32 rs rt (size - 1#32) pos 0x00#32)
  | .ins rt rs pos size => some (rFormat 0x1F#32 rs rt (pos + size - 1#32) pos 0x04#32)
  | .addiu rs rt imm => some (iFormat 0x09#32 rs rt imm)
  | .slti rs rt imm => some (iFormat 0x0A#32 rs rt imm)
  | .sltiu rs rt imm => some (iFormat 0x0B#32 rs rt imm)
  | .andi rs rt imm => some (iFormat 0x0C#32 rs rt imm)
  | .ori rs rt imm => some (iFormat 0x0D#32 rs rt imm)
  | .xori rs rt imm => some (iFormat 0x0E#32 rs rt imm)
  -- 7B S1 integer ALU: end
  -- Release 6 (wave R6-1)
  | .aui rs rt imm => some (iFormat 0x0F#32 rs rt imm)
  | .nal off => some (iFormat 0x01#32 0#32 0x10#32 off)
  | .bal off => some (iFormat 0x01#32 0#32 0x11#32 off)
  | .pause => some (rFormat 0#32 0#32 0#32 0#32 5#32 0#32)
  -- BEGIN R6-2
  -- ERETNC p.179 (CO 1 | `0^18` | 1 | `011000`)
  | .eretnc => some (fld 6 26 0x10#32 ||| fld 1 25 1#32 ||| fld 1 6 1#32 ||| fld 6 0 0x18#32)
  -- SIGRIE p.375 (REGIMM `000001` | `00000` | SIGRIE `10111` | code)
  | .sigrie code => some (iFormat 0x01#32 0#32 0x17#32 code)
  -- CACHE p.114, Release 6 diagram (SPECIAL3 | base | op | offset (9) | 0 | CACHE `100101`)
  | .cache base op off => some (off9Format base op off 0x25#32)
  -- END R6-2

/-- The `opcode` field (bits 31..26). -/
def opcode (w : W32) : W32 := w >>> 26

/-- **COP0 encoding space** (MD00090 Vol III Rev 6.02 §6.2.22, p.100: "A COP0 or Cache instruction"):
opcode COP0 `010000`, or the Release 6 CACHE, SPECIAL3 `011111` with function `100101` (MD00086 Vol
II-A Rev 6.06, CACHE, p.114; the pre-Release 6 CACHE opcode `101111` is "6Rm", Table A.2, p.451, and
signals Reserved Instruction). For an encoding assigned to a coprocessor "the unusable exception takes
priority" (Table A.1, p.451). -/
def InCop0Space (w : W32) : Bool :=
  opcode w == 0x10#32 || (opcode w == 0x1F#32 && (w &&& 0x3F#32) == 0x25#32)

/-- **COP1 encoding space** (§6.2.22, p.100: "A COP1, COP1X, LWC1, SWC1, LDC1, SDC1 or MOVCI (Special
opcode function field encoding) instruction"): opcodes COP1 `010001`, LWC1 `110001`, SWC1 `111001`,
LDC1 `110101`, SDC1 `111101`. Release 6 removed COP1X (`010011`, "6R", Table A.2, p.451) and MOVCI
(SPECIAL function `000001`, "6R", Table A.3, p.452); their words signal Reserved Instruction ("6Rm and
6R instructions signal a Reserved Instruction exception when executed by a Release 6 implementation",
Table A.1, p.451), so they are not in the space. -/
def InCop1Space (w : W32) : Bool :=
  opcode w == 0x11#32 || opcode w == 0x31#32 || opcode w == 0x39#32 || opcode w == 0x35#32 ||
    opcode w == 0x3D#32

/-- **COP2 encoding space** (§6.2.22, p.100: "A COP2, LWC2, SWC2, LDC2, or SDC2 instruction"): opcode
COP2 `010010`. Release 6 moved LWC2/SWC2/LDC2/SDC2 under COP2 ("6Rm" at their old opcodes `110010`,
`111010`, `110110`, `111110`, which Release 6 reuses for BC, BALC, POP66, POP76; Table A.2, p.451). -/
def InCop2Space (w : W32) : Bool := opcode w == 0x12#32

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
(`Manual.FetchExecute`). The cases, on the Release 6 diagrams (MD00086 Vol II-A Rev 6.06, printed
page of each diagram):

* **A nonzero unnamed field** ("Fields that contain zeros but are not named are unused fields that
  are required to be zero ... If such fields are set to non-zero values, the operation of the
  processor is UNPREDICTABLE", §2.1.1, p.12): bits 10..6 of the SPECIAL three-register ALU functions
  ADD p.33, ADDU p.38, SUB p.388, SUBU p.390, AND p.44, OR p.314, XOR p.446, NOR p.313, SLT p.378,
  SLTU p.381, SLLV p.377, SRAV p.384; bits 10..7 of SRLV/ROTRV (p.386, p.340); bits 25..21 of SLL
  p.376 and SRA p.383; bits 25..22 of SRL/ROTR (p.385, p.339); bits 20..16 of JALR p.196; bits 25..11
  of SYNC p.407; bits 20..16 of CLZ p.135 and CLO p.134 (their `sa = 00001`); bits 25..21 of SEB p.365,
  SEH p.366, WSBH p.445; bits 25..21 and 10..9 of RDHWR p.332; bit 6 of LL p.223, SC p.347, PREF p.321;
  bits 24..7 of ERET p.177 and ERETNC p.179 (bit 6 tells them apart); bit 6 of CACHE p.114; bits
  25..21 of SIGRIE p.375 (REGIMM `rt = 10111`); bits 10..3 of MFC0 p.266,
  MTC0 p.290; bits 10..6 and 4..0 of DI p.164, EI p.176; bits 10..0 of RDPGPR p.335, WRPGPR p.444;
  bits 10..0 of MFC1 p.267, MTC1 p.292, MFHC1 p.271, MTHC1 p.295, CFC1 p.129, CTC1 p.149; bits 20..16
  of the one-operand COP1 functions (SQRT p.382, ABS p.32, MOV p.275, NEG p.307, ROUND.W p.342, TRUNC.W
  p.441, CEIL.W p.128, FLOOR.W p.186, RECIP p.336, RSQRT p.343, CVT.D p.153, CVT.S p.159, CVT.W p.160).
* **`EXT` with `lsb + msbd > 31`** (p.183) and **`INS` with `lsb > msb`** (p.193).
* **A `JALR` hint other than `00000` and `10000`**: "In release 1 of the architecture, the only
  defined hint field value is 0 ... In Release 2 of the architecture, bit 10 of the hint field is
  used to encode a hazard barrier" (JALR p.196); the JALR.HB diagram (p.198) puts "Any other legal
  hint value" in bits 9..6, and no other value is defined.

The pre-Release 6 diagrams Release 6 removed (MOVN/MOVZ, the HI/LO and multiply/divide functions,
JR, MOVCI, SPECIAL2, COP1X, the branch-likely and trap-immediate encodings, BLTZAL/BGEZAL with
`rs ≠ 0`, C.cond.fmt, MOVCF.fmt) are not diagrams of this profile: their words "signal a Reserved
Instruction exception" (Table A.1, p.451; §A.4, p.461), and so are not listed here. Neither are the
primary opcodes Release 6 reuses (BLEZ/BGTZ with `rt ≠ 0`, the old LUI with `rs ≠ 0` = AUI). -/
def UnpredictableEncoding (w : W32) : Bool :=
  let op := fldOf w 31 26
  let rs := fldOf w 25 21
  let rd := fldOf w 15 11
  let sa := fldOf w 10 6
  let fn := fldOf w 5 0
  let nz (hi lo : Nat) : Bool := fldOf w hi lo != 0
  match op with
  | 0x00 =>  -- SPECIAL
    if [0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x2A, 0x2B, 0x04, 0x07].contains fn
    then nz 10 6
    else if fn == 0x06 then nz 10 7
    else if fn == 0x00 || fn == 0x03 then nz 25 21
    else if fn == 0x02 then nz 25 22
    else if fn == 0x09 then nz 20 16 || (sa != 0 && sa != 16)
    else if fn == 0x0F then nz 25 11
    else if fn == 0x10 || fn == 0x11 then sa == 1 && nz 20 16   -- CLZ, CLO
    else false
  | 0x1F =>  -- SPECIAL3
    if fn == 0x20 && [0x10, 0x18, 0x02].contains sa then nz 25 21
    else if fn == 0x00 then sa + rd > 31          -- EXT: lsb + msbd > 31
    else if fn == 0x04 then sa > rd               -- INS: lsb > msb
    else if fn == 0x3B then nz 25 21 || nz 10 9   -- RDHWR
    else if fn == 0x36 || fn == 0x26 || fn == 0x35 then nz 6 6   -- LL, SC, PREF
    -- BEGIN R6-2
    else if fn == 0x25 then nz 6 6                                 -- CACHE
    -- END R6-2
    else false
  -- BEGIN R6-2
  | 0x01 => fldOf w 20 16 == 0x17 && rs != 0                       -- SIGRIE
  -- END R6-2
  | 0x10 =>  -- COP0
    if fldOf w 25 25 == 1 then fn == 0x18 && nz 24 7   -- ERET
    else if rs == 0x00 || rs == 0x04 then nz 10 3      -- MFC0, MTC0
    else if rs == 0x0B && rd == 12 then nz 10 6 || nz 4 0   -- DI, EI
    else if rs == 0x0A || rs == 0x0E then nz 10 0      -- RDPGPR, WRPGPR
    else false
  | 0x11 =>  -- COP1
    if [0x00, 0x04, 0x03, 0x07, 0x02, 0x06].contains rs then nz 10 0
    else if rs == 0x10 || rs == 0x11 then
      if [0x04, 0x05, 0x06, 0x07, 0x0C, 0x0D, 0x0E, 0x0F, 0x15, 0x16, 0x24].contains fn then
        nz 20 16
      else if (rs == 0x10 && fn == 0x21) || (rs == 0x11 && fn == 0x20) then nz 20 16  -- CVT.D.S, CVT.S.D
      else false
    else if rs == 0x14 then (fn == 0x20 || fn == 0x21) && nz 20 16                 -- CVT.S.W, CVT.D.W
    else false
  | _ => false

end Manual
