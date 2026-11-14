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
