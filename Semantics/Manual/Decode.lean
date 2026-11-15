import Semantics.Manual.Encoding

/-!
# Manual.Decode — the specification's own decoder, from the format diagrams (wave 12b)

The manual decodes an instruction word by its format diagrams: a word is the instruction whose
diagram it matches. `Manual.Decode w` is that reading, built from the diagrams `Manual.enc`
(`Manual/Encoding.lean`, one line per instruction page of MD00086 Vol II-A Rev 6.06) and not from the
model's `decode`:

* `candidates w` reads, for every instruction of the profile, its operand fields out of `w` at the
  positions its diagram gives (the same positions `enc` writes them to). It is a reading of fields
  only: whether `w` *is* that instruction is decided by the diagram alone, `enc i = some w`.
* `Decode w` is `.instr i` for the first candidate `i` whose diagram is `w`; otherwise
  `.unpredictable` when `w` matches the opcode and function fields of a diagram but holds an
  UNPREDICTABLE value in another field (`UnpredictableEncoding`: "Fields that contain zeros but are not
  named are unused fields that are required to be zero ... If such fields are set to non-zero values,
  the operation of the processor is UNPREDICTABLE", MD00086 Vol II-A Rev 6.06 §2.1.1, p.12);
  otherwise `.reserved`: the word matches no diagram of this profile, and executing it raises
  Coprocessor Unusable or Reserved Instruction by the encoding space it is in (`Manual.Undecodable`;
  "If any instruction is subsetted out based on the rules below, an attempt to execute that
  instruction must cause the appropriate exception (typically Reserved Instruction or Coprocessor
  Unusable)", MD00086 Vol II-A Rev 6.06 §3.1, p.29; Table A.1, p.449, image-only).

**What the trusted surface states about it** (proved in `Refine/DecodeDiagram.lean`):
`Decode w = .instr i → enc i = some w` (soundness: the instruction's diagram is `w`), and
`enc i = some w → ∃ j, Decode w = .instr j ∧ enc j = some w` (completeness: every word that matches a
diagram is decoded, whatever the field values the diagram names; so `candidates` cannot omit an
instruction). Hence `Decode w = .reserved` exactly when `w` matches no diagram and has no
UNPREDICTABLE field value.

**A word whose fields the manual leaves UNDEFINED or UNPREDICTABLE in the Operation** is decoded as
the instruction: `MFC0`/`MTC0` of a register coprocessor 0 does not contain ("Pre-Release 6: The
results are UNDEFINED if coprocessor 0 does not contain a register as specified by rd and sel",
MD00086 Vol II-A Rev 6.06, MFC0, p.266; MTC0, p.290) reaches `Oracle.cp0Undefined` through the
Operation (`Ops.MFC0`, `Ops.MTC0`); `EXT` with `lsb + msbd > 31` (p.183) and `INS` with `lsb > msb`
(p.193) reach `Oracle.extOutOfRange`/`insLsbAboveMsb` (`Ops.EXT`, `Ops.INS`).

**Instructions of the opcode tables outside this profile** (no constructor, so no diagram here): the
TLB instructions, which under the Fixed Mapping MMU "are no longer required and must cause a Reserved
Instruction Exception" (MD00090 Vol III Rev 6.02 §A.1.3, p.317); `CACHE` and the EJTAG instructions
`SDBBP`/`DERET`, optional and subsetted out ("EJTAG is optional and may be subsetted out", MD00086 Vol
II-A Rev 6.06 §3.1, p.31); docs/spec/SPEC-NOTES.md and MIPS-COVERAGE-GAPS.md list them. Their words
decode as `.reserved` (p.29, above).

`decodeDiagram` is the `Option` view used as the decoder of `Manual.InstructionTime` in the top
theorems (`Refine.step_eq_manual`).
-/

namespace Manual

/-- Bits `hi..lo` of an instruction word, zero-extended to a word (a field of the format diagram). -/
def fieldAt (w : W32) (hi lo : Nat) : W32 := (w.extractLsb hi lo).zeroExtend 32

/-- The result of decoding a word by the format diagrams. -/
inductive DecodeResult where
  /-- The word is the diagram of this instruction (`enc i = some w`). -/
  | instr (i : Instruction)
  /-- The word matches a diagram's opcode and function fields but holds an UNPREDICTABLE field
  value (`UnpredictableEncoding`). -/
  | unpredictable
  /-- The word matches no diagram: Coprocessor Unusable or Reserved Instruction by its encoding
  space (`Undecodable`). -/
  | reserved
  deriving DecidableEq, Repr

/-- **The operand fields of `w` read at the positions of each diagram** (`enc`, MD00086 Vol II-A Rev
6.06, the diagram of each page; the printed pages are listed at `enc`). One entry per instruction
of the profile. The positions: `rs`/`base`/`fr`/`fmt` bits 25..21, `rt`/`ft`/`index` 20..16,
`rd`/`fs` 15..11, `sa`/`fd`/`stype`/`lsb` 10..6, `immediate`/`offset` 15..0, `instr_index` 25..0,
`cc` 20..18 (MOVCI, MOVCF.fmt, BC1) or 10..8 (C.cond.fmt), `cond` 3..0, `sel` 2..0, the `code` of
SYSCALL/BREAK 25..6, of the register traps 15..6, of WAIT 24..6. `EXT` reads `msbd` (15..11) as
`size - 1` and `INS` reads `msb` (15..11) as `pos + size - 1`, inverting the arithmetic `enc` writes
(EXT p.183, INS p.192). `CLZ`/`CLO` read `rd` from 15..11; their diagram repeats it in 20..16. -/
def candidates (w : W32) : List Instruction :=
  let f := fieldAt w
  [ .add (f 25 21) (f 20 16) (f 15 11),
    .lw (f 25 21) (f 20 16) (f 15 0),
    .sw (f 25 21) (f 20 16) (f 15 0),
    .lwl (f 25 21) (f 20 16) (f 15 0),
    .beq (f 25 21) (f 20 16) (f 15 0),
    .beql (f 25 21) (f 20 16) (f 15 0),
    .addS (f 10 6) (f 15 11) (f 20 16),
    .mtc0 (f 20 16) (f 15 11) (f 2 0),
    .bne (f 25 21) (f 20 16) (f 15 0),
    .blez (f 25 21) (f 15 0),
    .bgtz (f 25 21) (f 15 0),
    .bltz (f 25 21) (f 15 0),
    .bgez (f 25 21) (f 15 0),
    .bltzal (f 25 21) (f 15 0),
    .bgezal (f 25 21) (f 15 0),
    .bnel (f 25 21) (f 20 16) (f 15 0),
    .blezl (f 25 21) (f 15 0),
    .bgtzl (f 25 21) (f 15 0),
    .bltzl (f 25 21) (f 15 0),
    .bgezl (f 25 21) (f 15 0),
    .bltzall (f 25 21) (f 15 0),
    .bgezall (f 25 21) (f 15 0),
    .j (f 25 0),
    .jal (f 25 0),
    .jr (f 25 21),
    .jalr (f 25 21) (f 15 11),
    .jrHb (f 25 21),
    .jalrHb (f 25 21) (f 15 11),
    .mfc0 (f 20 16) (f 15 11) (f 2 0),
    .di (f 20 16),
    .ei (f 20 16),
    .eret,
    .wait (f 24 6),
    .rdpgpr (f 15 11) (f 20 16),
    .wrpgpr (f 15 11) (f 20 16),
    .rdhwr (f 20 16) (f 15 11),
    .lb (f 25 21) (f 20 16) (f 15 0),
    .lbu (f 25 21) (f 20 16) (f 15 0),
    .lh (f 25 21) (f 20 16) (f 15 0),
    .lhu (f 25 21) (f 20 16) (f 15 0),
    .sb (f 25 21) (f 20 16) (f 15 0),
    .sh (f 25 21) (f 20 16) (f 15 0),
    .pref (f 25 21) (f 20 16) (f 15 0),
    .sync (f 10 6),
    .synci (f 25 21) (f 15 0),
    .ll (f 25 21) (f 20 16) (f 15 0),
    .sc (f 25 21) (f 20 16) (f 15 0),
    .lwr (f 25 21) (f 20 16) (f 15 0),
    .swl (f 25 21) (f 20 16) (f 15 0),
    .swr (f 25 21) (f 20 16) (f 15 0),
    .teq (f 25 21) (f 20 16) (f 15 6),
    .tne (f 25 21) (f 20 16) (f 15 6),
    .tlt (f 25 21) (f 20 16) (f 15 6),
    .tge (f 25 21) (f 20 16) (f 15 6),
    .tltu (f 25 21) (f 20 16) (f 15 6),
    .tgeu (f 25 21) (f 20 16) (f 15 6),
    .teqi (f 25 21) (f 15 0),
    .tnei (f 25 21) (f 15 0),
    .tgei (f 25 21) (f 15 0),
    .tgeiu (f 25 21) (f 15 0),
    .tlti (f 25 21) (f 15 0),
    .tltiu (f 25 21) (f 15 0),
    .syscall (f 25 6),
    .break (f 25 6),
    .mfc1 (f 20 16) (f 15 11),
    .mtc1 (f 20 16) (f 15 11),
    .mfhc1 (f 20 16) (f 15 11),
    .mthc1 (f 20 16) (f 15 11),
    .cfc1 (f 20 16) (f 15 11),
    .ctc1 (f 20 16) (f 15 11),
    .lwc1 (f 25 21) (f 20 16) (f 15 0),
    .swc1 (f 25 21) (f 20 16) (f 15 0),
    .ldc1 (f 25 21) (f 20 16) (f 15 0),
    .sdc1 (f 25 21) (f 20 16) (f 15 0),
    .lwxc1 (f 10 6) (f 20 16) (f 25 21),
    .ldxc1 (f 10 6) (f 20 16) (f 25 21),
    .swxc1 (f 15 11) (f 20 16) (f 25 21),
    .sdxc1 (f 15 11) (f 20 16) (f 25 21),
    .prefx (f 15 11) (f 20 16) (f 25 21),
    .subS (f 10 6) (f 15 11) (f 20 16),
    .mulS (f 10 6) (f 15 11) (f 20 16),
    .divS (f 10 6) (f 15 11) (f 20 16),
    .sqrtS (f 10 6) (f 15 11),
    .absS (f 10 6) (f 15 11),
    .movS (f 10 6) (f 15 11),
    .negS (f 10 6) (f 15 11),
    .recipS (f 10 6) (f 15 11),
    .rsqrtS (f 10 6) (f 15 11),
    .roundWS (f 10 6) (f 15 11),
    .truncWS (f 10 6) (f 15 11),
    .ceilWS (f 10 6) (f 15 11),
    .floorWS (f 10 6) (f 15 11),
    .cvtWS (f 10 6) (f 15 11),
    .addD (f 10 6) (f 15 11) (f 20 16),
    .subD (f 10 6) (f 15 11) (f 20 16),
    .mulD (f 10 6) (f 15 11) (f 20 16),
    .divD (f 10 6) (f 15 11) (f 20 16),
    .sqrtD (f 10 6) (f 15 11),
    .absD (f 10 6) (f 15 11),
    .movD (f 10 6) (f 15 11),
    .negD (f 10 6) (f 15 11),
    .recipD (f 10 6) (f 15 11),
    .rsqrtD (f 10 6) (f 15 11),
    .roundWD (f 10 6) (f 15 11),
    .truncWD (f 10 6) (f 15 11),
    .ceilWD (f 10 6) (f 15 11),
    .floorWD (f 10 6) (f 15 11),
    .cvtWD (f 10 6) (f 15 11),
    .cvtDS (f 10 6) (f 15 11),
    .cvtSW (f 10 6) (f 15 11),
    .cvtDW (f 10 6) (f 15 11),
    .cvtSD (f 10 6) (f 15 11),
    .cCondS (f 3 0) (f 10 8) (f 15 11) (f 20 16),
    .cCondD (f 3 0) (f 10 8) (f 15 11) (f 20 16),
    .movfS (f 10 6) (f 15 11) (f 20 18),
    .movtS (f 10 6) (f 15 11) (f 20 18),
    .movnS (f 10 6) (f 15 11) (f 20 16),
    .movzS (f 10 6) (f 15 11) (f 20 16),
    .movfD (f 10 6) (f 15 11) (f 20 18),
    .movtD (f 10 6) (f 15 11) (f 20 18),
    .movnD (f 10 6) (f 15 11) (f 20 16),
    .movzD (f 10 6) (f 15 11) (f 20 16),
    .movf (f 25 21) (f 20 18) (f 15 11),
    .movt (f 25 21) (f 20 18) (f 15 11),
    .maddS (f 10 6) (f 25 21) (f 15 11) (f 20 16),
    .maddD (f 10 6) (f 25 21) (f 15 11) (f 20 16),
    .msubS (f 10 6) (f 25 21) (f 15 11) (f 20 16),
    .msubD (f 10 6) (f 25 21) (f 15 11) (f 20 16),
    .nmaddS (f 10 6) (f 25 21) (f 15 11) (f 20 16),
    .nmaddD (f 10 6) (f 25 21) (f 15 11) (f 20 16),
    .nmsubS (f 10 6) (f 25 21) (f 15 11) (f 20 16),
    .nmsubD (f 10 6) (f 25 21) (f 15 11) (f 20 16),
    .bc1f (f 20 18) (f 15 0),
    .bc1t (f 20 18) (f 15 0),
    .bc1fl (f 20 18) (f 15 0),
    .bc1tl (f 20 18) (f 15 0),
    .addu (f 25 21) (f 20 16) (f 15 11),
    .sub (f 25 21) (f 20 16) (f 15 11),
    .subu (f 25 21) (f 20 16) (f 15 11),
    .and (f 25 21) (f 20 16) (f 15 11),
    .or (f 25 21) (f 20 16) (f 15 11),
    .xor (f 25 21) (f 20 16) (f 15 11),
    .nor (f 25 21) (f 20 16) (f 15 11),
    .slt (f 25 21) (f 20 16) (f 15 11),
    .sltu (f 25 21) (f 20 16) (f 15 11),
    .movn (f 25 21) (f 20 16) (f 15 11),
    .movz (f 25 21) (f 20 16) (f 15 11),
    .sll (f 15 11) (f 20 16) (f 10 6),
    .srl (f 15 11) (f 20 16) (f 10 6),
    .sra (f 15 11) (f 20 16) (f 10 6),
    .sllv (f 15 11) (f 20 16) (f 25 21),
    .srlv (f 15 11) (f 20 16) (f 25 21),
    .srav (f 15 11) (f 20 16) (f 25 21),
    .rotr (f 15 11) (f 20 16) (f 10 6),
    .rotrv (f 15 11) (f 20 16) (f 25 21),
    .mult (f 25 21) (f 20 16),
    .multu (f 25 21) (f 20 16),
    .div (f 25 21) (f 20 16),
    .divu (f 25 21) (f 20 16),
    .mfhi (f 15 11),
    .mthi (f 25 21),
    .mflo (f 15 11),
    .mtlo (f 25 21),
    .mul (f 25 21) (f 20 16) (f 15 11),
    .madd (f 25 21) (f 20 16),
    .maddu (f 25 21) (f 20 16),
    .msub (f 25 21) (f 20 16),
    .msubu (f 25 21) (f 20 16),
    .clz (f 25 21) (f 15 11),
    .clo (f 25 21) (f 15 11),
    .seb (f 15 11) (f 20 16),
    .seh (f 15 11) (f 20 16),
    .wsbh (f 15 11) (f 20 16),
    .ext (f 20 16) (f 25 21) (f 10 6) (f 15 11 + 1#32),
    .ins (f 20 16) (f 25 21) (f 10 6) (f 15 11 - f 10 6 + 1#32),
    .addi (f 25 21) (f 20 16) (f 15 0),
    .addiu (f 25 21) (f 20 16) (f 15 0),
    .slti (f 25 21) (f 20 16) (f 15 0),
    .sltiu (f 25 21) (f 20 16) (f 15 0),
    .andi (f 25 21) (f 20 16) (f 15 0),
    .ori (f 25 21) (f 20 16) (f 15 0),
    .xori (f 25 21) (f 20 16) (f 15 0),
    .lui (f 20 16) (f 15 0) ]

/-- **Decode by the format diagrams** (module doc): the instruction whose diagram `w` is; else an
UNPREDICTABLE field value; else no diagram. -/
def Decode (w : W32) : DecodeResult :=
  match (candidates w).find? (fun i => enc i == some w) with
  | some i => .instr i
  | none => if UnpredictableEncoding w then .unpredictable else .reserved

/-- The decoder of `Manual.InstructionTime` given by `Decode`: the instruction, or `none` for a word
that matches no diagram (`InstructionTime` then tells `UnpredictableEncoding` words from the others,
as `Decode` does). -/
def decodeDiagram (w : W32) : Option Instruction :=
  match Decode w with
  | .instr i => some i
  | _ => none

end Manual
