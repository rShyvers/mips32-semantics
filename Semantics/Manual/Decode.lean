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
the instruction: `EXT` with `lsb + msbd > 31` (p.183) and `INS` with `lsb > msb` (p.193) reach
`Oracle.extOutOfRange`/`insLsbAboveMsb` (`Ops.EXT`, `Ops.INS`). (`MFC0`/`MTC0` of a register
coprocessor 0 does not contain is defined in Release 6: it reads 0 or is ignored, MFC0 p.266, MTC0
p.290.)

**Instructions of the opcode tables outside this profile** (no constructor, so no diagram here): the
pre-Release 6 encodings Release 6 removed or moved ("6R"/"6Rm" in the opcode tables: "6Rm and 6R
instructions signal a Reserved Instruction exception when executed by a Release 6 implementation. If the
encoding has been used for a new instruction or coprocessor, the unusable exception takes priority",
MD00086 Vol II-A Rev 6.06 Table A.1, p.451; §A.4, p.461); the TLB instructions, which under the Fixed Mapping MMU
"are no longer required and must cause a Reserved Instruction Exception" (MD00090 Vol III Rev 6.02
§A.1.3, p.317; TLBINV/TLBINVF with `Config4.IE = 0`, DECISIONS D4); the EJTAG instructions
`SDBBP`/`DERET`, optional and subsetted out ("If EJTAG is not implemented, the EJTAG instructions
(SDBBP and DERET) can be subsetted out", MD00082 Vol I-A Rev 6.01 §2.4.1, p.31; DECISIONS D7);
docs/spec/SPEC-NOTES.md and MIPS-COVERAGE-GAPS.md list them. Their words decode as `.reserved`
(p.29, above).

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
of the profile. The positions: `rs`/`base`/`fmt` bits 25..21, `rt`/`ft`/`hint` 20..16, `rd`/`fs`
15..11, `sa`/`fd`/`stype`/`lsb` 10..6, `immediate`/`offset` 15..0, the 9-bit `offset` of the Release
6 `LL`/`SC`/`PREF` 15..7, `instr_index` 25..0, `sel` 2..0 (MFC0/MTC0) or 8..6 (RDHWR), the `code` of
SYSCALL/BREAK 25..6, of the register traps 15..6, of WAIT 24..6, the 2-bit `sa` of `LSA` and `bp` of
`ALIGN` 7..6 (LSA p.232, ALIGN p.39), the 19-bit immediate of `ADDIUPC`/`LWPC` 18..0 (p.37, p.246). `EXT` reads `msbd` (15..11) as
`size - 1` and `INS` reads `msb` (15..11) as `pos + size - 1`, inverting the arithmetic `enc` writes
(EXT p.183, INS p.192). `PAUSE` comes first: its diagram (`SPECIAL 0 0 0 5 SLL`, PAUSE p.317) is the
`SLL` diagram (p.376) with every field fixed, and the more specific diagram names the instruction
(Release 6 makes PAUSE a CTI with its own Operation, PAUSE p.317). The Release 6 compact branches
read the 26-bit `offset` of BC/BALC at 25..0 and the 21-bit `offset` of BEQZC/BNEZC at 20..0; the
compact branches sharing an opcode are separated by the constraints of their diagrams (`encIf`), so
at most one of them has the diagram `w`. R6-6B: `CMP.condn.fmt` reads `condn` at 4..0 (p.136); its
diagram holds only for the `condn` values of Table A.17 (`CmpCondnOK`). -/
def candidates (w : W32) : List Instruction :=
  let f := fieldAt w
  [ .pause,
    .add (f 25 21) (f 20 16) (f 15 11),
    .lw (f 25 21) (f 20 16) (f 15 0),
    .sw (f 25 21) (f 20 16) (f 15 0),
    .beq (f 25 21) (f 20 16) (f 15 0),
    .addS (f 10 6) (f 15 11) (f 20 16),
    .mtc0 (f 20 16) (f 15 11) (f 2 0),
    .bne (f 25 21) (f 20 16) (f 15 0),
    .blez (f 25 21) (f 15 0),
    .bgtz (f 25 21) (f 15 0),
    .bltz (f 25 21) (f 15 0),
    .bgez (f 25 21) (f 15 0),
    .j (f 25 0),
    .jal (f 25 0),
    .jalr (f 25 21) (f 15 11),
    .jalrHb (f 25 21) (f 15 11),
    .mfc0 (f 20 16) (f 15 11) (f 2 0),
    .di (f 20 16),
    .ei (f 20 16),
    .eret,
    .wait (f 24 6),
    .rdpgpr (f 15 11) (f 20 16),
    .wrpgpr (f 15 11) (f 20 16),
    .rdhwr (f 20 16) (f 15 11) (f 8 6),
    .lb (f 25 21) (f 20 16) (f 15 0),
    .lbu (f 25 21) (f 20 16) (f 15 0),
    .lh (f 25 21) (f 20 16) (f 15 0),
    .lhu (f 25 21) (f 20 16) (f 15 0),
    .sb (f 25 21) (f 20 16) (f 15 0),
    .sh (f 25 21) (f 20 16) (f 15 0),
    .pref (f 25 21) (f 20 16) (f 15 7),
    .sync (f 10 6),
    .synci (f 25 21) (f 15 0),
    .ll (f 25 21) (f 20 16) (f 15 7),
    .sc (f 25 21) (f 20 16) (f 15 7),
    .teq (f 25 21) (f 20 16) (f 15 6),
    .tne (f 25 21) (f 20 16) (f 15 6),
    .tlt (f 25 21) (f 20 16) (f 15 6),
    .tge (f 25 21) (f 20 16) (f 15 6),
    .tltu (f 25 21) (f 20 16) (f 15 6),
    .tgeu (f 25 21) (f 20 16) (f 15 6),
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
    .addu (f 25 21) (f 20 16) (f 15 11),
    .sub (f 25 21) (f 20 16) (f 15 11),
    .subu (f 25 21) (f 20 16) (f 15 11),
    .and (f 25 21) (f 20 16) (f 15 11),
    .or (f 25 21) (f 20 16) (f 15 11),
    .xor (f 25 21) (f 20 16) (f 15 11),
    .nor (f 25 21) (f 20 16) (f 15 11),
    .slt (f 25 21) (f 20 16) (f 15 11),
    .sltu (f 25 21) (f 20 16) (f 15 11),
    .sll (f 15 11) (f 20 16) (f 10 6),
    .srl (f 15 11) (f 20 16) (f 10 6),
    .sra (f 15 11) (f 20 16) (f 10 6),
    .sllv (f 15 11) (f 20 16) (f 25 21),
    .srlv (f 15 11) (f 20 16) (f 25 21),
    .srav (f 15 11) (f 20 16) (f 25 21),
    .rotr (f 15 11) (f 20 16) (f 10 6),
    .rotrv (f 15 11) (f 20 16) (f 25 21),
    .clz (f 25 21) (f 15 11),
    .clo (f 25 21) (f 15 11),
    .seb (f 15 11) (f 20 16),
    .seh (f 15 11) (f 20 16),
    .wsbh (f 15 11) (f 20 16),
    .ext (f 20 16) (f 25 21) (f 10 6) (f 15 11 + 1#32),
    .ins (f 20 16) (f 25 21) (f 10 6) (f 15 11 - f 10 6 + 1#32),
    .addiu (f 25 21) (f 20 16) (f 15 0),
    .slti (f 25 21) (f 20 16) (f 15 0),
    .sltiu (f 25 21) (f 20 16) (f 15 0),
    .andi (f 25 21) (f 20 16) (f 15 0),
    .ori (f 25 21) (f 20 16) (f 15 0),
    .xori (f 25 21) (f 20 16) (f 15 0),
    .aui (f 25 21) (f 20 16) (f 15 0),
    .nal (f 15 0),
    .bal (f 15 0),
    -- BEGIN R6-2
    .eretnc,
    .sigrie (f 15 0),
    .cache (f 25 21) (f 20 16) (f 15 7),
    -- END R6-2
    -- BEGIN R6-4
    .mul (f 25 21) (f 20 16) (f 15 11),
    .muh (f 25 21) (f 20 16) (f 15 11),
    .mulu (f 25 21) (f 20 16) (f 15 11),
    .muhu (f 25 21) (f 20 16) (f 15 11),
    .div (f 25 21) (f 20 16) (f 15 11),
    .mod (f 25 21) (f 20 16) (f 15 11),
    .divu (f 25 21) (f 20 16) (f 15 11),
    .modu (f 25 21) (f 20 16) (f 15 11),
    .seleqz (f 25 21) (f 20 16) (f 15 11),
    .selnez (f 25 21) (f 20 16) (f 15 11),
    .lsa (f 25 21) (f 20 16) (f 15 11) (f 7 6),
    .align (f 25 21) (f 20 16) (f 15 11) (f 7 6),
    .bitswap (f 15 11) (f 20 16),
    .addiupc (f 25 21) (f 18 0),
    .lwpc (f 25 21) (f 18 0),
    .auipc (f 25 21) (f 15 0),
    .aluipc (f 25 21) (f 15 0),
    -- END R6-4
    -- BEGIN R6-3
    .bc (f 25 0),
    .balc (f 25 0),
    .beqc (f 25 21) (f 20 16) (f 15 0),
    .bnec (f 25 21) (f 20 16) (f 15 0),
    .bltc (f 25 21) (f 20 16) (f 15 0),
    .bgec (f 25 21) (f 20 16) (f 15 0),
    .bltuc (f 25 21) (f 20 16) (f 15 0),
    .bgeuc (f 25 21) (f 20 16) (f 15 0),
    .blezc (f 20 16) (f 15 0),
    .bgezc (f 20 16) (f 15 0),
    .bgtzc (f 20 16) (f 15 0),
    .bltzc (f 20 16) (f 15 0),
    .beqzc (f 25 21) (f 20 0),
    .bnezc (f 25 21) (f 20 0),
    .blezalc (f 20 16) (f 15 0),
    .bgezalc (f 20 16) (f 15 0),
    .bgtzalc (f 20 16) (f 15 0),
    .bltzalc (f 20 16) (f 15 0),
    .beqzalc (f 20 16) (f 15 0),
    .bnezalc (f 20 16) (f 15 0),
    .bovc (f 25 21) (f 20 16) (f 15 0),
    .bnvc (f 25 21) (f 20 16) (f 15 0),
    .jic (f 20 16) (f 15 0),
    .jialc (f 20 16) (f 15 0),
    -- END R6-3
    -- BEGIN R6-5
    .roundLS (f 10 6) (f 15 11),
    .roundLD (f 10 6) (f 15 11),
    .truncLS (f 10 6) (f 15 11),
    .truncLD (f 10 6) (f 15 11),
    .ceilLS (f 10 6) (f 15 11),
    .ceilLD (f 10 6) (f 15 11),
    .floorLS (f 10 6) (f 15 11),
    .floorLD (f 10 6) (f 15 11),
    .cvtLS (f 10 6) (f 15 11),
    .cvtLD (f 10 6) (f 15 11),
    .cvtSL (f 10 6) (f 15 11),
    .cvtDL (f 10 6) (f 15 11),
    -- END R6-5
    -- BEGIN R6-6B
    .cmpS (f 4 0) (f 10 6) (f 15 11) (f 20 16),
    .cmpD (f 4 0) (f 10 6) (f 15 11) (f 20 16),
    .bc1eqz (f 20 16) (f 15 0),
    .bc1nez (f 20 16) (f 15 0),
    .selS (f 10 6) (f 15 11) (f 20 16),
    .selD (f 10 6) (f 15 11) (f 20 16),
    .seleqzS (f 10 6) (f 15 11) (f 20 16),
    .seleqzD (f 10 6) (f 15 11) (f 20 16),
    .selnezS (f 10 6) (f 15 11) (f 20 16),
    .selnezD (f 10 6) (f 15 11) (f 20 16),
    .maddfS (f 10 6) (f 15 11) (f 20 16),
    .maddfD (f 10 6) (f 15 11) (f 20 16),
    .msubfS (f 10 6) (f 15 11) (f 20 16),
    .msubfD (f 10 6) (f 15 11) (f 20 16),
    .rintS (f 10 6) (f 15 11),
    .rintD (f 10 6) (f 15 11),
    .classS (f 10 6) (f 15 11),
    .classD (f 10 6) (f 15 11),
    .minS (f 10 6) (f 15 11) (f 20 16),
    .minD (f 10 6) (f 15 11) (f 20 16),
    .minaS (f 10 6) (f 15 11) (f 20 16),
    .minaD (f 10 6) (f 15 11) (f 20 16),
    .maxS (f 10 6) (f 15 11) (f 20 16),
    .maxD (f 10 6) (f 15 11) (f 20 16),
    .maxaS (f 10 6) (f 15 11) (f 20 16),
    .maxaD (f 10 6) (f 15 11) (f 20 16)
    -- END R6-6B
    ]

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
