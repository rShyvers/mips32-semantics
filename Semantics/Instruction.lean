import Semantics.Word
import Semantics.Types

/-!
# Instruction — the modeled MIPS32 Release 6 instruction set, decode, and encode

Depends only on `Word` and `Types`. The encodings are those of the Release 6 format diagrams of
MD00086 Vol II-A Rev 6.06 (one page per instruction, cited per constructor) and the opcode tables of
its Appendix A (Table A.2, p.451 onwards).

**One union type, one decoder table per release.** `Instruction` has one constructor per
instruction any modeled release has; which instructions a release *has* is decided only by that
release's decoder table (`decodeFor`). Release 6 is the only release modeled (`Release`, `profile`
in `Types.lean`), so `decode = decodeFor profile.release`. The Release 6 table is written as one
function per major opcode group (`decodeSpecial`, `decodeRegimm`, `decodeSpecial3`, `decodeCop0`,
`decodeCop1`, `decodePrimary`), so a sibling table for another release can reuse or replace each.

**Removed encodings.** Every pre-Release 6 encoding Release 6 removes ("6R"/"6Rm" in Table A.2 and
the sub-tables: "6Rm and 6R instructions signal a Reserved Instruction exception when executed by a
Release 6 implementation. If the encoding has been used for a new instruction or coprocessor, the
unusable exception takes priority", MD00086 Vol II-A Rev 6.06 Table A.1, p.451) does not decode
(`step` raises Reserved Instruction, or Coprocessor Unusable in a coprocessor's space). Encodings
Release 6 reuses for instructions a later wave of this project adds are marked `-- W<n>:` at the
place they will be decoded; until then they do not decode either.

All instruction variants carry their **raw** field values as `W32`s (not yet sign/zero-extended);
`Step.lean` (`Semantics/Exec/*`) applies the extensions each instruction's semantics require. This
keeps `decode`/`encode` a pure, total, reversible bit-layout transformation.

Field-shape summary (see each constructor's docstring for details):
- R-type reg/reg/reg (`rs rt rd`): `add addu sub subu and or xor nor slt sltu`.
- R-type shift (`rd rt shamt`): `sll srl sra rotr`; variable shift (`rd rt rs`): `sllv srlv srav
  rotrv`. `pause` is `sll $0,$0,5`.
- Register jump (`rs rd`): `jalr jalrHb` (`jr`/`jr.hb` are `rd = 0`).
- Bit count (`rs rd`): `clo clz`; BSHFL (`rd rt`): `seb seh wsbh`; bit fields (`rt rs pos size`):
  `ext ins`; `rdhwr` (`rt rd sel`).
- I-type (`rs rt imm`): `addiu slti sltiu andi ori xori aui`; loads/stores `lw sw lb lbu lh lhu sh
  sb`; `ll sc` (`imm` = the 9-bit offset field); branches `beq bne` (`rs rt imm`), `blez bgtz bltz
  bgez` (`rs imm`), `nal bal` (`imm`); `synci` (`rs imm`); `pref` (`rs hint imm`, 9-bit offset).
- J-type (`target`): `j jal`.
- `syscall`/`break` (`code`, bits 25..6); register traps `teq tne tlt tge tltu tgeu` (`rs rt code`,
  bits 15..6); `sync` (`stype`).
- Coprocessor 0: `mfc0 mtc0` (`rt rd sel`), `di ei` (`rt`), `eret`, `wait` (`code`), `rdpgpr
  wrpgpr` (`rd rt`).
- Coprocessor 1 (FPU; opcode COP1 and the four FP load/stores; `fmt` S = 0x10, D = 0x11, W = 0x14):
  moves `mfc1 mtc1 mfhc1 mthc1 cfc1 ctc1` (`rt fs`); `lwc1 swc1 ldc1 sdc1` (`rs ft imm`);
  arithmetic, conversions and moves per format (`fd fs ft` / `fd fs`).
  -- W5: the FPU is still the 32-bit register model (`Status.FR = 0`, register pairs for doubles,
  -- legacy NaN encoding); Release 6 requires `FR = 1` with a 64-bit FPU (MD00082 Vol I-A Rev 6.01
  -- §6.4.1, p.84) and `FCSR.NAN2008 = ABS2008 = 1` (§6.5.4, p.92-94).
-/

/-- The modeled MIPS32 machine-instruction set: one constructor per instruction (the field-shape
summary in the module docstring groups them). Each constructor's fields are the **raw** bit-field
values extracted from the 32-bit encoding. Which constructors a release has is given by its
decoder table (`decodeFor`). -/
inductive Instruction where
  -- R-type reg/reg/reg
  /-- `$rd = $rs + $rt`, signed; traps on overflow (opcode 0, funct 0x20). -/
  | add  (rs rt rd : W32)
  /-- `$rd = $rs + $rt`, wraps (opcode 0, funct 0x21). -/
  | addu (rs rt rd : W32)
  /-- `$rd = $rs - $rt`, signed; traps on overflow (opcode 0, funct 0x22). -/
  | sub  (rs rt rd : W32)
  /-- `$rd = $rs - $rt`, wraps (opcode 0, funct 0x23). -/
  | subu (rs rt rd : W32)
  /-- `$rd = $rs & $rt` (opcode 0, funct 0x24). -/
  | and  (rs rt rd : W32)
  /-- `$rd = $rs | $rt` (opcode 0, funct 0x25). -/
  | or   (rs rt rd : W32)
  /-- `$rd = $rs ^ $rt` (opcode 0, funct 0x26). -/
  | xor  (rs rt rd : W32)
  /-- `$rd = ~($rs | $rt)` (opcode 0, funct 0x27). -/
  | nor  (rs rt rd : W32)
  /-- `$rd = ($rs < $rt) ? 1 : 0`, signed (opcode 0, funct 0x2a). -/
  | slt  (rs rt rd : W32)
  /-- `$rd = ($rs <u $rt) ? 1 : 0`, unsigned (opcode 0, funct 0x2b). -/
  | sltu (rs rt rd : W32)
  -- R-type shift (rs unused)
  /-- `$rd = $rt << shamt`, logical (opcode 0, funct 0x00). The no-op idioms `nop` (`sll $0,$0,0`),
  `ssnop` (shamt 1) and `ehb` (shamt 3) are this instruction with `rd = 0`; `sll $0,$0,5` is
  `pause` (below), not `sll`. -/
  | sll  (rd rt shamt : W32)
  /-- `PAUSE`: wait for `LLbit` to clear (MD00086 Vol II-A Rev 6.06, PAUSE, p.317: SPECIAL, `rs` =
  `rt` = `rd` = 0, `sa` = 5, funct `SLL`). A control transfer instruction for the delay-slot rule
  ("CTIs include all branches and jumps, NAL, ERET, ERETNC, DERET, WAIT, and PAUSE", p.317;
  Release 6 requires Reserved Instruction in a delay slot). -/
  | pause
  /-- `$rd = $rt >> shamt`, logical/zero-fill (opcode 0, funct 0x02). -/
  | srl  (rd rt shamt : W32)
  /-- `$rd = $rt >> shamt`, arithmetic/sign-fill (opcode 0, funct 0x03). -/
  | sra  (rd rt shamt : W32)
  -- R-type variable shift (opcode 0; shamt field unused/fixed 0). MIPS32
  -- v1.x addition: compilers emit these (not `sll`/`srl`/`sra`) whenever
  -- the shift amount is a runtime value rather than a compile-time
  -- constant (`docs/spec/MIPS-COVERAGE-GAPS.md` §3.4).
  /-- `$rd = $rt << ($rs & 0x1f)`, logical, shift amount from a register's
  low 5 bits (opcode 0, funct 0x04). MIPS32. -/
  | sllv (rd rt rs : W32)
  /-- `$rd = $rt >> ($rs & 0x1f)`, logical/zero-fill, shift amount from a
  register's low 5 bits (opcode 0, funct 0x06). MIPS32. -/
  | srlv (rd rt rs : W32)
  /-- `$rd = $rt >> ($rs & 0x1f)`, arithmetic/sign-fill, shift amount from a
  register's low 5 bits (opcode 0, funct 0x07). MIPS32. -/
  | srav (rd rt rs : W32)
  -- R-type rotate (MIPS32r2; docs/spec/MIPS-COVERAGE-GAPS.md §3.4). Real
  -- MIPS32r2 overloads `srl`'s opcode-0/funct-0x02 encoding: the `rs` field
  -- (normally unused/fixed 0 for the plain shift-by-constant format) is set
  -- to 0x01 to select rotate instead of shift. Likewise `srlv`'s
  -- opcode-0/funct-0x06 encoding is overloaded via the (normally
  -- unused/fixed 0) `shamt` field set to 0x01. These are new decode/encode
  -- branches alongside the existing `srl`/`srlv` ones, not replacements.
  /-- `$rd = $rt` rotated right by the constant `sa` (0-31) bits -- bits
  shifted off the bottom wrap around to the top, unlike `srl`'s zero-fill
  (opcode 0, funct 0x02, `rs` field = 0x01). MIPS32r2. -/
  | rotr (rd rt sa : W32)
  /-- `$rd = $rt` rotated right by `$rs & 0x1f` bits, rotate amount from a
  register's low 5 bits (opcode 0, funct 0x06, `shamt` field = 0x01).
  MIPS32r2. -/
  | rotrv (rd rt rs : W32)
  -- R-type jump register. Release 6 has one register jump, JALR: "Release 6: JR is defined to be
  -- JALR with the destination register specifier rd set to 0 ... The pre-Release 6 instruction
  -- encoding for JR is removed in Release 6" (MD00086 Vol II-A Rev 6.06, JR, p.207; JR.HB p.208).
  -- `jr rs` is the assembler idiom `jalr $0, rs` (writing GPR 0 has no effect).
  /-- `$rd = PC_next + 4` (the address of the instruction *after* the delay
  slot — same `pc + 8` link-value convention as `jal`); `PC = $rs`, after
  the usual one-instruction delay slot (opcode 0, funct 0x09; MD00086 Vol II-A Rev 6.06, JALR,
  p.196). `rd = 0` is `JR` (p.206). `rt` and hint bits 10..6 are 0. -/
  | jalr (rs rd : W32)
  /-- `JALR.HB rd, rs`: `JALR` with hazard barrier (MD00086 Vol II-A Rev 6.06, JALR.HB,
  p.198-199): SPECIAL, `rs`, `0` (bits 20..16), `rd`, hint bit 10 = 1 and bits 9..6 = 0,
  funct `001001`. Links and jumps as `jalr`; `ClearHazards()` (no architectural state in this
  model: hazards are cleared immediately). `rd = 0` is `JR.HB` (p.208). -/
  | jalrHb (rs rd : W32)
  -- Bit count. Release 6 moved CLO/CLZ from SPECIAL2 to SPECIAL with `rt = 0`, `sa = 00001`
  -- (MD00086 Vol II-A Rev 6.06, CLO p.134, CLZ p.135); the pre-Release 6 SPECIAL2 form is removed.
  /-- `$rd = ` the number of leading one bits in `$rs`, counted from the MSB
  (32 if `$rs` is all-ones) (SPECIAL, `rt` = 0, `sa` = 1, funct 0x11; CLO p.134). -/
  | clo (rs rd : W32)
  /-- `$rd = ` the number of leading zero bits in `$rs`, counted from the MSB
  (32 if `$rs` is all-zero) (SPECIAL, `rt` = 0, `sa` = 1, funct 0x10; CLZ p.135). -/
  | clz (rs rd : W32)
  -- R-type SPECIAL3 BSHFL sign-extend (MIPS32r2). `rs` is unused/fixed 0;
  -- `funct` is 0x20 for the whole BSHFL sub-op family, and the shamt-position
  -- 5-bit sub-field (not a real shift amount here) selects which one.
  /-- `$rd = sign-extend($rt[7:0])` to 32 bits (SPECIAL3 opcode 0x1f,
  funct 0x20, sub-field 0x10). MIPS32r2. -/
  | seb (rd rt : W32)
  /-- `$rd = sign-extend($rt[15:0])` to 32 bits (SPECIAL3 opcode 0x1f,
  funct 0x20, sub-field 0x18). MIPS32r2. -/
  | seh (rd rt : W32)
  /-- "Word Swap Bytes Within Halfwords": swaps the byte order *within* each
  16-bit half of `$rt` independently (byte 0 <-> 1, byte 2 <-> 3), leaving
  the two halfwords in their original word positions -- **not** a full
  32-bit byte-reverse (that needs `wsbh` followed by `rotr` by 16)
  (SPECIAL3 opcode 0x1f, funct 0x20, sub-field 0x02 -- same BSHFL funct
  family as `seb`/`seh`, distinguished by the sub-field like they are).
  MIPS32r2. -/
  | wsbh (rd rt : W32)
  -- R-type SPECIAL3 bitfield extract/insert (MIPS32r2;
  -- docs/spec/MIPS-COVERAGE-GAPS.md section 3.4). Both `pos` and `size` are
  -- small compile-time constants (0-31) encoded directly in the
  -- instruction word, not register values. Real constraint `pos + size <=
  -- 32` is architecturally UNPREDICTABLE if violated; this model makes no
  -- special case for it (SPEC-NOTES precedent: just compute what the
  -- bit masking implies). The raw encoding packs `pos` into the `shamt`
  -- field (bits 10..6) for both instructions, but the `rd`-position field
  -- (bits 15..11) differs: for `ext` it holds `size - 1` ("msbd"); for
  -- `ins` it holds `pos + size - 1` ("msb") -- these are genuinely
  -- different fields in the real MIPS32 ISA (MD00086 section 3.2), not a
  -- typo. `decode`/`encode` below do the +-1 arithmetic so `Step.lean`
  -- only ever sees the semantic `pos`/`size` pair.
  /-- `$rt = zero-extend($rs[pos+size-1 .. pos])`, extracting a `size`-bit
  field starting at bit `pos` (SPECIAL3 opcode 0x1f, funct 0x00). MIPS32r2. -/
  | ext (rt rs pos size : W32)
  /-- Inserts the low `size` bits of `$rs` into `$rt` starting at bit `pos`;
  bits of `$rt` outside `[pos+size-1 .. pos]` are left unchanged (SPECIAL3
  opcode 0x1f, funct 0x04). MIPS32r2. -/
  | ins (rt rs pos size : W32)
  -- SPECIAL3 RDHWR: read a hardware register (`HWREna`-gated).
  /-- Read Hardware Register: `$rt = HWR[rd, sel]` (SPECIAL3 opcode 0x1f, funct 0x3b, `rs` = 0,
  bits 10..9 = 0, `sel` = bits 8..6; MD00086 Vol II-A Rev 6.06, RDHWR, p.332-334: "In Release 6, a
  sel field has been added"). The model implements `rd` = 0 `CPUNum`, 1 `SYNCI_Step`, 2 `CC`
  (= `Count`), 3 `CCRes`, each with `sel = 0`; access needs Coprocessor 0 to be enabled or the
  `HWREna` bit `rd` set, otherwise (and for every other `rd`/`sel`) Reserved Instruction
  (`Step.lean`). -/
  | rdhwr (rt rd sel : W32)
  /-- `$rt = $rs + sext16(imm)`, wraps (opcode 0x09). -/
  | addiu (rs rt imm : W32)
  /-- `$rt = ($rs < sext16(imm)) ? 1 : 0`, signed (opcode 0x0a). -/
  | slti  (rs rt imm : W32)
  /-- `$rt = ($rs <u sext16(imm)) ? 1 : 0` (opcode 0x0b). -/
  | sltiu (rs rt imm : W32)
  /-- `$rt = $rs & zext16(imm)` (opcode 0x0c). -/
  | andi  (rs rt imm : W32)
  /-- `$rt = $rs | zext16(imm)` (opcode 0x0d). -/
  | ori   (rs rt imm : W32)
  /-- `$rt = $rs ^ zext16(imm)` (opcode 0x0e). -/
  | xori  (rs rt imm : W32)
  /-- `AUI rt, rs, immediate`: `$rt = $rs + (imm << 16)` (opcode 0x0f; MD00086 Vol II-A Rev 6.06,
  AUI, p.47: "GPR[rt] ← GPR[rs] + sign_extend(immediate << 16)"). "In Release 6, LUI is an
  assembly idiom for AUI with rs=0" (p.47; LUI p.233): `lui rt, imm` is `aui rt, $0, imm`. -/
  | aui   (rs rt imm : W32)
  -- BEGIN R6-4
  -- Release 6 integer instructions (MD00086 Vol II-A Rev 6.06). Same-width multiply and divide
  -- (SPECIAL, the `sa` field selects the low/high or quotient/remainder half; Table A.23, p.462).
  /-- `MUL rd, rs, rt`: `$rd = ` the low word of the signed 64-bit product (SPECIAL, `sa` = 00010,
  funct `011000` SOP30; MUL MUH MULU MUHU, p.300-301). -/
  | mul  (rs rt rd : W32)
  /-- `MUH rd, rs, rt`: `$rd = ` the high word of the signed product (`sa` = 00011, SOP30; p.300). -/
  | muh  (rs rt rd : W32)
  /-- `MULU rd, rs, rt`: the low word of the unsigned product (`sa` = 00010, SOP31 `011001`; p.300). -/
  | mulu (rs rt rd : W32)
  /-- `MUHU rd, rs, rt`: the high word of the unsigned product (`sa` = 00011, SOP31; p.300). -/
  | muhu (rs rt rd : W32)
  /-- `DIV rd, rs, rt`: the signed quotient, truncated toward zero (SPECIAL, `sa` = 00010, funct
  `011010` SOP32; DIV MOD DIVU MODU, p.168-169). A zero divisor gives an UNPREDICTABLE result
  (p.168), the oracle choice `Manual.Oracle.divByZero`. -/
  | div  (rs rt rd : W32)
  /-- `MOD rd, rs, rt`: the signed remainder, with the sign of the dividend (`sa` = 00011, SOP32;
  p.168). -/
  | mod  (rs rt rd : W32)
  /-- `DIVU rd, rs, rt`: the unsigned quotient (`sa` = 00010, SOP33 `011011`; p.168). -/
  | divu (rs rt rd : W32)
  /-- `MODU rd, rs, rt`: the unsigned remainder (`sa` = 00011, SOP33; p.168). -/
  | modu (rs rt rd : W32)
  /-- `SELEQZ rd, rs, rt`: `$rd = ($rt = 0) ? $rs : 0` (SPECIAL, `sa` = 0, funct `110101`; SELEQZ
  SELNEZ, p.369). -/
  | seleqz (rs rt rd : W32)
  /-- `SELNEZ rd, rs, rt`: `$rd = ($rt ≠ 0) ? $rs : 0` (funct `110111`; p.369). -/
  | selnez (rs rt rd : W32)
  /-- `LSA rd, rs, rt, sa+1`: `$rd = ($rs << (sa+1)) + $rt` (SPECIAL, bits 10..8 = 000, the 2-bit
  `sa` in bits 7..6, funct `000101`; LSA, p.232). `sa` is the raw 2-bit field (shift 1..4). -/
  | lsa (rs rt rd sa : W32)
  /-- `ALIGN rd, rs, rt, bp`: `$rd = ($rt << 8·bp) | ($rs >> 8·(4-bp))` (SPECIAL3, bits 10..8 =
  ALIGN `010`, the 2-bit `bp` in bits 7..6, BSHFL `100000`; ALIGN, p.39, an image page). -/
  | align (rs rt rd bp : W32)
  /-- `BITSWAP rd, rt`: the bits of each byte of `$rt` reversed (SPECIAL3, `rs` = 0, `sa` =
  BITSWAP `00000`, BSHFL; BITSWAP, p.92). -/
  | bitswap (rd rt : W32)
  /-- `ADDIUPC rs, imm`: `$rs = PC + sign_extend(imm << 2)`, `PC` the address of the ADDIUPC
  instruction (PCREL `111011`, bits 20..19 = 00, a 19-bit `imm` in bits 18..0; ADDIUPC, p.37). -/
  | addiupc (rs imm : W32)
  /-- `LWPC rs, offset`: `$rs = MEM32[PC + sign_extend(offset << 2)]` (PCREL, bits 20..19 = 01, a
  19-bit `offset`; LWPC, p.246). -/
  | lwpc (rs off : W32)
  /-- `AUIPC rs, imm`: `$rs = PC + (imm << 16)` (PCREL, bits 20..16 = 11110; AUIPC, p.48). -/
  | auipc (rs imm : W32)
  /-- `ALUIPC rs, imm`: `$rs = ~0x0FFFF & (PC + sign_extend(imm << 16))` (PCREL, bits 20..16 =
  11111; ALUIPC, p.43). -/
  | aluipc (rs imm : W32)
  -- END R6-4
  -- I-type load/store: rs = base, rt = dest/src, imm = raw offset field
  /-- `$rt = MEM32[$rs + offset]`, word-aligned (opcode 0x23). -/
  | lw  (rs rt imm : W32)
  /-- `MEM32[$rs + offset] = $rt`, word-aligned (opcode 0x2b). -/
  | sw  (rs rt imm : W32)
  /-- `$rt = sext8(MEM8[$rs + offset])` (opcode 0x20). -/
  | lb  (rs rt imm : W32)
  /-- `$rt = zext8(MEM8[$rs + offset])` (opcode 0x24). -/
  | lbu (rs rt imm : W32)
  /-- `$rt = sext16(MEM16[$rs + offset])`, halfword-aligned (opcode 0x21). -/
  | lh  (rs rt imm : W32)
  /-- `$rt = zext16(MEM16[$rs + offset])`, halfword-aligned (opcode 0x25). -/
  | lhu (rs rt imm : W32)
  /-- `MEM16[$rs + offset] = $rt[15:0]`, halfword-aligned (opcode 0x29). -/
  | sh  (rs rt imm : W32)
  /-- `MEM8[$rs + offset] = $rt[7:0]`, no alignment requirement (opcode 0x28;
  MD00086 Rev 2.50 "SB"). -/
  | sb  (rs rt imm : W32)
  /-- `$rt = MEM32[$rs + offset]`, word-aligned, and sets `State.llBit` (MD00086 Vol II-A Rev
  6.06, LL, p.223). Release 6 encoding: SPECIAL3, `base` = bits 25..21, `rt`, a **9-bit** signed
  `offset` in bits 15..7, bit 6 = 0, funct `110110`; `imm` here is that raw 9-bit field. The
  pre-Release 6 opcode 0x30 is removed. A misaligned address is always an Address Error. -/
  | ll  (rs rt imm : W32)
  /-- Conditionally `MEM32[$rs + offset] = $rt`, word-aligned, based on
  `State.llBit`: if set, performs the store and writes `1` to `$rt`;
  otherwise the store does not happen and `0` is written to `$rt`. Either
  way, clears `llBit` (MD00086 Vol II-A Rev 6.06, SC, p.347). Release 6 encoding: SPECIAL3,
  9-bit signed `offset` in bits 15..7 (`imm` is that raw field), bit 6 = 0, funct `100110`; the
  pre-Release 6 opcode 0x38 is removed. -/
  | sc  (rs rt imm : W32)
  -- I-type branch reg/reg
  /-- `if $rs == $rt then PC = PC_next + (sext16(imm) << 2)` (opcode 0x04). -/
  | beq (rs rt imm : W32)
  /-- `if $rs != $rt then PC = PC_next + (sext16(imm) << 2)` (opcode 0x05). -/
  | bne (rs rt imm : W32)
  -- I-type branch reg-only (rt unused/fixed 0)
  /-- `if $rs <= 0 then PC = PC_next + (sext16(imm) << 2)` (opcode 0x06). -/
  | blez (rs imm : W32)
  /-- `if $rs > 0 then PC = PC_next + (sext16(imm) << 2)` (opcode 0x07). -/
  | bgtz (rs imm : W32)
  -- I-type REGIMM zero-comparison branches (MIPS32 ISA; opcode 0x01). All
  -- four share this one opcode; the `rt` field (not a separate opcode)
  -- selects which instruction it is (ground truth: MD00086 Rev 2.50 §3.2,
  -- Table 3-2, p. 25; see docs/spec/INSTRUCTION-REF.md for the full
  -- citation). Same `rs, offset` field shape as `blez`/`bgtz`.
  /-- `if $rs < 0 then PC = PC_next + (sext16(imm) << 2)`, signed
  (opcode 0x01, `rt` field = 0x00 `BLTZ`). -/
  | bltz (rs imm : W32)
  /-- `if $rs >= 0 then PC = PC_next + (sext16(imm) << 2)`, signed
  (opcode 0x01, `rt` field = 0x01 `BGEZ`). -/
  | bgez (rs imm : W32)
  /-- `NAL`: `$ra = PC + 8`, a not-taken branch with a delay slot (REGIMM, `rs` = 0, `rt` field =
  0x10; MD00086 Vol II-A Rev 6.06, NAL, p.306: "NAL is considered to be a not-taken branch, with a
  delay slot"; `imm` = the ignored 16-bit offset field). Release 6 keeps only this `rs = 0` case of
  the pre-Release 6 BLTZAL ("The pre-Release 6 instruction BLTZAL when rs is not GPR[0], is removed
  in Release 6, and is required to signal a Reserved Instruction exception", p.306). -/
  | nal (imm : W32)
  /-- `BAL`: `$ra = PC + 8`, then branch to `PC_next + (sext16(imm) << 2)` after the delay slot
  (REGIMM, `rs` = 0, `rt` field = 0x11; MD00086 Vol II-A Rev 6.06, BAL, p.50). "Release 6 keeps the
  BAL special case of BGEZAL, but removes all other instances of BGEZAL. BGEZAL with rs any register
  other than GPR[0] is required to signal a Reserved Instruction exception" (p.50). -/
  | bal (imm : W32)
  -- Instruction-cache synchronize hint (real MIPS32 ISA, MIPS32r2; see
  -- `docs/spec/MIPS-COVERAGE-GAPS.md` section 3.7). Shares REGIMM's opcode 0x01
  -- with the branch/trap-immediate families above, selected the same way
  -- (by the `rt` field, here fixed to `0x1f`), but its remaining operands
  -- (`rs`, `imm`) are an address computation like `lw`/`sw`/`blez`, not a
  -- branch target or trap comparand.
  /-- Hint to flush the instruction cache at `$rs + sext16(offset)`, for
  self-modifying code / JIT compilers (opcode 0x01 REGIMM, `rt` field =
  `0x1f` `SYNCI`). This simulator has no instruction-cache model, so
  `Step.lean` computes the address (exactly like `lw`/`sw`) but never uses
  it for anything -- a documented no-op, not a silently-dropped cache
  effect. -/
  | synci (rs imm : W32)
  -- J-type
  /-- `PC = (PC_next & 0xF0000000) | (target << 2)` (opcode 0x02). -/
  | j   (target : W32)
  /-- `$ra = PC_next; PC = (PC_next & 0xF0000000) | (target << 2)` (opcode 0x03). -/
  | jal (target : W32)
  -- syscall (no fields; the syscall number lives in $v0 at execution time)
  /-- System call (opcode 0, funct 0x0c); `code` = bits 25..6, ignored by
  execution. The environment-call number is `$v0` (services 1/4/10/11). -/
  | syscall (code : W32)
  -- R-type trap-on-condition (rd, shamt unused) — real MIPS32 SPECIAL-opcode
  -- trap family. Not modeled realistically by MARS (see
  -- docs/spec/INSTRUCTION-REF.md); funct values below are the standard
  -- MIPS32 ISA encoding, cited from the real architecture, not MARS.
  /-- `if $rs == $rt then trap` (opcode 0, funct 0x34). `code` = bits 15..6, ignored by execution. -/
  | teq (rs rt code : W32)
  /-- `if $rs != $rt then trap` (opcode 0, funct 0x36). `code` = bits 15..6, ignored by execution. -/
  | tne (rs rt code : W32)
  /-- `if $rs < $rt then trap`, signed (opcode 0, funct 0x32). `code` = bits 15..6, ignored by execution. -/
  | tlt (rs rt code : W32)
  /-- `if $rs >= $rt then trap`, signed (opcode 0, funct 0x30). `code` = bits 15..6, ignored by execution. -/
  | tge (rs rt code : W32)
  /-- `if $rs <u $rt then trap`, unsigned (opcode 0, funct 0x33). `code` = bits 15..6, ignored by execution. -/
  | tltu (rs rt code : W32)
  /-- `if $rs >=u $rt then trap`, unsigned (opcode 0, funct 0x31). `code` = bits 15..6, ignored by execution. -/
  | tgeu (rs rt code : W32)
  /-- Unconditional Breakpoint exception (opcode 0, funct 0x0d); `code` =
  bits 25..6, "available for use as software parameters" (MD00086 Vol II-A
  Rev 6.06, BREAK, p.109). -/
  | break (code : W32)
  /-- Memory-ordering barrier (opcode 0, funct 0x0f); `stype` = bits 10..6.
  A no-op in this single-hart model, for every `stype`. -/
  | sync (stype : W32)
  /-- Prefetch (SPECIAL3, funct `110101`; `hint` = bits 20..16, a **9-bit** signed `offset` in
  bits 15..7 (`imm` is that raw field), bit 6 = 0; the pre-Release 6 opcode 0x33 is removed).
  "Any action, including doing nothing, is permitted"; "PREF does not cause addressing-related
  exceptions" (MD00086 Vol II-A Rev 6.06, PREF, p.321). A no-op here. -/
  | pref (rs hint imm : W32)
  -- Coprocessor 0 (opcode 0x10).
  /-- `$rt = ` CP0 register `(rd, sel)` (`rs`-field = `MF` = 0x00), for every `(rd, sel)`: a
  register the model does not implement reads 0 (Release 6, MFC0 p.266). -/
  | mfc0 (rt rd sel : W32)
  /-- CP0 register `(rd, sel) := $rt` (`rs`-field = `MT` = 0x04), through the
  register's write mask (`Step.lean`). Same scoping as `mfc0`. -/
  | mtc0 (rt rd sel : W32)
  /-- Disable interrupts: `$rt = Status; Status.IE = 0` (`rs`-field = `MFMC0`
  = 0x0b, `rd` = 12, `sc` = bit 5 = 0; MD00086 Vol II-A Rev 6.06, DI, p.164). -/
  | di (rt : W32)
  /-- Enable interrupts: `$rt = Status; Status.IE = 1` (as `di`, `sc` = 1;
  MD00086 Vol II-A Rev 6.06, EI, p.176). -/
  | ei (rt : W32)
  /-- Exception return: `PC := cp0Epc`, `Status.EXL := 0` (opcode 0x10 COP0,
  `rs`-field = `CO` = 0x10, `funct` = 0x18). No operands. Real MIPS32:
  **not** a delay-slotted instruction — it takes effect immediately, an
  architectural exception to the general branch/jump delay-slot rule (see
  `Step.lean`'s execution semantics and `docs/spec/INSTRUCTION-REF.md`). -/
  | eret
  /-- Enter standby mode (opcode 0x10 COP0, bit 25 = `CO` = 1, `funct` =
  0x20); `code` = the 19-bit implementation-dependent field, bits 24..6.
  Completes, then stops the processor until an interrupt request restarts it
  (`State.standby`; MD00086 Vol II-A Rev 6.06, WAIT, p.442). -/
  | wait (code : W32)
  /-- Read GPR from previous shadow set: `GPR[rd] ← SGPR[SRSCtl.PSS, rt]`
  (COP0, `rs`-field = `RDPGPR` = 0x0a, bits 10..0 zero; MD00086 Vol II-A
  Rev 6.06, RDPGPR, p.335, "MIPS32 Release 2"). With only the normal GPRs
  (`SRSCtl.HSS = 0`) a register move. -/
  | rdpgpr (rd rt : W32)
  /-- Write GPR to previous shadow set: `SGPR[SRSCtl.PSS, rd] ← GPR[rt]`
  (COP0, `rs`-field = `WRPGPR` = 0x0e, bits 10..0 zero; MD00086 Vol II-A
  Rev 6.06, WRPGPR, p.444, "MIPS32 Release 2"). With only the normal GPRs a
  register move. -/
  | wrpgpr (rd rt : W32)
  -- Coprocessor 1 (FPU). Citations: MD00086 Vol II-A Rev 6.06, by
  -- instruction name; semantics in `Step.lean` / `FpOps.lean`.
  /-- `$rt = FPR[fs]` raw low word (COP1, `rs` = `MF` = 0x00). -/
  | mfc1 (rt fs : W32)
  /-- `FPR[fs] = $rt` raw word (COP1, `rs` = `MT` = 0x04). -/
  | mtc1 (rt fs : W32)
  /-- `$rt = ` high word of the double in `fs`, i.e. `FPR[fs+1]` (COP1, `rs` =
  `MFH` = 0x03; Release 2). -/
  | mfhc1 (rt fs : W32)
  /-- High word of the double in `fs` (`FPR[fs+1]`) `= $rt` (COP1, `rs` =
  `MTH` = 0x07; Release 2). -/
  | mthc1 (rt fs : W32)
  /-- `$rt = FP_Control[fs]` (COP1, `rs` = `CF` = 0x02): FIR 0, FCCR 25,
  FEXR 26, FENR 28, FCSR 31. -/
  | cfc1 (rt fs : W32)
  /-- `FP_Control[fs] = $rt` (COP1, `rs` = `CT` = 0x06), then
  CheckFPException. -/
  | ctc1 (rt fs : W32)
  /-- `FPR[ft] = MEM32[$rs + sext(imm)]` (opcode 0x31). -/
  | lwc1 (rs ft imm : W32)
  /-- `MEM32[$rs + sext(imm)] = FPR[ft]` (opcode 0x39). -/
  | swc1 (rs ft imm : W32)
  /-- `{FPR[ft+1],FPR[ft]} = MEM64[$rs + sext(imm)]`, doubleword-aligned
  (opcode 0x35). -/
  | ldc1 (rs ft imm : W32)
  /-- `MEM64[$rs + sext(imm)] = {FPR[ft+1],FPR[ft]}`, doubleword-aligned
  (opcode 0x3d). -/
  | sdc1 (rs ft imm : W32)
  -- Arithmetic, single (fmt = S = 0x10).
  /-- `fd = fs + ft` (funct 0x00). -/
  | addS (fd fs ft : W32)
  /-- `fd = fs − ft` (funct 0x01). -/
  | subS (fd fs ft : W32)
  /-- `fd = fs × ft` (funct 0x02). -/
  | mulS (fd fs ft : W32)
  /-- `fd = fs / ft` (funct 0x03). -/
  | divS (fd fs ft : W32)
  /-- `fd = sqrt fs` (funct 0x04). -/
  | sqrtS (fd fs : W32)
  /-- `fd = |fs|`, arithmetic (funct 0x05). -/
  | absS (fd fs : W32)
  /-- `fd = fs`, non-arithmetic (funct 0x06). -/
  | movS (fd fs : W32)
  /-- `fd = −fs`, arithmetic (funct 0x07). -/
  | negS (fd fs : W32)
  /-- `fd = 1.0 / fs` (funct 0x15; Release 2). -/
  | recipS (fd fs : W32)
  /-- `fd = 1.0 / sqrt fs` (funct 0x16; Release 2). -/
  | rsqrtS (fd fs : W32)
  /-- Single → word, round to nearest even (funct 0x0c). -/
  | roundWS (fd fs : W32)
  /-- Single → word, round toward zero (funct 0x0d). -/
  | truncWS (fd fs : W32)
  /-- Single → word, round toward +∞ (funct 0x0e). -/
  | ceilWS (fd fs : W32)
  /-- Single → word, round toward −∞ (funct 0x0f). -/
  | floorWS (fd fs : W32)
  /-- Single → word, rounding per FCSR.RM (funct 0x24). -/
  | cvtWS (fd fs : W32)
  /-- Single → double (fmt = S, funct 0x21). -/
  | cvtDS (fd fs : W32)
  /-- Word → single, rounding per FCSR.RM (fmt = W = 0x14, funct 0x20). -/
  | cvtSW (fd fs : W32)
  /-- Word → double, exact (fmt = W, funct 0x21). -/
  | cvtDW (fd fs : W32)
  -- Arithmetic, double (fmt = D = 0x11).
  /-- `fd = fs + ft` (funct 0x00). -/
  | addD (fd fs ft : W32)
  /-- `fd = fs − ft` (funct 0x01). -/
  | subD (fd fs ft : W32)
  /-- `fd = fs × ft` (funct 0x02). -/
  | mulD (fd fs ft : W32)
  /-- `fd = fs / ft` (funct 0x03). -/
  | divD (fd fs ft : W32)
  /-- `fd = sqrt fs` (funct 0x04). -/
  | sqrtD (fd fs : W32)
  /-- `fd = |fs|`, arithmetic (funct 0x05). -/
  | absD (fd fs : W32)
  /-- `fd = fs`, non-arithmetic (funct 0x06). -/
  | movD (fd fs : W32)
  /-- `fd = −fs`, arithmetic (funct 0x07). -/
  | negD (fd fs : W32)
  /-- `fd = 1.0 / fs` (funct 0x15; Release 2). -/
  | recipD (fd fs : W32)
  /-- `fd = 1.0 / sqrt fs` (funct 0x16; Release 2). -/
  | rsqrtD (fd fs : W32)
  /-- Double → word, round to nearest even (funct 0x0c). -/
  | roundWD (fd fs : W32)
  /-- Double → word, round toward zero (funct 0x0d). -/
  | truncWD (fd fs : W32)
  /-- Double → word, round toward +∞ (funct 0x0e). -/
  | ceilWD (fd fs : W32)
  /-- Double → word, round toward −∞ (funct 0x0f). -/
  | floorWD (fd fs : W32)
  /-- Double → word, rounding per FCSR.RM (funct 0x24). -/
  | cvtWD (fd fs : W32)
  /-- Double → single, rounding per FCSR.RM (fmt = D, funct 0x20). -/
  | cvtSD (fd fs : W32)
  -- BEGIN R6-2
  /-- `ERETNC`: exception return without clearing `LLbit` (MD00086 Vol II-A Rev 6.06, ERETNC,
  p.179-180: COP0, `CO` = 1, bits 24..7 zero, bit 6 = 1, funct `ERET` = 0x18). "ERETNC is identical
  to ERET except that an ERETNC will not clear the LLbit"; required by `Config5.LLB = 1` ("ERETNC
  instruction added", MD00090 Vol III Rev 6.02 Table 9.69, p.264). A CTI. -/
  | eretnc
  /-- `SIGRIE code`: signal a Reserved Instruction exception (MD00086 Vol II-A Rev 6.06, SIGRIE,
  p.375: REGIMM, `rs` = 0, `rt` = `SIGRIE` = 0x17, 16-bit `code` in bits 15..0, "available for
  software use"). "MIPS32 Release 6"; "required as of Release 6". -/
  | sigrie (code : W32)
  /-- `CACHE op, offset(base)`: perform cache operation `op` (MD00086 Vol II-A Rev 6.06, CACHE,
  p.114-120, Release 6 diagram: SPECIAL3, `base` 25..21, `op` 20..16, 9-bit `offset` 15..7, `0` bit
  6, funct `CACHE` = 0x25). The model has no cache: "The operation of this instruction is UNDEFINED
  for any operation/cache combination that is not implemented. In Release 6, the instruction in this
  case should perform no operation" (p.119). A coprocessor-0 instruction for the usability check
  ("A COP0 or Cache instruction", MD00090 Vol III Rev 6.02 §6.2.22, p.100). -/
  | cache (base op off : W32)
  -- END R6-2
  deriving Repr, DecidableEq

/-- Extract the 6-bit opcode field (bits 31..26), zero-extended to a `W32`. -/
def opcodeOf (w : W32) : W32 := (w.extractLsb 31 26).zeroExtend 32

/-- Extract the 5-bit `rs` field (bits 25..21), zero-extended to a `W32`. -/
def rsOf (w : W32) : W32 := (w.extractLsb 25 21).zeroExtend 32

/-- Extract the 5-bit `rt` field (bits 20..16), zero-extended to a `W32`. -/
def rtOf (w : W32) : W32 := (w.extractLsb 20 16).zeroExtend 32

/-- Extract the 5-bit `rd` field (bits 15..11), zero-extended to a `W32`. -/
def rdOf (w : W32) : W32 := (w.extractLsb 15 11).zeroExtend 32

/-- Extract the 5-bit `shamt` field (bits 10..6), zero-extended to a `W32`. -/
def shamtOf (w : W32) : W32 := (w.extractLsb 10 6).zeroExtend 32

/-- Extract the 6-bit `funct` field (bits 5..0), zero-extended to a `W32`. -/
def functOf (w : W32) : W32 := (w.extractLsb 5 0).zeroExtend 32

/-- Extract the raw 16-bit immediate/offset field (bits 15..0), zero-extended
to a `W32` with no sign interpretation applied. -/
def immOf (w : W32) : W32 := (w.extractLsb 15 0).zeroExtend 32

/-- Extract the raw 26-bit jump-target field (bits 25..0), zero-extended to a `W32`. -/
def targetOf (w : W32) : W32 := (w.extractLsb 25 0).zeroExtend 32

/-- Extract the `CO` bit (25) of a COP0 word. -/
def coOf (w : W32) : W32 := (w.extractLsb 25 25).zeroExtend 32

/-- Extract the 20-bit `code` field of `syscall`/`break` (bits 25..6). -/
def code20Of (w : W32) : W32 := (w.extractLsb 25 6).zeroExtend 32

/-- Extract the 10-bit `code` field of the register traps (bits 15..6). -/
def code10Of (w : W32) : W32 := (w.extractLsb 15 6).zeroExtend 32

/-- Extract the 19-bit `code` field of `wait` (bits 24..6). -/
def code19Of (w : W32) : W32 := (w.extractLsb 24 6).zeroExtend 32

/-- Extract the 9-bit `offset` field of the Release 6 SPECIAL3 `LL`/`SC`/`PREF` (bits 15..7; LL
p.223, SC p.347, PREF p.321), raw (not sign-extended). -/
def off9Of (w : W32) : W32 := (w.extractLsb 15 7).zeroExtend 32

/-- Extract bit 6 (the `0` bit between the 9-bit offset and the function field of `LL`/`SC`/
`PREF`). -/
def bit6Of (w : W32) : W32 := (w.extractLsb 6 6).zeroExtend 32

/-- `syscall`/`break` word: SPECIAL, 20-bit `code` in bits 25..6, `funct`. -/
def mkCode20 (code funct : W32) : W32 := field 20 6 code ||| field 6 0 funct

/-- Register-trap word: SPECIAL, `rs`, `rt`, 10-bit `code` in bits 15..6,
`funct`. -/
def mkTrap (rs rt code funct : W32) : W32 :=
  field 5 21 rs ||| field 5 16 rt ||| field 10 6 code ||| field 6 0 funct

/-- `wait`-shaped word: `opcode` (COP0 = 0x10), `co` (bit 25, = 1), 19-bit
`code` in bits 24..6, `funct` (0x20). -/
def mkWait (opcode co code funct : W32) : W32 :=
  field 6 26 opcode ||| field 1 25 co ||| field 19 6 code ||| field 6 0 funct

/-- The fields of a Release 6 SPECIAL3 word with a 9-bit offset (`LL`, `SC`, `PREF`; the opcode
SPECIAL3 = 0x1f is or-ed in by `encode`): `base` 25..21, `rt` 20..16, `offset` 15..7, `0` 6,
`funct` 5..0. -/
def mkOff9 (base rt off funct : W32) : W32 :=
  field 5 21 base ||| field 5 16 rt ||| field 9 7 off ||| field 6 0 funct

-- BEGIN R6-4
/-- Extract bits 10..8 (the fixed sub-field of `LSA` and `ALIGN` above their 2-bit `sa`/`bp`). -/
def sa3Of (w : W32) : W32 := (w.extractLsb 10 8).zeroExtend 32

/-- Extract bits 7..6 (the 2-bit `sa` of `LSA`, `bp` of `ALIGN`). -/
def sa2Of (w : W32) : W32 := (w.extractLsb 7 6).zeroExtend 32

/-- Extract bits 20..19 (the PCREL minor opcode of `ADDIUPC`/`LWPC`, Table A.13, p.455). -/
def pcrelOf (w : W32) : W32 := (w.extractLsb 20 19).zeroExtend 32

/-- Extract the 19-bit immediate/offset of `ADDIUPC`/`LWPC` (bits 18..0), raw. -/
def imm19Of (w : W32) : W32 := (w.extractLsb 18 0).zeroExtend 32

/-- An R-format word whose `sa` field is split into a 3-bit sub-opcode (bits 10..8) and a 2-bit
operand (bits 7..6): `LSA` (p.232) and `ALIGN` (p.39). The opcode is or-ed in by `encode`. -/
def mkRT2 (rs rt rd hi lo funct : W32) : W32 :=
  field 5 21 rs ||| field 5 16 rt ||| field 5 11 rd ||| field 3 8 hi ||| field 2 6 lo ||| field 6 0 funct

/-- The fields of `ADDIUPC`/`LWPC` (p.37, p.246): `rs` 25..21, minor opcode 20..19, 19-bit
immediate 18..0. The opcode PCREL = 0x3b is or-ed in by `encode`. -/
def mkPc19 (rs sub imm : W32) : W32 :=
  field 5 21 rs ||| field 2 19 sub ||| field 19 0 imm
-- END R6-4

/-- `decodeIf c i` is `some i` when the must-be-zero check `c` holds, `none`
otherwise. Used by the decoder tables to reject non-canonical encodings. -/
def decodeIf (c : Bool) (i : Instruction) : Option Instruction :=
  if c then some i else none

/-! ## The Release 6 decoder table

One function per major opcode group, each a table keyed by the field the manual's opcode tables
key it by (MD00086 Vol II-A Rev 6.06 Appendix A). **Strict decoding**: every field an encoding fixes
(to zero or another constant) is checked, so `encode i = w` whenever `decode w = some i`
(`Refine/Decode.lean`, `encode_of_decode`). Encodings the manual calls UNPREDICTABLE are rejected
too: `ext` with `lsb + msbd > 31`, `ins` with `msb < lsb`. -/

/-- **SPECIAL** (opcode 0), keyed by `funct` (Table A.3, p.452). Release 6 removed MOVCI (0x01),
JR (0x08: JR is JALR with `rd = 0`, JR p.207), MOVZ/MOVN (0x0a/0x0b), MFHI/MTHI/MFLO/MTLO
(0x10-0x13 with `sa = 0`) and MULT/MULTU/DIV/DIVU (0x18-0x1b with `sa = 0`); those words do not
decode. Release 6 additions: funct 0x05 LSA (bits 10..8 zero, LSA p.232); 0x18-0x1b with `sa` =
00010/00011: MUL/MUH, MULU/MUHU, DIV/MOD, DIVU/MODU (Table A.23, p.462; `sa` = 0 is the removed
HI/LO form, other `sa` values are unassigned); 0x35 SELEQZ, 0x37 SELNEZ (p.369).
SDBBP (funct 0x0e in Release 6, SDBBP p.361) belongs to EJTAG, which is absent (DECISIONS D5): "If
EJTAG is not implemented, the EJTAG instructions (SDBBP and DERET) can be subsetted out" (MD00082
Vol I-A Rev 6.01 §2.4.1, p.31), so its word does not decode (Reserved Instruction, DECISIONS D7). -/
def decodeSpecial (w : W32) : Option Instruction :=
  let rs := rsOf w
  let rt := rtOf w
  let rd := rdOf w
  let shamt := shamtOf w
  let z (x : W32) : Bool := x == 0#32
  match (functOf w).toNat with
  | 0x20 => decodeIf (z shamt) (.add rs rt rd)
  | 0x21 => decodeIf (z shamt) (.addu rs rt rd)
  | 0x22 => decodeIf (z shamt) (.sub rs rt rd)
  | 0x23 => decodeIf (z shamt) (.subu rs rt rd)
  | 0x24 => decodeIf (z shamt) (.and rs rt rd)
  | 0x25 => decodeIf (z shamt) (.or rs rt rd)
  | 0x26 => decodeIf (z shamt) (.xor rs rt rd)
  | 0x27 => decodeIf (z shamt) (.nor rs rt rd)
  | 0x2a => decodeIf (z shamt) (.slt rs rt rd)
  | 0x2b => decodeIf (z shamt) (.sltu rs rt rd)
  -- funct 0x00: `sll`; `sll $0,$0,5` is PAUSE (PAUSE p.317).
  | 0x00 =>
    if z rt && z rd && shamt == 5#32 then decodeIf (z rs) .pause
    else decodeIf (z rs) (.sll rd rt shamt)
  -- funct 0x02: bits 25..22 must be zero; bit 21 (`R`) selects `rotr` over `srl`.
  | 0x02 =>
    match rs.toNat with
    | 0 => some (.srl rd rt shamt)
    | 1 => some (.rotr rd rt shamt)
    | _ => none
  | 0x03 => decodeIf (z rs) (.sra rd rt shamt)
  | 0x04 => decodeIf (z shamt) (.sllv rd rt rs)
  -- funct 0x06: bits 10..7 must be zero; bit 6 (`R`) selects `rotrv` over `srlv`.
  | 0x06 =>
    match shamt.toNat with
    | 0 => some (.srlv rd rt rs)
    | 1 => some (.rotrv rd rt rs)
    | _ => none
  | 0x07 => decodeIf (z shamt) (.srav rd rt rs)
  -- `jalr`: the `hint` field (bits 10..6) is 0, or `10000` for the hazard-barrier form (JALR p.196,
  -- JALR.HB p.198); any other hint value does not decode.
  | 0x09 =>
    if shamt == 0#32 then decodeIf (z rt) (.jalr rs rd)
    else decodeIf (shamt == 16#32 && z rt) (.jalrHb rs rd)
  -- CLZ/CLO (Release 6): `rt = 0`, `sa = 00001` (CLZ p.135, CLO p.134).
  | 0x10 => decodeIf (z rt && shamt == 1#32) (.clz rs rd)
  | 0x11 => decodeIf (z rt && shamt == 1#32) (.clo rs rd)
  -- `syscall`/`break`: bits 25..6 are the `code` field.
  | 0x0c => some (.syscall (code20Of w))
  | 0x0d => some (.break (code20Of w))
  -- `sync`: bits 25..11 must be zero; bits 10..6 are `stype`.
  | 0x0f => decodeIf (z rs && z rt && z rd) (.sync shamt)
  -- Traps: bits 15..6 are the `code` field.
  | 0x34 => some (.teq rs rt (code10Of w))
  | 0x36 => some (.tne rs rt (code10Of w))
  | 0x32 => some (.tlt rs rt (code10Of w))
  | 0x30 => some (.tge rs rt (code10Of w))
  | 0x33 => some (.tltu rs rt (code10Of w))
  | 0x31 => some (.tgeu rs rt (code10Of w))
  -- BEGIN R6-4
  -- MUL/MUH, MULU/MUHU, DIV/MOD, DIVU/MODU: `sa` 00010 / 00011 selects (Table A.23, p.462).
  | 0x18 => if shamt == 2#32 then some (.mul rs rt rd) else decodeIf (shamt == 3#32) (.muh rs rt rd)
  | 0x19 => if shamt == 2#32 then some (.mulu rs rt rd) else decodeIf (shamt == 3#32) (.muhu rs rt rd)
  | 0x1a => if shamt == 2#32 then some (.div rs rt rd) else decodeIf (shamt == 3#32) (.mod rs rt rd)
  | 0x1b => if shamt == 2#32 then some (.divu rs rt rd) else decodeIf (shamt == 3#32) (.modu rs rt rd)
  | 0x35 => decodeIf (z shamt) (.seleqz rs rt rd)
  | 0x37 => decodeIf (z shamt) (.selnez rs rt rd)
  -- LSA: bits 10..8 zero, the 2-bit `sa` in bits 7..6 (LSA p.232).
  | 0x05 => decodeIf (z (sa3Of w)) (.lsa rs rt rd (sa2Of w))
  -- END R6-4
  | _ => none

/-- **REGIMM** (opcode 1), keyed by `rt` (Table A.4, p.452). Release 6 keeps BLTZ, BGEZ, SYNCI and
the `rs = 0` cases of BLTZAL/BGEZAL as NAL/BAL (NAL p.306, BAL p.50); BLTZAL/BGEZAL with `rs ≠ 0`,
the branch-likely forms (rt 0x02, 0x03, 0x12, 0x13) and the trap-immediate forms (0x08-0x0e) are
removed and do not decode. Release 6 adds SIGRIE (`rt` = 0x17, `rs` = 0; SIGRIE p.375). -/
def decodeRegimm (w : W32) : Option Instruction :=
  let rs := rsOf w
  let imm := immOf w
  match (rtOf w).toNat with
  | 0x00 => some (.bltz rs imm)
  | 0x01 => some (.bgez rs imm)
  | 0x10 => decodeIf (rs == 0#32) (.nal imm)
  | 0x11 => decodeIf (rs == 0#32) (.bal imm)
  | 0x1f => some (.synci rs imm)
  -- BEGIN R6-2
  | 0x17 => decodeIf (rs == 0#32) (.sigrie imm)
  -- END R6-2
  | _ => none

/-- **SPECIAL3** (opcode 0x1f), keyed by `funct` (Table A.6, p.453; BSHFL Table A.10, p.454).
Release 6 moved `LL` (0x36), `SC` (0x26) and `PREF` (0x35) here, with a 9-bit offset. Release 6
adds BSHFL `sa` = 00000 BITSWAP (p.92) and `sa` = 010 bp ALIGN (p.39).
Release 6 recoded CACHE here (funct 0x25, 9-bit offset; CACHE p.114). -/
def decodeSpecial3 (w : W32) : Option Instruction :=
  let rs := rsOf w
  let rt := rtOf w
  let rd := rdOf w
  let shamt := shamtOf w
  let z (x : W32) : Bool := x == 0#32
  match (functOf w).toNat with
  | 0x20 =>  -- BSHFL: `rs` must be zero; the `sa` sub-field selects
    -- BEGIN R6-4
    -- ALIGN: bits 10..8 = 010, `bp` in bits 7..6, any `rs` (ALIGN p.39).
    if sa3Of w == 2#32 then some (.align rs rt rd (sa2Of w)) else
    -- END R6-4
    match shamt.toNat with
    | 0x10 => decodeIf (z rs) (.seb rd rt)
    | 0x18 => decodeIf (z rs) (.seh rd rt)
    | 0x02 => decodeIf (z rs) (.wsbh rd rt)
    -- BEGIN R6-4
    | 0x00 => decodeIf (z rs) (.bitswap rd rt)  -- BITSWAP (p.92)
    -- END R6-4
    | _ => none
  -- `ext`: the `rd` field holds `msbd = size - 1`, `shamt` holds `lsb = pos`;
  -- `lsb + msbd > 31` is UNPREDICTABLE and rejected.
  | 0x00 => decodeIf (decide (shamt.toNat + rd.toNat ≤ 31)) (.ext rt rs shamt (rd + 1#32))
  -- `ins`: the `rd` field holds `msb = pos + size - 1`; `msb < lsb` is
  -- UNPREDICTABLE and rejected.
  | 0x04 => decodeIf (decide (shamt.toNat ≤ rd.toNat)) (.ins rt rs shamt (rd - shamt + 1#32))
  -- `rdhwr`: `rs` and bits 10..9 must be zero; bits 8..6 are `sel` (RDHWR p.332).
  | 0x3b => decodeIf (z rs && decide (shamt.toNat < 8)) (.rdhwr rt rd shamt)
  -- `ll`/`sc`/`pref`: 9-bit offset in bits 15..7, bit 6 zero (LL p.223, SC p.347, PREF p.321).
  | 0x36 => decodeIf (z (bit6Of w)) (.ll rs rt (off9Of w))
  | 0x26 => decodeIf (z (bit6Of w)) (.sc rs rt (off9Of w))
  | 0x35 => decodeIf (z (bit6Of w)) (.pref rs rt (off9Of w))
  -- BEGIN R6-2
  -- `cache`: 9-bit offset in bits 15..7, bit 6 zero, `op` in bits 20..16 (CACHE p.114).
  | 0x25 => decodeIf (z (bit6Of w)) (.cache rs rt (off9Of w))
  -- END R6-2
  | _ => none

/-- **COP0** (opcode 0x10), keyed by bit 25 (`CO`) and then `funct`, else by `rs` (Tables A.11-A.13,
p.455). The TLB instructions (no TLB: "must cause a Reserved Instruction Exception", MD00090 Vol III
Rev 6.02 §A.1.3, p.317; TLBINV/TLBINVF with `Config4.IE = 0`, DECISIONS D4) and DERET (EJTAG absent:
"If EJTAG is not implemented, the EJTAG instructions (SDBBP and DERET) can be subsetted out",
MD00082 Vol I-A Rev 6.01 §2.4.1, p.31) do not decode. `mfc0`/`mtc0` decode for every `(rd, sel)`:
"Release 6: Reading a reserved register or a register that is not implemented for the current core
configuration returns 0" (MD00086 Vol II-A Rev 6.06, MFC0, p.266), writes to one "are ignored"
(MTC0, p.290). -/
def decodeCop0 (w : W32) : Option Instruction :=
  let rs := rsOf w
  let rt := rtOf w
  let rd := rdOf w
  let shamt := shamtOf w
  let z (x : W32) : Bool := x == 0#32
  -- CO sub-format: bit 25 set. `eret` requires bits 24..6 zero (`eretnc`: bit 6 one); `wait`'s
  -- bits 24..6 are its implementation-dependent `code` field.
  if coOf w == 1#32 then
    match (functOf w).toNat with
    | 0x18 =>
      -- BEGIN R6-2
      if shamt == 1#32 then decodeIf (rs == 16#32 && z rt && z rd) .eretnc else
      -- END R6-2
      decodeIf (rs == 16#32 && z rt && z rd && z shamt) .eret
    | 0x20 => some (.wait (code19Of w))
    | _ => none
  else
  match rs.toNat with
  -- `mfc0`/`mtc0`: bits 10..3 must be zero, bits 2..0 are `sel` (any register: Release 6).
  | 0x00 => decodeIf (z shamt && decide ((functOf w).toNat < 8)) (.mfc0 rt rd (functOf w))
  | 0x04 => decodeIf (z shamt && decide ((functOf w).toNat < 8)) (.mtc0 rt rd (functOf w))
  -- `MFMC0` (`di`/`ei`): `rd` = 12 (Status), bits 10..6 zero, bit 5 = `sc`,
  -- bits 4..0 zero.
  | 0x0b =>
    match (functOf w).toNat with
    | 0x00 => decodeIf (rd == 12#32 && z shamt) (.di rt)
    | 0x20 => decodeIf (rd == 12#32 && z shamt) (.ei rt)
    | _ => none
  -- `RDPGPR` (0x0a) / `WRPGPR` (0x0e): bits 10..0 must be zero.
  | 0x0a => decodeIf (z shamt && z (functOf w)) (.rdpgpr rd rt)
  | 0x0e => decodeIf (z shamt && z (functOf w)) (.wrpgpr rd rt)
  | _ => none

/-- **COP1** `fmt = S` (`rs` = 0x10), keyed by `funct` (Table A.15, p.456). Fields: `ft` = `rt`,
`fs` = `rd`, `fd` = `sa`; unary operations require `ft = 0`. Release 6 removed MOVCF (0x11),
MOVZ/MOVN (0x12/0x13) and C.cond.fmt (0x30-0x3f).
-- W5: CVT.L.S (0x25), ROUND/TRUNC/CEIL/FLOOR.L.S (0x08-0x0b).
-- W6: SEL (0x10), SELEQZ (0x14), SELNEZ (0x17), MADDF/MSUBF (0x18/0x19), RINT (0x1a), CLASS
--     (0x1b), MIN/MINA/MAX/MAXA (0x1c-0x1f). -/
def decodeCop1S (w : W32) : Option Instruction :=
  let rt := rtOf w
  let rd := rdOf w
  let shamt := shamtOf w
  let z (x : W32) : Bool := x == 0#32
  match (functOf w).toNat with
  | 0x00 => some (.addS shamt rd rt)
  | 0x01 => some (.subS shamt rd rt)
  | 0x02 => some (.mulS shamt rd rt)
  | 0x03 => some (.divS shamt rd rt)
  | 0x04 => decodeIf (z rt) (.sqrtS shamt rd)
  | 0x05 => decodeIf (z rt) (.absS shamt rd)
  | 0x06 => decodeIf (z rt) (.movS shamt rd)
  | 0x07 => decodeIf (z rt) (.negS shamt rd)
  | 0x0c => decodeIf (z rt) (.roundWS shamt rd)
  | 0x0d => decodeIf (z rt) (.truncWS shamt rd)
  | 0x0e => decodeIf (z rt) (.ceilWS shamt rd)
  | 0x0f => decodeIf (z rt) (.floorWS shamt rd)
  | 0x15 => decodeIf (z rt) (.recipS shamt rd)
  | 0x16 => decodeIf (z rt) (.rsqrtS shamt rd)
  | 0x21 => decodeIf (z rt) (.cvtDS shamt rd)
  | 0x24 => decodeIf (z rt) (.cvtWS shamt rd)
  | _ => none

/-- **COP1** `fmt = D` (`rs` = 0x11), keyed by `funct` (Table A.16, p.457); as `decodeCop1S`.
-- W5: CVT.L.D (0x25), ROUND/TRUNC/CEIL/FLOOR.L.D (0x08-0x0b).
-- W6: SEL, SELEQZ, SELNEZ, MADDF, MSUBF, RINT, CLASS, MIN, MINA, MAX, MAXA (.D). -/
def decodeCop1D (w : W32) : Option Instruction :=
  let rt := rtOf w
  let rd := rdOf w
  let shamt := shamtOf w
  let z (x : W32) : Bool := x == 0#32
  match (functOf w).toNat with
  | 0x00 => some (.addD shamt rd rt)
  | 0x01 => some (.subD shamt rd rt)
  | 0x02 => some (.mulD shamt rd rt)
  | 0x03 => some (.divD shamt rd rt)
  | 0x04 => decodeIf (z rt) (.sqrtD shamt rd)
  | 0x05 => decodeIf (z rt) (.absD shamt rd)
  | 0x06 => decodeIf (z rt) (.movD shamt rd)
  | 0x07 => decodeIf (z rt) (.negD shamt rd)
  | 0x0c => decodeIf (z rt) (.roundWD shamt rd)
  | 0x0d => decodeIf (z rt) (.truncWD shamt rd)
  | 0x0e => decodeIf (z rt) (.ceilWD shamt rd)
  | 0x0f => decodeIf (z rt) (.floorWD shamt rd)
  | 0x15 => decodeIf (z rt) (.recipD shamt rd)
  | 0x16 => decodeIf (z rt) (.rsqrtD shamt rd)
  | 0x20 => decodeIf (z rt) (.cvtSD shamt rd)
  | 0x24 => decodeIf (z rt) (.cvtWD shamt rd)
  | _ => none

/-- **COP1** (opcode 0x11), keyed by `rs` (Table A.14, p.456). Release 6 removed BC1 (`rs` =
0x08: BC1F/BC1T/BC1FL/BC1TL).
-- W5: `rs` 0x09 BC1EQZ, 0x0d BC1NEZ; `fmt = L` (0x15) CVT.S.L/CVT.D.L.
-- W6: `fmt = W` / `L` functs 0x00-0x1f: CMP.condn.S / CMP.condn.D. -/
def decodeCop1 (w : W32) : Option Instruction :=
  let rt := rtOf w
  let rd := rdOf w
  let shamt := shamtOf w
  let z (x : W32) : Bool := x == 0#32
  match (rsOf w).toNat with
  -- `mfc1`/`mtc1`/`mfhc1`/`mthc1`/`cfc1`/`ctc1`: bits 10..0 must be zero.
  | 0x00 => decodeIf (z shamt && z (functOf w)) (.mfc1 rt rd)
  | 0x04 => decodeIf (z shamt && z (functOf w)) (.mtc1 rt rd)
  | 0x03 => decodeIf (z shamt && z (functOf w)) (.mfhc1 rt rd)
  | 0x07 => decodeIf (z shamt && z (functOf w)) (.mthc1 rt rd)
  | 0x02 => decodeIf (z shamt && z (functOf w)) (.cfc1 rt rd)
  | 0x06 => decodeIf (z shamt && z (functOf w)) (.ctc1 rt rd)
  | 0x10 => decodeCop1S w
  | 0x11 => decodeCop1D w
  | 0x14 =>  -- fmt = W
    match (functOf w).toNat with
    | 0x20 => decodeIf (z rt) (.cvtSW shamt rd)
    | 0x21 => decodeIf (z rt) (.cvtDW shamt rd)
    | _ => none
  | _ => none

/-- **The Release 6 primary opcode table** (Table A.2, p.451). Removed by Release 6 (do not decode):
ADDI (0x08), COP1X (0x13: "Release 6 removes all pre-Release 6 COP1X instructions", Table A.21,
p.459), BEQL/BNEL/BLEZL/BGTZL (0x14-0x17 with `rt = 0`), SPECIAL2 (0x1c), JALX (0x1d), LWL/LWR/
SWL/SWR (0x22, 0x26, 0x2a, 0x2e), CACHE (0x2f), LL (0x30), LWC2/LDC2/SWC2/SDC2 (0x32, 0x36, 0x3a,
0x3e), PREF (0x33), SC (0x38). LUI is AUI with `rs = 0` (0x0f).
-- W3: 0x06/0x07 with `rt ≠ 0` (POP06/POP07: BLEZALC, BGEZALC, BGEUC, BGTZALC, BLTZALC, BLTUC),
--     0x08 POP10, 0x16 POP26, 0x17 POP27, 0x18 POP30, 0x32 BC, 0x36 POP66, 0x3a BALC, 0x3e POP76.
Release 6 adds 0x3b PCREL (Table A.13, p.455; Table A.24, p.462): bits 20..19 = 00 ADDIUPC (p.37),
01 LWPC (p.246); bits 20..16 = 11110 AUIPC (p.48), 11111 ALUIPC (p.43); the others (LWUPC, LDPC and
the reserved 11xxx values) are MIPS64-only or reserved and do not decode. -/
def decodePrimary (w : W32) : Option Instruction :=
  let rs := rsOf w
  let rt := rtOf w
  let imm := immOf w
  let z (x : W32) : Bool := x == 0#32
  match (opcodeOf w).toNat with
  | 0x00 => decodeSpecial w
  | 0x01 => decodeRegimm w
  | 0x02 => some (.j (targetOf w))
  | 0x03 => some (.jal (targetOf w))
  | 0x04 => some (.beq rs rt imm)
  | 0x05 => some (.bne rs rt imm)
  | 0x06 => decodeIf (z rt) (.blez rs imm)
  | 0x07 => decodeIf (z rt) (.bgtz rs imm)
  | 0x09 => some (.addiu rs rt imm)
  | 0x0a => some (.slti rs rt imm)
  | 0x0b => some (.sltiu rs rt imm)
  | 0x0c => some (.andi rs rt imm)
  | 0x0d => some (.ori rs rt imm)
  | 0x0e => some (.xori rs rt imm)
  | 0x0f => some (.aui rs rt imm)
  | 0x10 => decodeCop0 w
  | 0x11 => decodeCop1 w
  | 0x1f => decodeSpecial3 w
  | 0x20 => some (.lb rs rt imm)
  | 0x21 => some (.lh rs rt imm)
  | 0x23 => some (.lw rs rt imm)
  | 0x24 => some (.lbu rs rt imm)
  | 0x25 => some (.lhu rs rt imm)
  | 0x28 => some (.sb rs rt imm)
  | 0x29 => some (.sh rs rt imm)
  | 0x2b => some (.sw rs rt imm)
  | 0x31 => some (.lwc1 rs rt imm)
  | 0x35 => some (.ldc1 rs rt imm)
  | 0x39 => some (.swc1 rs rt imm)
  | 0x3d => some (.sdc1 rs rt imm)
  -- BEGIN R6-4
  | 0x3b =>  -- PCREL
    match (pcrelOf w).toNat with
    | 0 => some (.addiupc rs (imm19Of w))
    | 1 => some (.lwpc rs (imm19Of w))
    | _ => if rt == 0x1e#32 then some (.auipc rs imm)
           else decodeIf (rt == 0x1f#32) (.aluipc rs imm)
  -- END R6-4
  | _ => none

/-- **The decoder table of each release.** An instruction is available in a release exactly when
that release's table emits it. -/
def decodeFor : Release → W32 → Option Instruction
  | .r6 => decodePrimary

/-- Decode a raw 32-bit instruction word into an `Instruction`, or `none` if the word is not the
canonical encoding of an instruction of this profile's release (`step` then raises Reserved
Instruction or Coprocessor Unusable). -/
def decode (w : W32) : Option Instruction := decodeFor profile.release w

/-- Encode an `Instruction` back into its raw 32-bit word: the canonical
encoding, with every reserved/don't-care field zero. `decode (encode i) =
some i` for well-formed `i` (fields in range); see
`Semantics/Specs/DecodeSpec.lean`. -/
def encode (i : Instruction) : W32 :=
  match i with
  | .add  rs rt rd => mkRT rs rt rd 0#32 0x20#32
  | .addu rs rt rd => mkRT rs rt rd 0#32 0x21#32
  | .sub  rs rt rd => mkRT rs rt rd 0#32 0x22#32
  | .subu rs rt rd => mkRT rs rt rd 0#32 0x23#32
  | .and  rs rt rd => mkRT rs rt rd 0#32 0x24#32
  | .or   rs rt rd => mkRT rs rt rd 0#32 0x25#32
  | .xor  rs rt rd => mkRT rs rt rd 0#32 0x26#32
  | .nor  rs rt rd => mkRT rs rt rd 0#32 0x27#32
  | .slt  rs rt rd => mkRT rs rt rd 0#32 0x2a#32
  | .sltu rs rt rd => mkRT rs rt rd 0#32 0x2b#32
  | .sll  rd rt shamt => mkRT 0#32 rt rd shamt 0x00#32
  | .pause => mkRT 0#32 0#32 0#32 5#32 0x00#32
  | .srl  rd rt shamt => mkRT 0#32 rt rd shamt 0x02#32
  | .sra  rd rt shamt => mkRT 0#32 rt rd shamt 0x03#32
  | .sllv rd rt rs => mkRT rs rt rd 0#32 0x04#32
  | .srlv rd rt rs => mkRT rs rt rd 0#32 0x06#32
  | .srav rd rt rs => mkRT rs rt rd 0#32 0x07#32
  -- Rotate (MIPS32r2): `rs`/`shamt` field overloading, per the `.rotr`/
  -- `.rotrv` docstrings.
  | .rotr  rd rt sa => mkRT 0x01#32 rt rd sa 0x02#32
  | .rotrv rd rt rs => mkRT rs rt rd 0x01#32 0x06#32
  | .jalr rs rd => mkRT rs 0#32 rd 0#32 0x09#32
  | .jalrHb rs rd => mkRT rs 0#32 rd 16#32 0x09#32
  -- SPECIAL2: duplicate rd into the rt-position field per the real encoding.
  | .clo rs rd => mkRT rs 0#32 rd 1#32 0x11#32
  | .clz rs rd => mkRT rs 0#32 rd 1#32 0x10#32
  -- SPECIAL3 BSHFL: rs fixed 0, shamt-position field selects seb/seh/wsbh.
  | .seb rd rt => (0x1f#32 <<< 26) ||| mkRT 0#32 rt rd 0x10#32 0x20#32
  | .seh rd rt => (0x1f#32 <<< 26) ||| mkRT 0#32 rt rd 0x18#32 0x20#32
  | .wsbh rd rt => (0x1f#32 <<< 26) ||| mkRT 0#32 rt rd 0x02#32 0x20#32
  -- SPECIAL3 bitfield extract/insert: `pos` is the raw `shamt` field for
  -- both; the raw `rd`-position field is `size - 1` for `ext` ("msbd") but
  -- `pos + size - 1` for `ins` ("msb") -- see the `.ext`/`.ins` docstrings.
  | .ext rt rs pos size => (0x1f#32 <<< 26) ||| mkRT rs rt (size - 1#32) pos 0x00#32
  | .ins rt rs pos size => (0x1f#32 <<< 26) ||| mkRT rs rt (pos + size - 1#32) pos 0x04#32
  | .rdhwr rt rd sel => (0x1f#32 <<< 26) ||| mkRT 0#32 rt rd sel 0x3b#32
  | .addiu rs rt imm => mkIT 0x09#32 rs rt imm
  | .slti  rs rt imm => mkIT 0x0a#32 rs rt imm
  | .sltiu rs rt imm => mkIT 0x0b#32 rs rt imm
  | .andi  rs rt imm => mkIT 0x0c#32 rs rt imm
  | .ori   rs rt imm => mkIT 0x0d#32 rs rt imm
  | .xori  rs rt imm => mkIT 0x0e#32 rs rt imm
  | .aui   rs rt imm => mkIT 0x0f#32 rs rt imm
  -- BEGIN R6-4
  | .mul  rs rt rd => mkRT rs rt rd 2#32 0x18#32
  | .muh  rs rt rd => mkRT rs rt rd 3#32 0x18#32
  | .mulu rs rt rd => mkRT rs rt rd 2#32 0x19#32
  | .muhu rs rt rd => mkRT rs rt rd 3#32 0x19#32
  | .div  rs rt rd => mkRT rs rt rd 2#32 0x1a#32
  | .mod  rs rt rd => mkRT rs rt rd 3#32 0x1a#32
  | .divu rs rt rd => mkRT rs rt rd 2#32 0x1b#32
  | .modu rs rt rd => mkRT rs rt rd 3#32 0x1b#32
  | .seleqz rs rt rd => mkRT rs rt rd 0#32 0x35#32
  | .selnez rs rt rd => mkRT rs rt rd 0#32 0x37#32
  | .lsa rs rt rd sa => mkRT2 rs rt rd 0#32 sa 0x05#32
  | .align rs rt rd bp => (0x1f#32 <<< 26) ||| mkRT2 rs rt rd 2#32 bp 0x20#32
  | .bitswap rd rt => (0x1f#32 <<< 26) ||| mkRT 0#32 rt rd 0#32 0x20#32
  | .addiupc rs imm => (0x3b#32 <<< 26) ||| mkPc19 rs 0#32 imm
  | .lwpc rs off => (0x3b#32 <<< 26) ||| mkPc19 rs 1#32 off
  | .auipc rs imm => mkIT 0x3b#32 rs 0x1e#32 imm
  | .aluipc rs imm => mkIT 0x3b#32 rs 0x1f#32 imm
  -- END R6-4
  | .lw rs rt imm => mkIT 0x23#32 rs rt imm
  | .sw rs rt imm => mkIT 0x2b#32 rs rt imm
  | .lb rs rt imm => mkIT 0x20#32 rs rt imm
  | .lbu rs rt imm => mkIT 0x24#32 rs rt imm
  | .lh rs rt imm => mkIT 0x21#32 rs rt imm
  | .lhu rs rt imm => mkIT 0x25#32 rs rt imm
  | .sh rs rt imm => mkIT 0x29#32 rs rt imm
  | .sb rs rt imm => mkIT 0x28#32 rs rt imm
  | .ll rs rt imm => (0x1f#32 <<< 26) ||| mkOff9 rs rt imm 0x36#32
  | .sc rs rt imm => (0x1f#32 <<< 26) ||| mkOff9 rs rt imm 0x26#32
  | .beq rs rt imm => mkIT 0x04#32 rs rt imm
  | .bne rs rt imm => mkIT 0x05#32 rs rt imm
  | .blez rs imm => mkIT 0x06#32 rs 0#32 imm
  | .bgtz rs imm => mkIT 0x07#32 rs 0#32 imm
  | .bltz   rs imm => mkIT 0x01#32 rs 0x00#32 imm
  | .bgez   rs imm => mkIT 0x01#32 rs 0x01#32 imm
  | .nal imm => mkIT 0x01#32 0#32 0x10#32 imm
  | .bal imm => mkIT 0x01#32 0#32 0x11#32 imm
  | .synci  rs imm => mkIT 0x01#32 rs 0x1f#32 imm
  | .j   target => (0x02#32 <<< 26) ||| mkJT target
  | .jal target => (0x03#32 <<< 26) ||| mkJT target
  | .syscall code => mkCode20 code 0x0c#32
  | .teq rs rt code => mkTrap rs rt code 0x34#32
  | .tne rs rt code => mkTrap rs rt code 0x36#32
  | .tlt rs rt code => mkTrap rs rt code 0x32#32
  | .tge rs rt code => mkTrap rs rt code 0x30#32
  | .tltu rs rt code => mkTrap rs rt code 0x33#32
  | .tgeu rs rt code => mkTrap rs rt code 0x31#32
  | .break code => mkCode20 code 0x0d#32
  -- sync: no stored `stype` field, so this always encodes `stype = 0`
  -- (the default "complete barrier"), same simplification as `break`'s
  -- unmodeled "code" field.
  | .sync stype => mkRT 0#32 0#32 0#32 stype 0x0f#32
  | .pref rs hint imm => (0x1f#32 <<< 26) ||| mkOff9 rs hint imm 0x35#32
  -- Coprocessor 0 (CP0). Same opcode-OR convention as the COP1 cases below.
  | .mfc0 rt rd sel => (0x10#32 <<< 26) ||| mkRT 0x00#32 rt rd 0#32 sel
  | .mtc0 rt rd sel => (0x10#32 <<< 26) ||| mkRT 0x04#32 rt rd 0#32 sel
  | .di rt => (0x10#32 <<< 26) ||| mkRT 0x0b#32 rt 12#32 0#32 0x00#32
  | .ei rt => (0x10#32 <<< 26) ||| mkRT 0x0b#32 rt 12#32 0#32 0x20#32
  | .eret => (0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x18#32
  | .wait code => mkWait 0x10#32 1#32 code 0x20#32
  | .rdpgpr rd rt => (0x10#32 <<< 26) ||| mkRT 0x0a#32 rt rd 0#32 0#32
  | .wrpgpr rd rt => (0x10#32 <<< 26) ||| mkRT 0x0e#32 rt rd 0#32 0#32
  -- Coprocessor 1 (FPU). `mkRT` leaves the opcode field 0 (correct for
  -- plain R-type), so the COP1 cases OR in opcode 0x11 explicitly, the same
  -- way `.j`/`.jal` OR in their opcode over `mkJT`'s target-only field.
  | .mfc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x00#32 rt fs 0#32 0#32
  | .mtc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x04#32 rt fs 0#32 0#32
  | .mfhc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x03#32 rt fs 0#32 0#32
  | .mthc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x07#32 rt fs 0#32 0#32
  | .cfc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x02#32 rt fs 0#32 0#32
  | .ctc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x06#32 rt fs 0#32 0#32
  | .lwc1 rs ft imm => mkIT 0x31#32 rs ft imm
  | .swc1 rs ft imm => mkIT 0x39#32 rs ft imm
  | .ldc1 rs ft imm => mkIT 0x35#32 rs ft imm
  | .sdc1 rs ft imm => mkIT 0x3d#32 rs ft imm
  | .addS fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs fd 0x00#32
  | .subS fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs fd 0x01#32
  | .mulS fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs fd 0x02#32
  | .divS fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs fd 0x03#32
  | .sqrtS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x04#32
  | .absS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x05#32
  | .movS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x06#32
  | .negS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x07#32
  | .recipS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x15#32
  | .rsqrtS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x16#32
  | .roundWS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x0c#32
  | .truncWS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x0d#32
  | .ceilWS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x0e#32
  | .floorWS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x0f#32
  | .cvtWS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x24#32
  | .addD fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs fd 0x00#32
  | .subD fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs fd 0x01#32
  | .mulD fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs fd 0x02#32
  | .divD fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs fd 0x03#32
  | .sqrtD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x04#32
  | .absD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x05#32
  | .movD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x06#32
  | .negD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x07#32
  | .recipD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x15#32
  | .rsqrtD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x16#32
  | .roundWD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x0c#32
  | .truncWD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x0d#32
  | .ceilWD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x0e#32
  | .floorWD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x0f#32
  | .cvtWD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x24#32
  | .cvtDS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x21#32
  | .cvtSD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x20#32
  | .cvtSW fd fs => (0x11#32 <<< 26) ||| mkRT 0x14#32 0#32 fs fd 0x20#32
  | .cvtDW fd fs => (0x11#32 <<< 26) ||| mkRT 0x14#32 0#32 fs fd 0x21#32
  -- BEGIN R6-2
  | .eretnc => (0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 1#32 0x18#32
  | .sigrie code => mkIT 0x01#32 0#32 0x17#32 code
  | .cache base op off => (0x1f#32 <<< 26) ||| mkOff9 base op off 0x25#32
  -- END R6-2
