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
(`step` raises Reserved Instruction, or Coprocessor Unusable in a coprocessor's space).

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
  The FPU is the Release 6 64-bit FPU (`Status.FR = 1`, one 64-bit FPR per double, `fmt` L =
  0x15 for the longword conversions; MD00082 Vol I-A Rev 6.01 §6.4.1, p.84) with
  `FCSR.NAN2008 = ABS2008 = 1` (§6.5.4, p.92-94).
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
  -- R-type variable shift (SPECIAL; the `sa` field is 0): SLLV p.377, SRLV p.386, SRAV p.384.
  /-- `$rd = $rt << ($rs & 0x1f)`, logical, shift amount from a register's
  low 5 bits (opcode 0, funct 0x04). MIPS32. -/
  | sllv (rd rt rs : W32)
  /-- `$rd = $rt >> ($rs & 0x1f)`, logical/zero-fill, shift amount from a
  register's low 5 bits (opcode 0, funct 0x06). MIPS32. -/
  | srlv (rd rt rs : W32)
  /-- `$rd = $rt >> ($rs & 0x1f)`, arithmetic/sign-fill, shift amount from a
  register's low 5 bits (opcode 0, funct 0x07). MIPS32. -/
  | srav (rd rt rs : W32)
  -- R-type rotate: ROTR is SRL's encoding (funct 0x02) with bit 21 (`R`, the low bit of the `rs`
  -- field) set; ROTRV is SRLV's (funct 0x06) with bit 6 (`R`, the low bit of `sa`) set (ROTR p.339,
  -- ROTRV p.340).
  /-- `$rd = $rt` rotated right by the constant `sa` (0-31) bits -- bits
  shifted off the bottom wrap around to the top, unlike `srl`'s zero-fill
  (opcode 0, funct 0x02, `rs` field = 0x01; ROTR, p.339). -/
  | rotr (rd rt sa : W32)
  /-- `$rd = $rt` rotated right by `$rs & 0x1f` bits, rotate amount from a
  register's low 5 bits (opcode 0, funct 0x06, `shamt` field = 0x01; ROTRV, p.340). -/
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
  -- R-type SPECIAL3 BSHFL sign-extend (funct 0x20): `rs` is 0 and the `sa`-position sub-field
  -- selects the operation.
  /-- `$rd = sign-extend($rt[7:0])` to 32 bits (SPECIAL3 opcode 0x1f,
  funct 0x20, sub-field 0x10; SEB, p.365). -/
  | seb (rd rt : W32)
  /-- `$rd = sign-extend($rt[15:0])` to 32 bits (SPECIAL3 opcode 0x1f,
  funct 0x20, sub-field 0x18; SEH, p.366). -/
  | seh (rd rt : W32)
  /-- "Word Swap Bytes Within Halfwords": swaps the byte order *within* each
  16-bit half of `$rt` independently (byte 0 <-> 1, byte 2 <-> 3), leaving
  the two halfwords in their original word positions -- **not** a full
  32-bit byte-reverse (that needs `wsbh` followed by `rotr` by 16)
  (SPECIAL3 opcode 0x1f, funct 0x20, sub-field 0x02 -- same BSHFL funct
  family as `seb`/`seh`, distinguished by the sub-field like they are; WSBH, p.445). -/
  | wsbh (rd rt : W32)
  -- R-type SPECIAL3 bitfield extract/insert (EXT p.183-184, INS p.192-193). `pos` (`lsb`) is
  -- the `sa` field (bits 10..6) of both; the `rd`-position field (bits 15..11) holds
  -- `msbd = size - 1` for EXT and `msb = pos + size - 1` for INS. `decode`/`encode` do the ±1
  -- arithmetic, so the constructors carry `pos`/`size`; the UNPREDICTABLE field combinations do
  -- not decode (`decodeSpecial3`).
  /-- `$rt = zero-extend($rs[pos+size-1 .. pos])`, extracting a `size`-bit
  field starting at bit `pos` (SPECIAL3 opcode 0x1f, funct 0x00; EXT, p.183). -/
  | ext (rt rs pos size : W32)
  /-- Inserts the low `size` bits of `$rs` into `$rt` starting at bit `pos`;
  bits of `$rt` outside `[pos+size-1 .. pos]` are left unchanged (SPECIAL3
  opcode 0x1f, funct 0x04; INS, p.192). -/
  | ins (rt rs pos size : W32)
  -- SPECIAL3 RDHWR: read a hardware register (`HWREna`-gated).
  /-- Read Hardware Register: `$rt = HWR[rd, sel]` (SPECIAL3 opcode 0x1f, funct 0x3b, `rs` = 0,
  bits 10..9 = 0, `sel` = bits 8..6; MD00086 Vol II-A Rev 6.06, RDHWR, p.332-334: "In Release 6, a
  sel field has been added"). The model implements `rd` = 0 `CPUNum`, 1 `SYNCI_Step`, 2 `CC`
  (= `Count`), 3 `CCRes`, each with `sel = 0`; access needs Coprocessor 0 to be enabled or the
  `HWREna` bit `rd` set, otherwise (and for every other `rd`/`sel`) Reserved Instruction
  (`Step.lean`). -/
  | rdhwr (rt rd sel : W32)
  -- I-type arithmetic and logic with a 16-bit immediate
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
  /-- `MEM8[$rs + offset] = $rt[7:0]`, no alignment requirement (opcode 0x28; MD00086 Vol II-A
  Rev 6.06, SB, p.344). -/
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
  -- I-type REGIMM zero-comparison branches (opcode 0x01): the `rt` field selects the instruction
  -- (Table A.4, p.452). BLTZ (p.97) and BGEZ (p.75) have the `rs, offset` shape of `blez`/`bgtz`.
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
  -- Instruction-cache synchronize hint (REGIMM, `rt` = 0x1f; SYNCI p.412-414): `rs`, `imm` form an
  -- address as in `lw`/`sw`.
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
  -- Breakpoint, memory barrier and prefetch
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
  /-- `$rt = FPR[fs]63..32`, the high word of the 64-bit FPR `fs` (COP1, `rs` = `MFH` = 0x03;
  MD00086 Vol II-A Rev 6.06, MFHC1, p.271). -/
  | mfhc1 (rt fs : W32)
  /-- The high word of the 64-bit FPR `fs` `= $rt`, the low word unchanged (COP1, `rs` = `MTH` =
  0x07; MD00086 Vol II-A Rev 6.06, MTHC1, p.295). -/
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
  -- FP arithmetic and conversions, single (fmt = S = 0x10).
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
  /-- `fd = |fs|`, non-arithmetic with `FCSR.ABS2008 = 1` (funct 0x05). -/
  | absS (fd fs : W32)
  /-- `fd = fs`, non-arithmetic (funct 0x06). -/
  | movS (fd fs : W32)
  /-- `fd = −fs`, non-arithmetic with `FCSR.ABS2008 = 1` (funct 0x07). -/
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
  -- FP arithmetic and conversions, double (fmt = D = 0x11).
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
  /-- `fd = |fs|`, non-arithmetic with `FCSR.ABS2008 = 1` (funct 0x05). -/
  | absD (fd fs : W32)
  /-- `fd = fs`, non-arithmetic (funct 0x06). -/
  | movD (fd fs : W32)
  /-- `fd = −fs`, non-arithmetic with `FCSR.ABS2008 = 1` (funct 0x07). -/
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
  -- Privileged and system instructions: ERETNC, SIGRIE, CACHE
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
  -- Release 6 compact branches and jumps (MD00086 Vol II-A Rev 6.06): no delay slot. The
  -- conditional ones have a forbidden slot (the next instruction, when not taken); BC, BALC, JIC
  -- and JIALC have neither (MD00082 Vol I-A Rev 6.01 §5.3.2, p.62). Several share a primary opcode
  -- and are told apart by the `rs`/`rt` fields (Table A.26 "B*C compact branch encodings", p.464):
  -- each constructor's docstring gives its constraint, which `decode` checks and `WellFormed`
  -- requires. `off` is the raw offset field (16 bits; 21 for BEQZC/BNEZC; 26 for BC/BALC).
  /-- `BC offset`: `PC ← PC + 4 + sext(offset ‖ 00)` (opcode `110010`, 26-bit offset; BC, p.53). -/
  | bc (off : W32)
  /-- `BALC offset`: `GPR[31] ← PC + 4`, then as `bc` (opcode `111010`; BALC, p.52). -/
  | balc (off : W32)
  /-- `BEQC rs, rt, offset`: branch if `GPR[rs] = GPR[rt]` (POP10 `001000`, `0 < rs < rt`;
  B<cond>C, p.82-85). -/
  | beqc (rs rt off : W32)
  /-- `BNEC rs, rt, offset`: branch if `GPR[rs] ≠ GPR[rt]` (POP30 `011000`, `0 < rs < rt`; p.82-85). -/
  | bnec (rs rt off : W32)
  /-- `BLTC rs, rt, offset`: branch if `GPR[rs] < GPR[rt]`, signed (POP27 `010111`, `rs ≠ 0`,
  `rt ≠ 0`, `rs ≠ rt`; p.82-85). -/
  | bltc (rs rt off : W32)
  /-- `BGEC rs, rt, offset`: branch if `GPR[rs] ≥ GPR[rt]`, signed (POP26 `010110`, `rs ≠ 0`,
  `rt ≠ 0`, `rs ≠ rt`; p.82-85). -/
  | bgec (rs rt off : W32)
  /-- `BLTUC rs, rt, offset`: branch if `GPR[rs] < GPR[rt]`, unsigned (POP07 `000111`, `rs ≠ 0`,
  `rt ≠ 0`, `rs ≠ rt`; p.82-85). -/
  | bltuc (rs rt off : W32)
  /-- `BGEUC rs, rt, offset`: branch if `GPR[rs] ≥ GPR[rt]`, unsigned (POP06 `000110`, `rs ≠ 0`,
  `rt ≠ 0`, `rs ≠ rt`; p.82-85). -/
  | bgeuc (rs rt off : W32)
  /-- `BLEZC rt, offset`: branch if `GPR[rt] ≤ 0` (POP26, `rs = 0`, `rt ≠ 0`; p.82-85). -/
  | blezc (rt off : W32)
  /-- `BGEZC rt, offset`: branch if `GPR[rt] ≥ 0` (POP26, `rs = rt ≠ 0`; p.82-85). -/
  | bgezc (rt off : W32)
  /-- `BGTZC rt, offset`: branch if `GPR[rt] > 0` (POP27, `rs = 0`, `rt ≠ 0`; p.82-85). -/
  | bgtzc (rt off : W32)
  /-- `BLTZC rt, offset`: branch if `GPR[rt] < 0` (POP27, `rs = rt ≠ 0`; p.82-85). -/
  | bltzc (rt off : W32)
  /-- `BEQZC rs, offset`: branch if `GPR[rs] = 0` (POP66 `110110`, `rs ≠ 0`, 21-bit offset;
  p.82-85). -/
  | beqzc (rs off : W32)
  /-- `BNEZC rs, offset`: branch if `GPR[rs] ≠ 0` (POP76 `111110`, `rs ≠ 0`, 21-bit offset;
  p.82-85). -/
  | bnezc (rs off : W32)
  /-- `BLEZALC rt, offset`: `GPR[31] ← PC + 4`; branch if `GPR[rt] ≤ 0` (POP06, `rs = 0`, `rt ≠ 0`;
  B{LE,GE,GT,LT,EQ,NE}ZALC, p.77-79). -/
  | blezalc (rt off : W32)
  /-- `BGEZALC rt, offset`: link; branch if `GPR[rt] ≥ 0` (POP06, `rs = rt ≠ 0`; p.77-79). -/
  | bgezalc (rt off : W32)
  /-- `BGTZALC rt, offset`: link; branch if `GPR[rt] > 0` (POP07, `rs = 0`, `rt ≠ 0`; p.77-79). -/
  | bgtzalc (rt off : W32)
  /-- `BLTZALC rt, offset`: link; branch if `GPR[rt] < 0` (POP07, `rs = rt ≠ 0`; p.77-79). -/
  | bltzalc (rt off : W32)
  /-- `BEQZALC rt, offset`: link; branch if `GPR[rt] = 0` (POP10, `rs = 0`, `rt ≠ 0`; p.77-79). -/
  | beqzalc (rt off : W32)
  /-- `BNEZALC rt, offset`: link; branch if `GPR[rt] ≠ 0` (POP30, `rs = 0`, `rt ≠ 0`; p.77-79). -/
  | bnezalc (rt off : W32)
  /-- `BOVC rs, rt, offset`: branch if `GPR[rs] + GPR[rt]` overflows 32-bit signed (POP10,
  `rs ≥ rt`; BOVC, p.107-108). -/
  | bovc (rs rt off : W32)
  /-- `BNVC rs, rt, offset`: branch if `GPR[rs] + GPR[rt]` does not overflow (POP30, `rs ≥ rt`;
  BNVC, p.107-108). -/
  | bnvc (rs rt off : W32)
  /-- `JIC rt, offset`: `PC ← GPR[rt] + sext(offset)` (POP66, `rs = 0`; JIC, p.205). -/
  | jic (rt off : W32)
  /-- `JIALC rt, offset`: `GPR[31] ← PC + 4`, then as `jic` (POP76, `rs = 0`; JIALC, p.203). -/
  | jialc (rt off : W32)
  -- Longword conversions: the L-format (64-bit fixed point) ones a 64-bit Release 6 FPU
  -- requires ("Release 6 on a 64-bit FPU requires S, D, W, and L data formats", MD00082 Vol I-A
  -- Rev 6.01 Table 6.4 note 3, p.85). COP1 R-format, `ft` = 0; fields `fd` (= `sa`), `fs` (= `rd`).
  /-- `CVT.L.S`: single → longword, rounding per FCSR.RM (fmt = S, funct 0x25; MD00086 Vol II-A
  Rev 6.06, CVT.L.fmt, p.154). -/
  | cvtLS (fd fs : W32)
  /-- `CVT.L.D`: double → longword, rounding per FCSR.RM (fmt = D, funct 0x25; p.154). -/
  | cvtLD (fd fs : W32)
  /-- `ROUND.L.S`: single → longword, round to nearest even (fmt = S, funct 0x08; p.341). -/
  | roundLS (fd fs : W32)
  /-- `ROUND.L.D` (fmt = D, funct 0x08; p.341). -/
  | roundLD (fd fs : W32)
  /-- `TRUNC.L.S`: single → longword, round toward zero (fmt = S, funct 0x09; p.440). -/
  | truncLS (fd fs : W32)
  /-- `TRUNC.L.D` (fmt = D, funct 0x09; p.440). -/
  | truncLD (fd fs : W32)
  /-- `CEIL.L.S`: single → longword, round toward +∞ (fmt = S, funct 0x0a; p.127). -/
  | ceilLS (fd fs : W32)
  /-- `CEIL.L.D` (fmt = D, funct 0x0a; p.127). -/
  | ceilLD (fd fs : W32)
  /-- `FLOOR.L.S`: single → longword, round toward −∞ (fmt = S, funct 0x0b; p.185). -/
  | floorLS (fd fs : W32)
  /-- `FLOOR.L.D` (fmt = D, funct 0x0b; p.185). -/
  | floorLD (fd fs : W32)
  /-- `CVT.S.L`: longword → single, rounding per FCSR.RM (fmt = L = 0x15, funct 0x20; CVT.S.fmt,
  p.159). -/
  | cvtSL (fd fs : W32)
  /-- `CVT.D.L`: longword → double, rounding per FCSR.RM (fmt = L, funct 0x21; CVT.D.fmt, p.153). -/
  | cvtDL (fd fs : W32)
  -- Release 6 FP instructions: compare, branch on FPR, select, fused multiply-add, min/max,
  -- class and round (MD00086 Vol II-A Rev 6.06). COP1 R-format: `ft` = `rt`, `fs` = `rd`,
  -- `fd` = `sa`.
  /-- `CMP.condn.S fd, fs, ft`: `FPR[fd] ← FPR[fs] compare_cond FPR[ft]` as a 32-bit mask of all ones or
  all zeros (COP1, `rs` = 10100, bit 5 = 0, `condn` in bits 4..0; CMP.condn.fmt, p.136-140). `cond` is
  the `condn` field; only the 22 values of Table A.17 (p.457) are instructions (`cmpCondnOK`). The
  mnemonics are `cmp.af.s`, `cmp.un.s`, `cmp.eq.s`, `cmp.ueq.s`, `cmp.lt.s`, `cmp.ult.s`, `cmp.le.s`,
  `cmp.ule.s`, `cmp.saf.s`, `cmp.sun.s`, `cmp.seq.s`, `cmp.sueq.s`, `cmp.slt.s`, `cmp.sult.s`,
  `cmp.sle.s`, `cmp.sule.s`, `cmp.or.s`, `cmp.une.s`, `cmp.ne.s`, `cmp.sor.s`, `cmp.sune.s`,
  `cmp.sne.s`. -/
  | cmpS (cond fd fs ft : W32)
  /-- `CMP.condn.D fd, fs, ft`: as `cmpS`, a 64-bit mask (COP1, `rs` = 10101; p.136-140). The
  mnemonics are `cmp.af.d`, `cmp.un.d`, `cmp.eq.d`, `cmp.ueq.d`, `cmp.lt.d`, `cmp.ult.d`, `cmp.le.d`,
  `cmp.ule.d`, `cmp.saf.d`, `cmp.sun.d`, `cmp.seq.d`, `cmp.sueq.d`, `cmp.slt.d`, `cmp.sult.d`,
  `cmp.sle.d`, `cmp.sule.d`, `cmp.or.d`, `cmp.une.d`, `cmp.ne.d`, `cmp.sor.d`, `cmp.sune.d`,
  `cmp.sne.d`. -/
  | cmpD (cond fd fs ft : W32)
  /-- `BC1EQZ ft, offset`: branch with a delay slot if bit 0 of `FPR[ft]` is 0 (COP1, `rs` = 01001,
  16-bit `offset`; BC1EQZ BC1NEZ, p.54-55). A CTI. -/
  | bc1eqz (ft off : W32)
  /-- `BC1NEZ ft, offset`: branch with a delay slot if bit 0 of `FPR[ft]` is 1 (COP1, `rs` = 01101;
  p.54-55). A CTI. -/
  | bc1nez (ft off : W32)
  /-- `SEL.S fd, fs, ft`: `FPR[fd] ← FPR[fd].bit0 ? FPR[ft] : FPR[fs]` (fmt = S, funct 0x10; SEL.fmt,
  p.368). -/
  | selS (fd fs ft : W32)
  /-- `SEL.D` (fmt = D, funct 0x10; p.368). -/
  | selD (fd fs ft : W32)
  /-- `SELEQZ.S fd, fs, ft`: `FPR[fd] ← FPR[ft].bit0 ? 0 : FPR[fs]` (fmt = S, funct 0x14;
  SELEQZ.fmt SELNEQZ.fmt, p.371). -/
  | seleqzS (fd fs ft : W32)
  /-- `SELEQZ.D` (fmt = D, funct 0x14; p.371). -/
  | seleqzD (fd fs ft : W32)
  /-- `SELNEZ.S fd, fs, ft`: `FPR[fd] ← FPR[ft].bit0 ? FPR[fs] : 0` (fmt = S, funct 0x17; p.371). -/
  | selnezS (fd fs ft : W32)
  /-- `SELNEZ.D` (fmt = D, funct 0x17; p.371). -/
  | selnezD (fd fs ft : W32)
  /-- `MADDF.S fd, fs, ft`: `FPR[fd] ← FPR[fd] + FPR[fs] × FPR[ft]`, fused (fmt = S, funct 0x18;
  MADDF.fmt MSUBF.fmt, p.259-260). -/
  | maddfS (fd fs ft : W32)
  /-- `MADDF.D` (fmt = D, funct 0x18; p.259-260). -/
  | maddfD (fd fs ft : W32)
  /-- `MSUBF.S fd, fs, ft`: `FPR[fd] ← FPR[fd] − FPR[fs] × FPR[ft]`, fused (fmt = S, funct 0x19;
  p.259-260). -/
  | msubfS (fd fs ft : W32)
  /-- `MSUBF.D` (fmt = D, funct 0x19; p.259-260). -/
  | msubfD (fd fs ft : W32)
  /-- `MAX.S fd, fs, ft`: `maxNum(FPR[fs], FPR[ft])` (fmt = S, funct 0x1e; MAX.fmt MIN.fmt MAXA.fmt
  MINA.fmt, p.262-265). -/
  | maxS (fd fs ft : W32)
  /-- `MAX.D` (fmt = D, funct 0x1e; p.262-265). -/
  | maxD (fd fs ft : W32)
  /-- `MIN.S fd, fs, ft`: `minNum(FPR[fs], FPR[ft])` (fmt = S, funct 0x1c; p.262-265). -/
  | minS (fd fs ft : W32)
  /-- `MIN.D` (fmt = D, funct 0x1c; p.262-265). -/
  | minD (fd fs ft : W32)
  /-- `MAXA.S fd, fs, ft`: `maxNumMag(FPR[fs], FPR[ft])` (fmt = S, funct 0x1f; p.262-265). -/
  | maxaS (fd fs ft : W32)
  /-- `MAXA.D` (fmt = D, funct 0x1f; p.262-265). -/
  | maxaD (fd fs ft : W32)
  /-- `MINA.S fd, fs, ft`: `minNumMag(FPR[fs], FPR[ft])` (fmt = S, funct 0x1d; p.262-265). -/
  | minaS (fd fs ft : W32)
  /-- `MINA.D` (fmt = D, funct 0x1d; p.262-265). -/
  | minaD (fd fs ft : W32)
  /-- `CLASS.S fd, fs`: the 10-bit class mask of `FPR[fs]` (fmt = S, `ft` = 0, funct 0x1b; CLASS.fmt,
  p.132-133). -/
  | classS (fd fs : W32)
  /-- `CLASS.D` (fmt = D, funct 0x1b; p.132-133). -/
  | classD (fd fs : W32)
  /-- `RINT.S fd, fs`: round to an integral value in the same format, per FCSR.RM (fmt = S, `ft` = 0,
  funct 0x1a; RINT.fmt, p.337-338). -/
  | rintS (fd fs : W32)
  /-- `RINT.D` (fmt = D, funct 0x1a; p.337-338). -/
  | rintD (fd fs : W32)
  -- Virtual processors (DVP/EVP): no-ops without multi-threading (`Config5.VP = 0`).
  /-- `DVP rt`: disable the other virtual processors (MD00086 Vol II-A Rev 6.06, DVP, p.172-173:
  COP0, `rs` = `MFMC0` = 01011, `rt` 20..16, bits 15..6 zero, bit 5 `sc` = 1, bits 4..3 zero, bits
  2..0 = 100). "For implementations that do not support multi-threading (Config5VP=0), this
  instruction must be treated as a NOP instruction" (p.172); this profile has `Config5.VP = 0`
  (MD00090 Vol III Rev 6.02 Table 9.69, p.263; DECISIONS D5), so it is a no-op: `GPR[rt]` is not
  written. A coprocessor-0 instruction ("If access to Coprocessor 0 is not enabled, a Coprocessor
  Unusable Exception is signaled", p.172). -/
  | dvp (rt : W32)
  /-- `EVP rt`: enable the virtual processors (MD00086 Vol II-A Rev 6.06, EVP, p.181-182: as DVP
  with `sc` = 0). With `Config5.VP = 0` "this instruction must be treated as a NOP instruction"
  (p.181); a coprocessor-0 instruction. -/
  | evp (rt : W32)
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

/-- Extract the raw 21-bit offset field of `BEQZC`/`BNEZC` (bits 20..0; B<cond>C, MD00086 Vol II-A
Rev 6.06 p.82), zero-extended to a `W32`. -/
def off21Of (w : W32) : W32 := (w.extractLsb 20 0).zeroExtend 32

/-- A `BEQZC`/`BNEZC` word: `opcode` bits 31..26, `rs` bits 25..21, 21-bit `offset` bits 20..0. -/
def mkOff21 (opcode rs off : W32) : W32 :=
  field 6 26 opcode ||| field 5 21 rs ||| field 21 0 off

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
  -- MUL/MUH, MULU/MUHU, DIV/MOD, DIVU/MODU: `sa` 00010 / 00011 selects (Table A.23, p.462).
  | 0x18 => if shamt == 2#32 then some (.mul rs rt rd) else decodeIf (shamt == 3#32) (.muh rs rt rd)
  | 0x19 => if shamt == 2#32 then some (.mulu rs rt rd) else decodeIf (shamt == 3#32) (.muhu rs rt rd)
  | 0x1a => if shamt == 2#32 then some (.div rs rt rd) else decodeIf (shamt == 3#32) (.mod rs rt rd)
  | 0x1b => if shamt == 2#32 then some (.divu rs rt rd) else decodeIf (shamt == 3#32) (.modu rs rt rd)
  | 0x35 => decodeIf (z shamt) (.seleqz rs rt rd)
  | 0x37 => decodeIf (z shamt) (.selnez rs rt rd)
  -- LSA: bits 10..8 zero, the 2-bit `sa` in bits 7..6 (LSA p.232).
  | 0x05 => decodeIf (z (sa3Of w)) (.lsa rs rt rd (sa2Of w))
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
  | 0x17 => decodeIf (rs == 0#32) (.sigrie imm)
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
    -- ALIGN: bits 10..8 = 010, `bp` in bits 7..6, any `rs` (ALIGN p.39).
    if sa3Of w == 2#32 then some (.align rs rt rd (sa2Of w)) else
    match shamt.toNat with
    | 0x10 => decodeIf (z rs) (.seb rd rt)
    | 0x18 => decodeIf (z rs) (.seh rd rt)
    | 0x02 => decodeIf (z rs) (.wsbh rd rt)
    | 0x00 => decodeIf (z rs) (.bitswap rd rt)  -- BITSWAP (p.92)
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
  -- `cache`: 9-bit offset in bits 15..7, bit 6 zero, `op` in bits 20..16 (CACHE p.114).
  | 0x25 => decodeIf (z (bit6Of w)) (.cache rs rt (off9Of w))
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
      if shamt == 1#32 then decodeIf (rs == 16#32 && z rt && z rd) .eretnc else
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
    -- `dvp`/`evp` (DVP p.172, EVP p.181): `rd` and bits 10..6 zero, bits 5..0 = `sc`||00||100.
    | 0x24 => decodeIf (z rd && z shamt) (.dvp rt)
    | 0x04 => decodeIf (z rd && z shamt) (.evp rt)
    | _ => none
  -- `RDPGPR` (0x0a) / `WRPGPR` (0x0e): bits 10..0 must be zero.
  | 0x0a => decodeIf (z shamt && z (functOf w)) (.rdpgpr rd rt)
  | 0x0e => decodeIf (z shamt && z (functOf w)) (.wrpgpr rd rt)
  | _ => none

/-- **The COP1 instructions of one format** (`S`, `fmt` = 0x10, or `D`, `fmt` = 0x11): the
constructor of each operation of the S and D function tables (Tables A.15/A.16, p.456-457); the
conversions CVT.S.fmt (`100000`, p.159) and CVT.D.fmt (`100001`, p.153) exist for one of the two
formats each. The arithmetic, SEL, MADDF/MSUBF and MIN/MAX
families take `fd, fs, ft`, the others `fd, fs`. -/
structure Cop1Fmt where
  add : W32 → W32 → W32 → Instruction
  sub : W32 → W32 → W32 → Instruction
  mul : W32 → W32 → W32 → Instruction
  div : W32 → W32 → W32 → Instruction
  sqrt : W32 → W32 → Instruction
  abs : W32 → W32 → Instruction
  mov : W32 → W32 → Instruction
  neg : W32 → W32 → Instruction
  roundL : W32 → W32 → Instruction
  truncL : W32 → W32 → Instruction
  ceilL : W32 → W32 → Instruction
  floorL : W32 → W32 → Instruction
  roundW : W32 → W32 → Instruction
  truncW : W32 → W32 → Instruction
  ceilW : W32 → W32 → Instruction
  floorW : W32 → W32 → Instruction
  recip : W32 → W32 → Instruction
  rsqrt : W32 → W32 → Instruction
  cvtW : W32 → W32 → Instruction
  cvtL : W32 → W32 → Instruction
  /-- CVT.S.fmt (function `100000`), which format D has (CVT.S.D) and S does not. -/
  cvtS : Option (W32 → W32 → Instruction)
  /-- CVT.D.fmt (function `100001`), which format S has (CVT.D.S) and D does not. -/
  cvtD : Option (W32 → W32 → Instruction)
  sel : W32 → W32 → W32 → Instruction
  seleqz : W32 → W32 → W32 → Instruction
  selnez : W32 → W32 → W32 → Instruction
  maddf : W32 → W32 → W32 → Instruction
  msubf : W32 → W32 → W32 → Instruction
  rint : W32 → W32 → Instruction
  cls : W32 → W32 → Instruction
  min : W32 → W32 → W32 → Instruction
  mina : W32 → W32 → W32 → Instruction
  max : W32 → W32 → W32 → Instruction
  maxa : W32 → W32 → W32 → Instruction

/-- Format S (`fmt` = 0x10): the instructions `decodeCop1Fmt decodeFmtS` emits. -/
def decodeFmtS : Cop1Fmt :=
  { add := .addS, sub := .subS, mul := .mulS, div := .divS, sqrt := .sqrtS, abs := .absS,
    mov := .movS, neg := .negS, roundL := .roundLS, truncL := .truncLS, ceilL := .ceilLS,
    floorL := .floorLS, roundW := .roundWS, truncW := .truncWS, ceilW := .ceilWS,
    floorW := .floorWS, recip := .recipS, rsqrt := .rsqrtS, cvtW := .cvtWS, cvtL := .cvtLS,
    cvtS := none, cvtD := some .cvtDS,
    sel := .selS, seleqz := .seleqzS, selnez := .selnezS, maddf := .maddfS, msubf := .msubfS,
    rint := .rintS, cls := .classS, min := .minS, mina := .minaS, max := .maxS, maxa := .maxaS }

/-- Format D (`fmt` = 0x11): the instructions `decodeCop1Fmt decodeFmtD` emits. -/
def decodeFmtD : Cop1Fmt :=
  { add := .addD, sub := .subD, mul := .mulD, div := .divD, sqrt := .sqrtD, abs := .absD,
    mov := .movD, neg := .negD, roundL := .roundLD, truncL := .truncLD, ceilL := .ceilLD,
    floorL := .floorLD, roundW := .roundWD, truncW := .truncWD, ceilW := .ceilWD,
    floorW := .floorWD, recip := .recipD, rsqrt := .rsqrtD, cvtW := .cvtWD, cvtL := .cvtLD,
    cvtS := some .cvtSD, cvtD := none,
    sel := .selD, seleqz := .seleqzD, selnez := .selnezD, maddf := .maddfD, msubf := .msubfD,
    rint := .rintD, cls := .classD, min := .minD, mina := .minaD, max := .maxD, maxa := .maxaD }

/-- The `condn` values of CMP.condn.fmt that are instructions (MD00086 Vol II-A Rev 6.06, Table A.17,
p.457: functions `000000`-`001111` and `010001`-`010011`, `011001`-`011011`; "All encodings of the
condn field that are not specified ... are reserved in Release 6 and produce a Reserved Instruction
exception", CMP.condn.fmt, p.136). -/
def cmpCondns : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 25, 26, 27]

/-- Whether `c` is one of `cmpCondns`. -/
def cmpCondnOK (c : W32) : Bool := cmpCondns.contains c.toNat

/-- **COP1** `fmt = S` (`rs` = 0x10, Table A.15, p.456) and `fmt = D` (`rs` = 0x11, Table A.16,
p.457): one table keyed by `funct`, instantiated per format by `t`. Fields: `ft` = `rt`, `fs` = `rd`,
`fd` = `sa`; the operations with no `ft` operand require `ft = 0`. Release 6 removed MOVCF (0x11),
MOVZ/MOVN (0x12/0x13) and C.cond.fmt (0x30-0x3f), and adds SEL 0x10, SELEQZ 0x14, SELNEZ 0x17,
MADDF 0x18, MSUBF 0x19, RINT 0x1a and CLASS 0x1b (`ft = 0`), MIN 0x1c, MINA 0x1d, MAX 0x1e, MAXA 0x1f
(SEL p.368, SELEQZ/SELNEZ p.371, MADDF/MSUBF p.259, RINT p.337, CLASS p.132). The function values
of MIN/MINA/MAX/MAXA are those of the instruction page's diagrams (MAX.fmt, p.262: MIN `011100`, MINA
`011101`, MAX `011110`, MAXA `011111`); Table A.15 (p.456) prints MIN, MAX, MINA, MAXA in that order
instead. -/
def decodeCop1Fmt (t : Cop1Fmt) (w : W32) : Option Instruction :=
  let ft := rtOf w
  let fs := rdOf w
  let fd := shamtOf w
  let unary (mk : W32 → W32 → Instruction) : Option Instruction := decodeIf (ft == 0#32) (mk fd fs)
  match (functOf w).toNat with
  | 0x00 => some (t.add fd fs ft)
  | 0x01 => some (t.sub fd fs ft)
  | 0x02 => some (t.mul fd fs ft)
  | 0x03 => some (t.div fd fs ft)
  | 0x04 => unary t.sqrt
  | 0x05 => unary t.abs
  | 0x06 => unary t.mov
  | 0x07 => unary t.neg
  | 0x08 => unary t.roundL
  | 0x09 => unary t.truncL
  | 0x0a => unary t.ceilL
  | 0x0b => unary t.floorL
  | 0x0c => unary t.roundW
  | 0x0d => unary t.truncW
  | 0x0e => unary t.ceilW
  | 0x0f => unary t.floorW
  | 0x10 => some (t.sel fd fs ft)
  | 0x14 => some (t.seleqz fd fs ft)
  | 0x15 => unary t.recip
  | 0x16 => unary t.rsqrt
  | 0x17 => some (t.selnez fd fs ft)
  | 0x18 => some (t.maddf fd fs ft)
  | 0x19 => some (t.msubf fd fs ft)
  | 0x1a => unary t.rint
  | 0x1b => unary t.cls
  | 0x1c => some (t.min fd fs ft)
  | 0x1d => some (t.mina fd fs ft)
  | 0x1e => some (t.max fd fs ft)
  | 0x1f => some (t.maxa fd fs ft)
  | 0x20 => t.cvtS.bind unary
  | 0x21 => t.cvtD.bind unary
  | 0x24 => unary t.cvtW
  | 0x25 => unary t.cvtL
  | _ => none

/-- **COP1** (opcode 0x11), keyed by `rs` (Table A.14, p.456). Release 6 removed BC1 (`rs` =
0x08: BC1F/BC1T/BC1FL/BC1TL).
Release 6 adds BC1EQZ (`rs` = 0x09) and BC1NEZ (`rs` = 0x0d) (Table A.14, p.456; BC1EQZ BC1NEZ,
p.54), and CMP.condn.S / CMP.condn.D encoded with `fmt = W` / `L` and function `0 condn` (Table A.17,
p.457: "Release 6 introduces the CMP.condn fmt instruction family ... .S and .D for CMP.condn fmt are
encoded as .W 10100 and .L 10101"); only the `condn` values of Table A.17 decode (`cmpCondnOK`). -/
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
  | 0x10 => decodeCop1Fmt decodeFmtS w
  | 0x11 => decodeCop1Fmt decodeFmtD w
  | 0x14 =>  -- fmt = W
    match (functOf w).toNat with
    | 0x20 => decodeIf (z rt) (.cvtSW shamt rd)
    | 0x21 => decodeIf (z rt) (.cvtDW shamt rd)
    | _ => decodeIf (cmpCondnOK (functOf w)) (.cmpS (functOf w) shamt rd rt)
  | 0x15 =>  -- fmt = L
    match (functOf w).toNat with
    | 0x20 => decodeIf (z rt) (.cvtSL shamt rd)
    | 0x21 => decodeIf (z rt) (.cvtDL shamt rd)
    | _ => decodeIf (cmpCondnOK (functOf w)) (.cmpD (functOf w) shamt rd rt)
  | 0x09 => some (.bc1eqz rt (immOf w))
  | 0x0d => some (.bc1nez rt (immOf w))
  | _ => none

/-! ### The Release 6 compact branches: one opcode, several instructions

Release 6 packs several compact branches into one primary opcode and tells them apart by comparing
the `rs` and `rt` fields ("the encoding 010110.rs rt.offset16 is BGEC if neither rs nor rt are 00000
and rs is not equal to rt, but is BGEZC if rs is the same as rt, and is BLEZC if rs is 00000 and rt
is not", MD00086 Vol II-A Rev 6.06 §A.4, p.463; Table A.26 "B*C compact branch encodings", p.464).
Three shapes cover the nine shared opcodes. -/

/-- **POP06, POP07, POP26, POP27 with `rt ≠ 0`** (Table A.26, p.464): `rs = 0` is the
compare-with-zero form `zero rt` (BLEZALC, BGTZALC, BLEZC, BGTZC), `rs = rt` the other
compare-with-zero form `eq rt` (BGEZALC, BLTZALC, BGEZC, BLTZC), any other `rs` the two-register
form `two rs rt` (BGEUC, BLTUC, BGEC, BLTC). (`rt = 0` is BLEZ/BGTZ for POP06/POP07 and the removed
BLEZL/BGTZL for POP26/POP27: the caller decides.) -/
def decodeZeroEqTwo (zero eq : W32 → W32 → Instruction) (two : W32 → W32 → W32 → Instruction)
    (w : W32) : Instruction :=
  let rs := rsOf w
  let rt := rtOf w
  if rs == 0#32 then zero rt (immOf w)
  else if rs == rt then eq rt (immOf w)
  else two rs rt (immOf w)

/-- **POP10, POP30** (Table A.26, p.464; BOVC/BNVC p.107: "rs >= rt"): `rs < rt` is the
branch-and-link on zero `zero rt` when `rs = 0` (BEQZALC, BNEZALC) and the two-register compare
`two rs rt` otherwise (BEQC, BNEC); `rs ≥ rt` (including `rs = rt = 0`) is the overflow branch
`ovf rs rt` (BOVC, BNVC). -/
def decodeLtGe (zero : W32 → W32 → Instruction) (two ovf : W32 → W32 → W32 → Instruction)
    (w : W32) : Instruction :=
  let rs := rsOf w
  let rt := rtOf w
  if rs.toNat < rt.toNat then
    if rs == 0#32 then zero rt (immOf w) else two rs rt (immOf w)
  else ovf rs rt (immOf w)

/-- **POP66, POP76** (Table A.26, p.464; JIC p.205: "JIC and BEQZC differ only in the rs field"):
`rs = 0` is the compact jump `jmp rt offset16` (JIC, JIALC), any other `rs` the compare-with-zero
`z rs offset21` (BEQZC, BNEZC). -/
def decodeJumpOrZ (jmp z : W32 → W32 → Instruction) (w : W32) : Instruction :=
  if rsOf w == 0#32 then jmp (rtOf w) (immOf w) else z (rsOf w) (off21Of w)

/-- **The Release 6 primary opcode table** (Table A.2, p.451). Removed by Release 6 (do not decode):
ADDI (0x08), COP1X (0x13: "Release 6 removes all pre-Release 6 COP1X instructions", Table A.21,
p.459), BEQL/BNEL/BLEZL/BGTZL (0x14-0x17 with `rt = 0`), SPECIAL2 (0x1c), JALX (0x1d), LWL/LWR/
SWL/SWR (0x22, 0x26, 0x2a, 0x2e), CACHE (0x2f), LL (0x30), LWC2/LDC2/SWC2/SDC2 (0x32, 0x36, 0x3a,
0x3e), PREF (0x33), SC (0x38). LUI is AUI with `rs = 0` (0x0f). Release 6 reuses 0x06/0x07 with
`rt ≠ 0` (POP06/POP07), 0x08 (POP10), 0x16/0x17 with `rt ≠ 0` (POP26/POP27), 0x18 (POP30), 0x32
(BC), 0x36 (POP66), 0x3a (BALC) and 0x3e (POP76) for the compact branches (Table A.26, p.464).
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
  | 0x06 => if z rt then some (.blez rs imm) else some (decodeZeroEqTwo .blezalc .bgezalc .bgeuc w)
  | 0x07 => if z rt then some (.bgtz rs imm) else some (decodeZeroEqTwo .bgtzalc .bltzalc .bltuc w)
  | 0x08 => some (decodeLtGe .beqzalc .beqc .bovc w)
  | 0x18 => some (decodeLtGe .bnezalc .bnec .bnvc w)
  | 0x16 => decodeIf (!z rt) (decodeZeroEqTwo .blezc .bgezc .bgec w)
  | 0x17 => decodeIf (!z rt) (decodeZeroEqTwo .bgtzc .bltzc .bltc w)
  | 0x32 => some (.bc (targetOf w))
  | 0x3a => some (.balc (targetOf w))
  | 0x36 => some (decodeJumpOrZ .jic .beqzc w)
  | 0x3e => some (decodeJumpOrZ .jialc .bnezc w)
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
  | 0x3b =>  -- PCREL
    match (pcrelOf w).toNat with
    | 0 => some (.addiupc rs (imm19Of w))
    | 1 => some (.lwpc rs (imm19Of w))
    | _ => if rt == 0x1e#32 then some (.auipc rs imm)
           else decodeIf (rt == 0x1f#32) (.aluipc rs imm)
  | _ => none

/-- **The decoder table of each release.** An instruction is available in a release exactly when
that release's table emits it. -/
def decodeFor : Release → W32 → Option Instruction
  | .r6 => decodePrimary

/-- Decode a raw 32-bit instruction word into an `Instruction`, or `none` if the word is not the
canonical encoding of an instruction of this profile's release (`step` then raises Reserved
Instruction or Coprocessor Unusable). -/
def decode (w : W32) : Option Instruction := decodeFor profile.release w

/-- A COP1 register-format word (opcode COP1 = 0x11): `fmt` in the `rs` position (bits 25..21),
`ft` in `rt`, `fs` in `rd`, `fd` in `sa`, then the function field (Tables A.14-A.17, p.456-457). The
moves `mfc1`, `mtc1`, ... use it with `rt` and `fs` in the `ft`/`fs` positions and `fd = 0`.
Reducible, so the field lemmas about `x ||| mkRT ..` apply to it unchanged. -/
abbrev cop1R (fmt ft fs fd funct : W32) : W32 := (0x11#32 <<< 26) ||| mkRT fmt ft fs fd funct

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
  -- Rotate: the `R` bit (bit 21 of ROTR, bit 6 of ROTRV) set in SRL's/SRLV's encoding.
  | .rotr  rd rt sa => mkRT 0x01#32 rt rd sa 0x02#32
  | .rotrv rd rt rs => mkRT rs rt rd 0x01#32 0x06#32
  | .jalr rs rd => mkRT rs 0#32 rd 0#32 0x09#32
  | .jalrHb rs rd => mkRT rs 0#32 rd 16#32 0x09#32
  -- CLO/CLZ (Release 6): SPECIAL, `rt` = 0, `sa` = 00001 (CLO p.134, CLZ p.135).
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
  -- sync: `stype` in bits 10..6 (SYNC p.407).
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
  -- Coprocessor 1 (FPU): `cop1R fmt ft fs fd funct` (the moves: `cop1R sub rt fs 0 0`).
  | .mfc1 rt fs => cop1R 0x00#32 rt fs 0#32 0#32
  | .mtc1 rt fs => cop1R 0x04#32 rt fs 0#32 0#32
  | .mfhc1 rt fs => cop1R 0x03#32 rt fs 0#32 0#32
  | .mthc1 rt fs => cop1R 0x07#32 rt fs 0#32 0#32
  | .cfc1 rt fs => cop1R 0x02#32 rt fs 0#32 0#32
  | .ctc1 rt fs => cop1R 0x06#32 rt fs 0#32 0#32
  | .lwc1 rs ft imm => mkIT 0x31#32 rs ft imm
  | .swc1 rs ft imm => mkIT 0x39#32 rs ft imm
  | .ldc1 rs ft imm => mkIT 0x35#32 rs ft imm
  | .sdc1 rs ft imm => mkIT 0x3d#32 rs ft imm
  | .addS fd fs ft => cop1R 0x10#32 ft fs fd 0x00#32
  | .subS fd fs ft => cop1R 0x10#32 ft fs fd 0x01#32
  | .mulS fd fs ft => cop1R 0x10#32 ft fs fd 0x02#32
  | .divS fd fs ft => cop1R 0x10#32 ft fs fd 0x03#32
  | .sqrtS fd fs => cop1R 0x10#32 0#32 fs fd 0x04#32
  | .absS fd fs => cop1R 0x10#32 0#32 fs fd 0x05#32
  | .movS fd fs => cop1R 0x10#32 0#32 fs fd 0x06#32
  | .negS fd fs => cop1R 0x10#32 0#32 fs fd 0x07#32
  | .recipS fd fs => cop1R 0x10#32 0#32 fs fd 0x15#32
  | .rsqrtS fd fs => cop1R 0x10#32 0#32 fs fd 0x16#32
  | .roundWS fd fs => cop1R 0x10#32 0#32 fs fd 0x0c#32
  | .truncWS fd fs => cop1R 0x10#32 0#32 fs fd 0x0d#32
  | .ceilWS fd fs => cop1R 0x10#32 0#32 fs fd 0x0e#32
  | .floorWS fd fs => cop1R 0x10#32 0#32 fs fd 0x0f#32
  | .cvtWS fd fs => cop1R 0x10#32 0#32 fs fd 0x24#32
  | .addD fd fs ft => cop1R 0x11#32 ft fs fd 0x00#32
  | .subD fd fs ft => cop1R 0x11#32 ft fs fd 0x01#32
  | .mulD fd fs ft => cop1R 0x11#32 ft fs fd 0x02#32
  | .divD fd fs ft => cop1R 0x11#32 ft fs fd 0x03#32
  | .sqrtD fd fs => cop1R 0x11#32 0#32 fs fd 0x04#32
  | .absD fd fs => cop1R 0x11#32 0#32 fs fd 0x05#32
  | .movD fd fs => cop1R 0x11#32 0#32 fs fd 0x06#32
  | .negD fd fs => cop1R 0x11#32 0#32 fs fd 0x07#32
  | .recipD fd fs => cop1R 0x11#32 0#32 fs fd 0x15#32
  | .rsqrtD fd fs => cop1R 0x11#32 0#32 fs fd 0x16#32
  | .roundWD fd fs => cop1R 0x11#32 0#32 fs fd 0x0c#32
  | .truncWD fd fs => cop1R 0x11#32 0#32 fs fd 0x0d#32
  | .ceilWD fd fs => cop1R 0x11#32 0#32 fs fd 0x0e#32
  | .floorWD fd fs => cop1R 0x11#32 0#32 fs fd 0x0f#32
  | .cvtWD fd fs => cop1R 0x11#32 0#32 fs fd 0x24#32
  | .cvtDS fd fs => cop1R 0x10#32 0#32 fs fd 0x21#32
  | .cvtSD fd fs => cop1R 0x11#32 0#32 fs fd 0x20#32
  | .cvtSW fd fs => cop1R 0x14#32 0#32 fs fd 0x20#32
  | .cvtDW fd fs => cop1R 0x14#32 0#32 fs fd 0x21#32
  | .eretnc => (0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 1#32 0x18#32
  | .sigrie code => mkIT 0x01#32 0#32 0x17#32 code
  | .cache base op off => (0x1f#32 <<< 26) ||| mkOff9 base op off 0x25#32
  -- Compact branches and jumps (Table A.26, p.464): the canonical word of each form.
  | .bc off => (0x32#32 <<< 26) ||| mkJT off
  | .balc off => (0x3a#32 <<< 26) ||| mkJT off
  | .beqc rs rt off => mkIT 0x08#32 rs rt off
  | .bnec rs rt off => mkIT 0x18#32 rs rt off
  | .bltc rs rt off => mkIT 0x17#32 rs rt off
  | .bgec rs rt off => mkIT 0x16#32 rs rt off
  | .bltuc rs rt off => mkIT 0x07#32 rs rt off
  | .bgeuc rs rt off => mkIT 0x06#32 rs rt off
  | .blezc rt off => mkIT 0x16#32 0#32 rt off
  | .bgezc rt off => mkIT 0x16#32 rt rt off
  | .bgtzc rt off => mkIT 0x17#32 0#32 rt off
  | .bltzc rt off => mkIT 0x17#32 rt rt off
  | .beqzc rs off => mkOff21 0x36#32 rs off
  | .bnezc rs off => mkOff21 0x3e#32 rs off
  | .blezalc rt off => mkIT 0x06#32 0#32 rt off
  | .bgezalc rt off => mkIT 0x06#32 rt rt off
  | .bgtzalc rt off => mkIT 0x07#32 0#32 rt off
  | .bltzalc rt off => mkIT 0x07#32 rt rt off
  | .beqzalc rt off => mkIT 0x08#32 0#32 rt off
  | .bnezalc rt off => mkIT 0x18#32 0#32 rt off
  | .bovc rs rt off => mkIT 0x08#32 rs rt off
  | .bnvc rs rt off => mkIT 0x18#32 rs rt off
  | .jic rt off => mkIT 0x36#32 0#32 rt off
  | .jialc rt off => mkIT 0x3e#32 0#32 rt off
  | .cvtLS fd fs => cop1R 0x10#32 0#32 fs fd 0x25#32
  | .cvtLD fd fs => cop1R 0x11#32 0#32 fs fd 0x25#32
  | .roundLS fd fs => cop1R 0x10#32 0#32 fs fd 0x08#32
  | .roundLD fd fs => cop1R 0x11#32 0#32 fs fd 0x08#32
  | .truncLS fd fs => cop1R 0x10#32 0#32 fs fd 0x09#32
  | .truncLD fd fs => cop1R 0x11#32 0#32 fs fd 0x09#32
  | .ceilLS fd fs => cop1R 0x10#32 0#32 fs fd 0x0a#32
  | .ceilLD fd fs => cop1R 0x11#32 0#32 fs fd 0x0a#32
  | .floorLS fd fs => cop1R 0x10#32 0#32 fs fd 0x0b#32
  | .floorLD fd fs => cop1R 0x11#32 0#32 fs fd 0x0b#32
  | .cvtSL fd fs => cop1R 0x15#32 0#32 fs fd 0x20#32
  | .cvtDL fd fs => cop1R 0x15#32 0#32 fs fd 0x21#32
  | .cmpS cond fd fs ft => cop1R 0x14#32 ft fs fd cond
  | .cmpD cond fd fs ft => cop1R 0x15#32 ft fs fd cond
  | .bc1eqz ft off => mkIT 0x11#32 0x09#32 ft off
  | .bc1nez ft off => mkIT 0x11#32 0x0d#32 ft off
  | .selS fd fs ft => cop1R 0x10#32 ft fs fd 0x10#32
  | .selD fd fs ft => cop1R 0x11#32 ft fs fd 0x10#32
  | .seleqzS fd fs ft => cop1R 0x10#32 ft fs fd 0x14#32
  | .seleqzD fd fs ft => cop1R 0x11#32 ft fs fd 0x14#32
  | .selnezS fd fs ft => cop1R 0x10#32 ft fs fd 0x17#32
  | .selnezD fd fs ft => cop1R 0x11#32 ft fs fd 0x17#32
  | .maddfS fd fs ft => cop1R 0x10#32 ft fs fd 0x18#32
  | .maddfD fd fs ft => cop1R 0x11#32 ft fs fd 0x18#32
  | .msubfS fd fs ft => cop1R 0x10#32 ft fs fd 0x19#32
  | .msubfD fd fs ft => cop1R 0x11#32 ft fs fd 0x19#32
  | .rintS fd fs => cop1R 0x10#32 0#32 fs fd 0x1a#32
  | .rintD fd fs => cop1R 0x11#32 0#32 fs fd 0x1a#32
  | .classS fd fs => cop1R 0x10#32 0#32 fs fd 0x1b#32
  | .classD fd fs => cop1R 0x11#32 0#32 fs fd 0x1b#32
  | .minS fd fs ft => cop1R 0x10#32 ft fs fd 0x1c#32
  | .minD fd fs ft => cop1R 0x11#32 ft fs fd 0x1c#32
  | .minaS fd fs ft => cop1R 0x10#32 ft fs fd 0x1d#32
  | .minaD fd fs ft => cop1R 0x11#32 ft fs fd 0x1d#32
  | .maxS fd fs ft => cop1R 0x10#32 ft fs fd 0x1e#32
  | .maxD fd fs ft => cop1R 0x11#32 ft fs fd 0x1e#32
  | .maxaS fd fs ft => cop1R 0x10#32 ft fs fd 0x1f#32
  | .maxaD fd fs ft => cop1R 0x11#32 ft fs fd 0x1f#32
  | .dvp rt => (0x10#32 <<< 26) ||| mkRT 0x0b#32 rt 0#32 0#32 0x24#32
  | .evp rt => (0x10#32 <<< 26) ||| mkRT 0x0b#32 rt 0#32 0#32 0x04#32
