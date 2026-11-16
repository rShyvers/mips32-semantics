# MIPS32 Release 6 Instruction Reference

Per-instruction reference for the instruction set modeled by `Semantics/`: one entry for each of the 203 constructors of
`Instruction`, each citing its page of MD00086 Vol II-A Rev 6.06, followed by the instructions Release 6 removed (with their pages).
The generated matrix that follows an instruction from its manual page to its tests is [`TRACE.md`](../TRACE.md); the classification of all 263
manual pages is [`R6-COVERAGE.md`](R6-COVERAGE.md); the pins (choices the manual leaves open) and the divergences of QEMU from
the manual are in [`SPEC-NOTES.md`](SPEC-NOTES.md).

**Citation convention.** Document, revision, instruction or section, and the *printed* page, e.g. "MD00086 Vol II-A Rev 6.06, MUL, p.299".
The three normative documents are MD00082 Vol I-A Rev 6.01 ("Vol I"), MD00086 Vol II-A Rev 6.06 ("Vol II") and MD00090 Vol III Rev 6.02
("Vol III"), looked up with `python3 manuals/mipsdoc.py`.

**What an entry is.** The "Constructor" line is the doc comment of the constructor in `Semantics/Instruction.lean` (the model's
statement of what the instruction does; the encoding is in `decode`/`encode` there). "Proofs" names the spec theorem
`<ctor>_spec_raw` (it restates what `step` computes; it is not independent of `Step.lean`) and the refinement theorem
`Refine.<ctor>_refines` (the independent result: `step` agrees with the transcription of the manual's Operation in `Semantics/Manual/`).
Exact operand semantics, exceptions and the pseudocode are on the cited manual page.

## Global rules (Release 6)

1. **Little-endian**, `Config.BE = 0`, `Config5.DEC = 0` ("Only Little-Endian mode supported. Any implementation must support Little-endian
   mode", Vol III Config5, p.261). The byte order of memory is one constant of the profile.
2. **PC and delay slots.** Branches and jumps of the classic kind (`beq`, `bne`, `blez`, `bgtz`, `bltz`, `bgez`, the REGIMM and
   FP-condition branches, `j`, `jal`, `jalr`, `nal`, `bal`) have one delay slot; the branch-likely forms are removed. The Release 6
   compact branches and jumps (`bc`, `balc`, `beqc`, ..., `jic`, `jialc`) have no delay slot but a *forbidden slot*: a control-transfer
   instruction in a delay slot or forbidden slot raises Reserved Instruction (Vol II BEQ p.72, JALR p.196; Vol I 5.3.2.1-5.3.2.2, p.62),
   with EPC = the branch and `Cause.BD` set (pin D6, SPEC-NOTES). The pending branch target is the single state field `pendingBranch`.
3. **`$zero`** reads 0 and ignores writes. Release 6 has no `HI`/`LO`: multiply and divide write a GPR (`mul`, `muh`, `div`, `mod`, ...).
4. **Alignment.** Every misaligned load or store raises Address Error; `ll`/`sc` always do (Vol I Appendix B.2, p.128; Vol II SC p.349).
5. **Address translation.** Fixed Mapping MMU, Kernel/User Mode, no TLB (Vol I 2.4.2, p.32; Vol III A.1.3, p.317); the User-Mode address check
   and the segments are in `Semantics/State.lean` (`translate`) and proved in `Semantics/Specs/Mmu.lean`.
6. **Exceptions are state transitions, not halts.** `step` never halts; a fault updates Cause, EPC, Status and the PC as the manual's
   exception processing says (Vol III 6.2, p.86-100). Only the hosted run (`Semantics/Env.lean`, not architecture) stops.
7. **FPU.** 64-bit FPU, `Status.FR = 1`, IEEE 754-2008 NaN encoding and ABS/NEG (`FIR.Has2008 = 1`, `FCSR.NAN2008 = ABS2008 = 1`); the
   arithmetic is on bit patterns in `Semantics/FpOps.lean`, proved against `FpOpsSpec.lean`.
8. **Removed in Release 6** instructions do not decode: the word raises Reserved Instruction (or Coprocessor Unusable in the COP1/COP2 space
   as the profile decides); see the last section.

## Integer ALU, register form

### add

- **Manual:** MD00086 Vol II-A Rev 6.06, ADD (Add Word), p.33.
- **Constructor:** `add rs rt rd` (`Semantics/Instruction.lean`): `$rd = $rs + $rt`, signed; traps on overflow (opcode 0, funct 0x20).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `add_spec_raw` (`Semantics/Specs/Arith.lean`) and 3 more; refinement of the manual's Operation: `Refine.add_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 2 in tests/corpus, 6 in tests/oracle; 12 in-file `#guard`/`example` statements.

### addu

- **Manual:** MD00086 Vol II-A Rev 6.06, ADDU (Add Unsigned Word), p.38-39.
- **Constructor:** `addu rs rt rd` (`Semantics/Instruction.lean`): `$rd = $rs + $rt`, wraps (opcode 0, funct 0x21).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `addu_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.addu_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 12 in tests/corpus, 2 in tests/equiv, 2 in tests/asm, 45 in tests/oracle; 7 in-file `#guard`/`example` statements.

### sub

- **Manual:** MD00086 Vol II-A Rev 6.06, SUB (Subtract Word), p.388.
- **Constructor:** `sub rs rt rd` (`Semantics/Instruction.lean`): `$rd = $rs - $rt`, signed; traps on overflow (opcode 0, funct 0x22).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `sub_spec_raw` (`Semantics/Specs/Arith.lean`) and 1 more; refinement of the manual's Operation: `Refine.sub_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/equiv, 2 in tests/oracle; 7 in-file `#guard`/`example` statements.

### subu

- **Manual:** MD00086 Vol II-A Rev 6.06, SUBU (Subtract Unsigned Word), p.390.
- **Constructor:** `subu rs rt rd` (`Semantics/Instruction.lean`): `$rd = $rs - $rt`, wraps (opcode 0, funct 0x23).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `subu_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.subu_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/equiv, 14 in tests/oracle; 5 in-file `#guard`/`example` statements.

### and

- **Manual:** MD00086 Vol II-A Rev 6.06, AND (and), p.44.
- **Constructor:** `and rs rt rd` (`Semantics/Instruction.lean`): `$rd = $rs & $rt` (opcode 0, funct 0x24).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `and_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.and_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/corpus, 20 in tests/oracle; 3 in-file `#guard`/`example` statements.

### or

- **Manual:** MD00086 Vol II-A Rev 6.06, OR (Or), p.314.
- **Constructor:** `or rs rt rd` (`Semantics/Instruction.lean`): `$rd = $rs | $rt` (opcode 0, funct 0x25).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `or_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.or_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 16 in tests/oracle; 3 in-file `#guard`/`example` statements.

### xor

- **Manual:** MD00086 Vol II-A Rev 6.06, XOR (Exclusive OR), p.446.
- **Constructor:** `xor rs rt rd` (`Semantics/Instruction.lean`): `$rd = $rs ^ $rt` (opcode 0, funct 0x26).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `xor_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.xor_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/corpus, 2 in tests/oracle; 3 in-file `#guard`/`example` statements.

### nor

- **Manual:** MD00086 Vol II-A Rev 6.06, NOR (Not Or), p.313.
- **Constructor:** `nor rs rt rd` (`Semantics/Instruction.lean`): `$rd = ~($rs | $rt)` (opcode 0, funct 0x27).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `nor_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.nor_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/equiv, 2 in tests/oracle; 4 in-file `#guard`/`example` statements.

### slt

- **Manual:** MD00086 Vol II-A Rev 6.06, SLT (Set on Less Than), p.378.
- **Constructor:** `slt rs rt rd` (`Semantics/Instruction.lean`): `$rd = ($rs < $rt) ? 1 : 0`, signed (opcode 0, funct 0x2a).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `slt_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.slt_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 2 in tests/corpus, 2 in tests/equiv, 1 in tests/oracle; 7 in-file `#guard`/`example` statements.

### sltu

- **Manual:** MD00086 Vol II-A Rev 6.06, SLTU (Set on Less Than Unsigned), p.381.
- **Constructor:** `sltu rs rt rd` (`Semantics/Instruction.lean`): `$rd = ($rs <u $rt) ? 1 : 0`, unsigned (opcode 0, funct 0x2b).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `sltu_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.sltu_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/corpus, 4 in tests/oracle; 7 in-file `#guard`/`example` statements.

## Shifts by a constant

### sll

- **Manual:** MD00086 Vol II-A Rev 6.06, SLL (Shift Word Left Logical), p.376.
- **Constructor:** `sll rd rt shamt` (`Semantics/Instruction.lean`): `$rd = $rt << shamt`, logical (opcode 0, funct 0x00). The no-op idioms `nop` (`sll $0,$0,0`), `ssnop` (shamt 1) and `ehb` (shamt 3) are this instruction with `rd = 0`; `sll $0,$0,5` is `pause` (below), not `sll`.
- **Step arm:** `Semantics/Exec/Shift.lean`.
- **Proofs:** spec theorem `sll_spec_raw` (`Semantics/Specs/Shift.lean`) and 1 more; refinement of the manual's Operation: `Refine.sll_refines` (`Semantics/Refine/Shift.lean`).
- **Tests:** 6 in tests/corpus, 4 in tests/equiv, 9 in tests/asm, 66 in tests/oracle; 16 in-file `#guard`/`example` statements.

### pause

- **Manual:** MD00086 Vol II-A Rev 6.06, PAUSE (Wait for the LLBit to clear.), p.317-318.
- **Constructor:** `pause` (`Semantics/Instruction.lean`): `PAUSE`: wait for `LLbit` to clear (MD00086 Vol II-A Rev 6.06, PAUSE, p.317: SPECIAL, `rs` = `rt` = `rd` = 0, `sa` = 5, funct `SLL`). A control transfer instruction for the delay-slot rule ("CTIs include all branches and jumps, NAL, ERET, ERETNC, DERET, WAIT, and PAUSE", p.317; Release 6 requires Reserved Instruction in a delay slot).
- **Step arm:** `Semantics/Exec/System.lean`.
- **Proofs:** spec theorem `pause_spec_raw` (`Semantics/Specs/Cp0.lean`) and 1 more; refinement of the manual's Operation: `Refine.pause_refines` (`Semantics/Refine/System.lean`).
- **Tests:** 1 in tests/oracle; 16 in-file `#guard`/`example` statements.

### srl

- **Manual:** MD00086 Vol II-A Rev 6.06, SRL (Shift Word Right Logical), p.385.
- **Constructor:** `srl rd rt shamt` (`Semantics/Instruction.lean`): `$rd = $rt >> shamt`, logical/zero-fill (opcode 0, funct 0x02).
- **Step arm:** `Semantics/Exec/Shift.lean`.
- **Proofs:** spec theorem `srl_spec_raw` (`Semantics/Specs/Shift.lean`) and 2 more; refinement of the manual's Operation: `Refine.srl_refines` (`Semantics/Refine/Shift.lean`).
- **Tests:** 2 in tests/corpus, 4 in tests/asm, 25 in tests/oracle; 6 in-file `#guard`/`example` statements.

### sra

- **Manual:** MD00086 Vol II-A Rev 6.06, SRA (Shift Word Right Arithmetic), p.383.
- **Constructor:** `sra rd rt shamt` (`Semantics/Instruction.lean`): `$rd = $rt >> shamt`, arithmetic/sign-fill (opcode 0, funct 0x03).
- **Step arm:** `Semantics/Exec/Shift.lean`.
- **Proofs:** spec theorem `sra_spec_raw` (`Semantics/Specs/Shift.lean`); refinement of the manual's Operation: `Refine.sra_refines` (`Semantics/Refine/Shift.lean`).
- **Tests:** 1 in tests/corpus, 3 in tests/equiv, 1 in tests/oracle; 4 in-file `#guard`/`example` statements.

## Shifts by a register

### sllv

- **Manual:** MD00086 Vol II-A Rev 6.06, SLLV (Shift Word Left Logical Variable), p.377.
- **Constructor:** `sllv rd rt rs` (`Semantics/Instruction.lean`): `$rd = $rt << ($rs & 0x1f)`, logical, shift amount from a register's low 5 bits (opcode 0, funct 0x04). MIPS32.
- **Step arm:** `Semantics/Exec/Shift.lean`.
- **Proofs:** spec theorem `sllv_spec_raw` (`Semantics/Specs/Shift.lean`); refinement of the manual's Operation: `Refine.sllv_refines` (`Semantics/Refine/Shift.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/oracle; 7 in-file `#guard`/`example` statements.

### srlv

- **Manual:** MD00086 Vol II-A Rev 6.06, SRLV (Shift Word Right Logical Variable), p.386.
- **Constructor:** `srlv rd rt rs` (`Semantics/Instruction.lean`): `$rd = $rt >> ($rs & 0x1f)`, logical/zero-fill, shift amount from a register's low 5 bits (opcode 0, funct 0x06). MIPS32.
- **Step arm:** `Semantics/Exec/Shift.lean`.
- **Proofs:** spec theorem `srlv_spec_raw` (`Semantics/Specs/Shift.lean`); refinement of the manual's Operation: `Refine.srlv_refines` (`Semantics/Refine/Shift.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/oracle; 6 in-file `#guard`/`example` statements.

### srav

- **Manual:** MD00086 Vol II-A Rev 6.06, SRAV (Shift Word Right Arithmetic Variable), p.384.
- **Constructor:** `srav rd rt rs` (`Semantics/Instruction.lean`): `$rd = $rt >> ($rs & 0x1f)`, arithmetic/sign-fill, shift amount from a register's low 5 bits (opcode 0, funct 0x07). MIPS32.
- **Step arm:** `Semantics/Exec/Shift.lean`.
- **Proofs:** spec theorem `srav_spec_raw` (`Semantics/Specs/Shift.lean`); refinement of the manual's Operation: `Refine.srav_refines` (`Semantics/Refine/Shift.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/oracle; 5 in-file `#guard`/`example` statements.

## Rotates

### rotr

- **Manual:** MD00086 Vol II-A Rev 6.06, ROTR (Rotate Word Right), p.339.
- **Constructor:** `rotr rd rt sa` (`Semantics/Instruction.lean`): `$rd = $rt` rotated right by the constant `sa` (0-31) bits -- bits shifted off the bottom wrap around to the top, unlike `srl`'s zero-fill (opcode 0, funct 0x02, `rs` field = 0x01).
- **Step arm:** `Semantics/Exec/Shift.lean`.
- **Proofs:** spec theorem `rotr_spec_raw` (`Semantics/Specs/Shift.lean`) and 2 more; refinement of the manual's Operation: `Refine.rotr_refines` (`Semantics/Refine/Shift.lean`).
- **Tests:** 1 in tests/oracle; 6 in-file `#guard`/`example` statements.

### rotrv

- **Manual:** MD00086 Vol II-A Rev 6.06, ROTRV (Rotate Word Right Variable), p.340.
- **Constructor:** `rotrv rd rt rs` (`Semantics/Instruction.lean`): `$rd = $rt` rotated right by `$rs & 0x1f` bits, rotate amount from a register's low 5 bits (opcode 0, funct 0x06, `shamt` field = 0x01).
- **Step arm:** `Semantics/Exec/Shift.lean`.
- **Proofs:** spec theorem `rotrv_spec_raw` (`Semantics/Specs/Shift.lean`); refinement of the manual's Operation: `Refine.rotrv_refines` (`Semantics/Refine/Shift.lean`).
- **Tests:** 1 in tests/oracle; 5 in-file `#guard`/`example` statements.

## Register jump (JALR; JR is an idiom)

### jalr

- **Manual:** MD00086 Vol II-A Rev 6.06, JALR (Jump and Link Register), p.196-197.
- **Constructor:** `jalr rs rd` (`Semantics/Instruction.lean`): `$rd = PC_next + 4` (the address of the instruction *after* the delay slot — same `pc + 8` link-value convention as `jal`); `PC = $rs`, after the usual one-instruction delay slot (opcode 0, funct 0x09; MD00086 Vol II-A Rev 6.06, JALR, p.196). `rd = 0` is `JR` (p.206). `rt` and hint bits 10..6 are 0.
- **Step arm:** `Semantics/Exec/Jump.lean`.
- **Proofs:** spec theorem `jalr_spec_raw` (`Semantics/Specs/Jump.lean`) and 3 more; refinement of the manual's Operation: `Refine.jalr_refines` (`Semantics/Refine/Jump.lean`).
- **Tests:** 2 in tests/corpus, 8 in tests/asm, 11 in tests/oracle; 15 in-file `#guard`/`example` statements.

### jalr.hb

- **Manual:** MD00086 Vol II-A Rev 6.06, JALR.HB (Jump and Link Register with Hazard Barrier), p.198-200.
- **Assembler form:** `jalr.hb`.
- **Constructor:** `jalrHb rs rd` (`Semantics/Instruction.lean`): `JALR.HB rd, rs`: `JALR` with hazard barrier (MD00086 Vol II-A Rev 6.06, JALR.HB, p.198-199): SPECIAL, `rs`, `0` (bits 20..16), `rd`, hint bit 10 = 1 and bits 9..6 = 0, funct `001001`. Links and jumps as `jalr`; `ClearHazards()` (no architectural state in this model: hazards are cleared immediately). `rd = 0` is `JR.HB` (p.208).
- **Step arm:** `Semantics/Exec/Jump.lean`.
- **Proofs:** spec theorem `jalrHb_spec_raw` (`Semantics/Specs/Jump.lean`) and 1 more; refinement of the manual's Operation: `Refine.jalrHb_refines` (`Semantics/Refine/Jump.lean`).
- **Tests:** 2 in tests/oracle; 9 in-file `#guard`/`example` statements.

## Bit count (CLO, CLZ)

### clo

- **Manual:** MD00086 Vol II-A Rev 6.06, CLO (Count Leading Ones in Word), p.134.
- **Constructor:** `clo rs rd` (`Semantics/Instruction.lean`): `$rd = ` the number of leading one bits in `$rs`, counted from the MSB (32 if `$rs` is all-ones) (SPECIAL, `rt` = 0, `sa` = 1, funct 0x11; CLO p.134).
- **Step arm:** `Semantics/Exec/BitOps.lean`.
- **Proofs:** spec theorem `clo_spec_raw` (`Semantics/Specs/BitOps.lean`); refinement of the manual's Operation: `Refine.clo_refines` (`Semantics/Refine/BitOps.lean`).
- **Tests:** 1 in tests/corpus, 2 in tests/oracle; 10 in-file `#guard`/`example` statements.

### clz

- **Manual:** MD00086 Vol II-A Rev 6.06, CLZ (Count Leading Zeros in Word), p.135.
- **Constructor:** `clz rs rd` (`Semantics/Instruction.lean`): `$rd = ` the number of leading zero bits in `$rs`, counted from the MSB (32 if `$rs` is all-zero) (SPECIAL, `rt` = 0, `sa` = 1, funct 0x10; CLZ p.135).
- **Step arm:** `Semantics/Exec/BitOps.lean`.
- **Proofs:** spec theorem `clz_spec_raw` (`Semantics/Specs/BitOps.lean`); refinement of the manual's Operation: `Refine.clz_refines` (`Semantics/Refine/BitOps.lean`).
- **Tests:** 1 in tests/corpus, 2 in tests/oracle; 9 in-file `#guard`/`example` statements.

## SPECIAL3 BSHFL: sign extension and byte swaps

### seb

- **Manual:** MD00086 Vol II-A Rev 6.06, SEB (Sign-Extend Byte), p.365.
- **Constructor:** `seb rd rt` (`Semantics/Instruction.lean`): `$rd = sign-extend($rt[7:0])` to 32 bits (SPECIAL3 opcode 0x1f, funct 0x20, sub-field 0x10).
- **Step arm:** `Semantics/Exec/BitOps.lean`.
- **Proofs:** spec theorem `seb_spec_raw` (`Semantics/Specs/BitOps.lean`); refinement of the manual's Operation: `Refine.seb_refines` (`Semantics/Refine/BitOps.lean`).
- **Tests:** 1 in tests/oracle; 5 in-file `#guard`/`example` statements.

### seh

- **Manual:** MD00086 Vol II-A Rev 6.06, SEH (Sign-Extend Halfword), p.366-367.
- **Constructor:** `seh rd rt` (`Semantics/Instruction.lean`): `$rd = sign-extend($rt[15:0])` to 32 bits (SPECIAL3 opcode 0x1f, funct 0x20, sub-field 0x18).
- **Step arm:** `Semantics/Exec/BitOps.lean`.
- **Proofs:** spec theorem `seh_spec_raw` (`Semantics/Specs/BitOps.lean`); refinement of the manual's Operation: `Refine.seh_refines` (`Semantics/Refine/BitOps.lean`).
- **Tests:** 1 in tests/oracle; 4 in-file `#guard`/`example` statements.

### wsbh

- **Manual:** MD00086 Vol II-A Rev 6.06, WSBH (Word Swap Bytes Within Halfwords), p.445.
- **Constructor:** `wsbh rd rt` (`Semantics/Instruction.lean`): "Word Swap Bytes Within Halfwords": swaps the byte order *within* each 16-bit half of `$rt` independently (byte 0 <-> 1, byte 2 <-> 3), leaving the two halfwords in their original word positions -- **not** a full 32-bit byte-reverse (that needs `wsbh` followed by `rotr` by 16) (SPECIAL3 opcode 0x1f, funct 0x20, sub-field 0x02 -- same BSHFL funct family as `seb`/`seh`, distinguished by the sub-field like they are).
- **Step arm:** `Semantics/Exec/BitOps.lean`.
- **Proofs:** spec theorem `wsbh_spec_raw` (`Semantics/Specs/BitOps.lean`); refinement of the manual's Operation: `Refine.wsbh_refines` (`Semantics/Refine/BitOps.lean`).
- **Tests:** 1 in tests/oracle; 4 in-file `#guard`/`example` statements.

## Bitfield extract and insert

### ext

- **Manual:** MD00086 Vol II-A Rev 6.06, EXT (Extract Bit Field), p.183-184.
- **Constructor:** `ext rt rs pos size` (`Semantics/Instruction.lean`): `$rt = zero-extend($rs[pos+size-1 .. pos])`, extracting a `size`-bit field starting at bit `pos` (SPECIAL3 opcode 0x1f, funct 0x00).
- **Step arm:** `Semantics/Exec/BitOps.lean`.
- **Proofs:** spec theorem `ext_spec_raw` (`Semantics/Specs/BitOps.lean`) and 1 more; refinement of the manual's Operation: `Refine.ext_refines` (`Semantics/Refine/BitOps.lean`).
- **Tests:** 1 in tests/oracle; 8 in-file `#guard`/`example` statements.

### ins

- **Manual:** MD00086 Vol II-A Rev 6.06, INS (Insert Bit Field), p.192-193.
- **Constructor:** `ins rt rs pos size` (`Semantics/Instruction.lean`): Inserts the low `size` bits of `$rs` into `$rt` starting at bit `pos`; bits of `$rt` outside `[pos+size-1 .. pos]` are left unchanged (SPECIAL3 opcode 0x1f, funct 0x04).
- **Step arm:** `Semantics/Exec/BitOps.lean`.
- **Proofs:** spec theorem `ins_spec_raw` (`Semantics/Specs/BitOps.lean`) and 2 more; refinement of the manual's Operation: `Refine.ins_refines` (`Semantics/Refine/BitOps.lean`).
- **Tests:** 1 in tests/oracle; 6 in-file `#guard`/`example` statements.

## RDHWR and the hardware registers

### rdhwr

- **Manual:** MD00086 Vol II-A Rev 6.06, RDHWR (Read Hardware Register), p.332-334.
- **Constructor:** `rdhwr rt rd sel` (`Semantics/Instruction.lean`): Read Hardware Register: `$rt = HWR[rd, sel]` (SPECIAL3 opcode 0x1f, funct 0x3b, `rs` = 0, bits 10..9 = 0, `sel` = bits 8..6; MD00086 Vol II-A Rev 6.06, RDHWR, p.332-334: "In Release 6, a sel field has been added"). The model implements `rd` = 0 `CPUNum`, 1 `SYNCI_Step`, 2 `CC` (= `Count`), 3 `CCRes`, each with `sel = 0`; access needs Coprocessor 0 to be enabled or the `HWREna` bit `rd` set, otherwise (and for every other `rd`/`sel`) Reserved Instruction (`Step.lean`).
- **Step arm:** `Semantics/Exec/System.lean`.
- **Proofs:** spec theorem `rdhwr_spec_raw` (`Semantics/Specs/Timer.lean`) and 5 more; refinement of the manual's Operation: `Refine.rdhwr_refines` (`Semantics/Refine/System.lean`).
- **Tests:** 6 in tests/oracle; 25 in-file `#guard`/`example` statements.

### addiu

- **Manual:** MD00086 Vol II-A Rev 6.06, ADDIU (Add Immediate Unsigned Word), p.36.
- **Constructor:** `addiu rs rt imm` (`Semantics/Instruction.lean`): `$rt = $rs + sext16(imm)`, wraps (opcode 0x09).
- **Step arm:** `Semantics/Exec/Immediate.lean`.
- **Proofs:** spec theorem `addiu_spec_raw` (`Semantics/Specs/Immediate.lean`); refinement of the manual's Operation: `Refine.addiu_refines` (`Semantics/Refine/Immediate.lean`).
- **Tests:** 7 in tests/corpus, 3 in tests/equiv, 2 in tests/asm, 64 in tests/oracle; 14 in-file `#guard`/`example` statements.

### slti

- **Manual:** MD00086 Vol II-A Rev 6.06, SLTI (Set on Less Than Immediate), p.379.
- **Constructor:** `slti rs rt imm` (`Semantics/Instruction.lean`): `$rt = ($rs < sext16(imm)) ? 1 : 0`, signed (opcode 0x0a).
- **Step arm:** `Semantics/Exec/Immediate.lean`.
- **Proofs:** spec theorem `slti_spec_raw` (`Semantics/Specs/Immediate.lean`); refinement of the manual's Operation: `Refine.slti_refines` (`Semantics/Refine/Immediate.lean`).
- **Tests:** 1 in tests/corpus, 2 in tests/oracle; 3 in-file `#guard`/`example` statements.

### sltiu

- **Manual:** MD00086 Vol II-A Rev 6.06, SLTIU (Set on Less Than Immediate Unsigned), p.380.
- **Constructor:** `sltiu rs rt imm` (`Semantics/Instruction.lean`): `$rt = ($rs <u sext16(imm)) ? 1 : 0` (opcode 0x0b).
- **Step arm:** `Semantics/Exec/Immediate.lean`.
- **Proofs:** spec theorem `sltiu_spec_raw` (`Semantics/Specs/Immediate.lean`); refinement of the manual's Operation: `Refine.sltiu_refines` (`Semantics/Refine/Immediate.lean`).
- **Tests:** 1 in tests/corpus, 3 in tests/oracle; 3 in-file `#guard`/`example` statements.

### andi

- **Manual:** MD00086 Vol II-A Rev 6.06, ANDI (and immediate), p.45-46.
- **Constructor:** `andi rs rt imm` (`Semantics/Instruction.lean`): `$rt = $rs & zext16(imm)` (opcode 0x0c).
- **Step arm:** `Semantics/Exec/Immediate.lean`.
- **Proofs:** spec theorem `andi_spec_raw` (`Semantics/Specs/Immediate.lean`); refinement of the manual's Operation: `Refine.andi_refines` (`Semantics/Refine/Immediate.lean`).
- **Tests:** 8 in tests/corpus, 1 in tests/equiv, 4 in tests/asm, 32 in tests/oracle; 3 in-file `#guard`/`example` statements.

### ori

- **Manual:** MD00086 Vol II-A Rev 6.06, ORI (Or Immediate), p.315-316.
- **Constructor:** `ori rs rt imm` (`Semantics/Instruction.lean`): `$rt = $rs | zext16(imm)` (opcode 0x0d).
- **Step arm:** `Semantics/Exec/Immediate.lean`.
- **Proofs:** spec theorem `ori_spec_raw` (`Semantics/Specs/Immediate.lean`); refinement of the manual's Operation: `Refine.ori_refines` (`Semantics/Refine/Immediate.lean`).
- **Tests:** 1 in tests/corpus, 2 in tests/asm, 33 in tests/oracle; 4 in-file `#guard`/`example` statements.

### xori

- **Manual:** MD00086 Vol II-A Rev 6.06, XORI (Exclusive OR Immediate), p.447.
- **Constructor:** `xori rs rt imm` (`Semantics/Instruction.lean`): `$rt = $rs ^ zext16(imm)` (opcode 0x0e).
- **Step arm:** `Semantics/Exec/Immediate.lean`.
- **Proofs:** spec theorem `xori_spec_raw` (`Semantics/Specs/Immediate.lean`); refinement of the manual's Operation: `Refine.xori_refines` (`Semantics/Refine/Immediate.lean`).
- **Tests:** 2 in tests/corpus, 4 in tests/oracle; 3 in-file `#guard`/`example` statements.

### aui

- **Manual:** MD00086 Vol II-A Rev 6.06, AUI (Add Immediate to Upper Bits), p.47.
- **Constructor:** `aui rs rt imm` (`Semantics/Instruction.lean`): `AUI rt, rs, immediate`: `$rt = $rs + (imm << 16)` (opcode 0x0f; MD00086 Vol II-A Rev 6.06, AUI, p.47: "GPR[rt] ← GPR[rs] + sign_extend(immediate << 16)"). "In Release 6, LUI is an assembly idiom for AUI with rs=0" (p.47; LUI p.233): `lui rt, imm` is `aui rt, $0, imm`.
- **Step arm:** `Semantics/Exec/Immediate.lean`.
- **Proofs:** spec theorem `aui_spec_raw` (`Semantics/Specs/Immediate.lean`) and 1 more; refinement of the manual's Operation: `Refine.aui_refines` (`Semantics/Refine/Immediate.lean`).
- **Tests:** 2 in tests/corpus, 3 in tests/asm, 38 in tests/oracle; 15 in-file `#guard`/`example` statements.

## Release 6 integer instructions (multiply/divide, PC-relative, ALIGN, BITSWAP, SELEQZ/SELNEZ, LSA, ...)

### mul

- **Manual:** MD00086 Vol II-A Rev 6.06, MUL (Multiply Word to GPR), p.299.
- **Constructor:** `mul rs rt rd` (`Semantics/Instruction.lean`): `MUL rd, rs, rt`: `$rd = ` the low word of the signed 64-bit product (SPECIAL, `sa` = 00010, funct `011000` SOP30; MUL MUH MULU MUHU, p.300-301).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `mul_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.mul_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 2 in tests/equiv, 1 in tests/oracle; 3 in-file `#guard`/`example` statements.

### muh

- **Manual:** MD00086 Vol II-A Rev 6.06, MUL MUH MULU MUHU (Multiply Integers (with result to GPR)), p.300-301.
- **Constructor:** `muh rs rt rd` (`Semantics/Instruction.lean`): `MUH rd, rs, rt`: `$rd = ` the high word of the signed product (`sa` = 00011, SOP30; p.300).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `muh_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.muh_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

### mulu

- **Manual:** MD00086 Vol II-A Rev 6.06, MUL MUH MULU MUHU (Multiply Integers (with result to GPR)), p.300-301.
- **Constructor:** `mulu rs rt rd` (`Semantics/Instruction.lean`): `MULU rd, rs, rt`: the low word of the unsigned product (`sa` = 00010, SOP31 `011001`; p.300).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `mulu_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.mulu_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

### muhu

- **Manual:** MD00086 Vol II-A Rev 6.06, MUL MUH MULU MUHU (Multiply Integers (with result to GPR)), p.300-301.
- **Constructor:** `muhu rs rt rd` (`Semantics/Instruction.lean`): `MUHU rd, rs, rt`: the high word of the unsigned product (`sa` = 00011, SOP31; p.300).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `muhu_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.muhu_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

### div

- **Manual:** MD00086 Vol II-A Rev 6.06, DIV (Divide Word), p.165-167.
- **Constructor:** `div rs rt rd` (`Semantics/Instruction.lean`): `DIV rd, rs, rt`: the signed quotient, truncated toward zero (SPECIAL, `sa` = 00010, funct `011010` SOP32; DIV MOD DIVU MODU, p.168-169). A zero divisor gives an UNPREDICTABLE result (p.168), the oracle choice `Manual.Oracle.divByZero`.
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `div_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.div_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/equiv, 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

### mod

- **Manual:** MD00086 Vol II-A Rev 6.06, DIV MOD DIVU MODU (Divide Integers (with result to GPR)), p.168-169.
- **Constructor:** `mod rs rt rd` (`Semantics/Instruction.lean`): `MOD rd, rs, rt`: the signed remainder, with the sign of the dividend (`sa` = 00011, SOP32; p.168).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `mod_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.mod_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/equiv, 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

### divu

- **Manual:** MD00086 Vol II-A Rev 6.06, DIVU (Divide Unsigned Word), p.171.
- **Constructor:** `divu rs rt rd` (`Semantics/Instruction.lean`): `DIVU rd, rs, rt`: the unsigned quotient (`sa` = 00010, SOP33 `011011`; p.168).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `divu_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.divu_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

### modu

- **Manual:** MD00086 Vol II-A Rev 6.06, DIV MOD DIVU MODU (Divide Integers (with result to GPR)), p.168-169.
- **Constructor:** `modu rs rt rd` (`Semantics/Instruction.lean`): `MODU rd, rs, rt`: the unsigned remainder (`sa` = 00011, SOP33; p.168).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `modu_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.modu_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

### seleqz

- **Manual:** MD00086 Vol II-A Rev 6.06, SELEQZ SELNEZ (Select integer GPR value or zero), p.369-370.
- **Constructor:** `seleqz rs rt rd` (`Semantics/Instruction.lean`): `SELEQZ rd, rs, rt`: `$rd = ($rt = 0) ? $rs : 0` (SPECIAL, `sa` = 0, funct `110101`; SELEQZ SELNEZ, p.369).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `seleqz_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.seleqz_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/oracle; 2 in-file `#guard`/`example` statements.

### selnez

- **Manual:** MD00086 Vol II-A Rev 6.06, SELEQZ SELNEZ (Select integer GPR value or zero), p.369-370.
- **Constructor:** `selnez rs rt rd` (`Semantics/Instruction.lean`): `SELNEZ rd, rs, rt`: `$rd = ($rt ≠ 0) ? $rs : 0` (funct `110111`; p.369).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `selnez_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.selnez_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

### lsa

- **Manual:** MD00086 Vol II-A Rev 6.06, LSA (Load Scaled Address), p.232.
- **Constructor:** `lsa rs rt rd sa` (`Semantics/Instruction.lean`): `LSA rd, rs, rt, sa+1`: `$rd = ($rs << (sa+1)) + $rt` (SPECIAL, bits 10..8 = 000, the 2-bit `sa` in bits 7..6, funct `000101`; LSA, p.232). `sa` is the raw 2-bit field (shift 1..4).
- **Step arm:** `Semantics/Exec/IntArith.lean`.
- **Proofs:** spec theorem `lsa_spec_raw` (`Semantics/Specs/Arith.lean`); refinement of the manual's Operation: `Refine.lsa_refines` (`Semantics/Refine/IntArith.lean`).
- **Tests:** 1 in tests/oracle; 3 in-file `#guard`/`example` statements.

### align

- **Manual:** MD00086 Vol II-A Rev 6.06, ALIGN (Concatenate two GPRs, and extract a contiguous subset at a byte position), p.39-41.
- **Constructor:** `align rs rt rd bp` (`Semantics/Instruction.lean`): `ALIGN rd, rs, rt, bp`: `$rd = ($rt << 8·bp) | ($rs >> 8·(4-bp))` (SPECIAL3, bits 10..8 = ALIGN `010`, the 2-bit `bp` in bits 7..6, BSHFL `100000`; ALIGN, p.39, an image page).
- **Step arm:** `Semantics/Exec/BitOps.lean`.
- **Proofs:** spec theorem `align_spec_raw` (`Semantics/Specs/BitOps.lean`); refinement of the manual's Operation: `Refine.align_refines` (`Semantics/Refine/BitOps.lean`).
- **Tests:** 1 in tests/oracle; 3 in-file `#guard`/`example` statements.

### bitswap

- **Manual:** MD00086 Vol II-A Rev 6.06, BITSWAP (Swaps (reverses) bits in each byte), p.92-93.
- **Constructor:** `bitswap rd rt` (`Semantics/Instruction.lean`): `BITSWAP rd, rt`: the bits of each byte of `$rt` reversed (SPECIAL3, `rs` = 0, `sa` = BITSWAP `00000`, BSHFL; BITSWAP, p.92).
- **Step arm:** `Semantics/Exec/BitOps.lean`.
- **Proofs:** spec theorem `bitswap_spec_raw` (`Semantics/Specs/BitOps.lean`); refinement of the manual's Operation: `Refine.bitswap_refines` (`Semantics/Refine/BitOps.lean`).
- **Tests:** 1 in tests/oracle; 2 in-file `#guard`/`example` statements.

### addiupc

- **Manual:** MD00086 Vol II-A Rev 6.06, ADDIUPC (Add Immediate to PC (unsigned - non-trapping)), p.37.
- **Constructor:** `addiupc rs imm` (`Semantics/Instruction.lean`): `ADDIUPC rs, imm`: `$rs = PC + sign_extend(imm << 2)`, `PC` the address of the ADDIUPC instruction (PCREL `111011`, bits 20..19 = 00, a 19-bit `imm` in bits 18..0; ADDIUPC, p.37).
- **Step arm:** `Semantics/Exec/Immediate.lean`.
- **Proofs:** spec theorem `addiupc_spec_raw` (`Semantics/Specs/PcRel.lean`); refinement of the manual's Operation: `Refine.addiupc_refines` (`Semantics/Refine/PcRel.lean`).
- **Tests:** 1 in tests/oracle; 4 in-file `#guard`/`example` statements.

### lwpc

- **Manual:** MD00086 Vol II-A Rev 6.06, LWPC (Load Word PC-relative), p.246-247.
- **Constructor:** `lwpc rs off` (`Semantics/Instruction.lean`): `LWPC rs, offset`: `$rs = MEM32[PC + sign_extend(offset << 2)]` (PCREL, bits 20..19 = 01, a 19-bit `offset`; LWPC, p.246).
- **Step arm:** `Semantics/Exec/Immediate.lean`.
- **Proofs:** spec theorem `lwpc_spec_raw` (`Semantics/Specs/PcRel.lean`); refinement of the manual's Operation: `Refine.lwpc_refines` (`Semantics/Refine/PcRel.lean`).
- **Tests:** 1 in tests/oracle; 2 in-file `#guard`/`example` statements.

### auipc

- **Manual:** MD00086 Vol II-A Rev 6.06, AUIPC (Add Upper Immediate to PC), p.48.
- **Constructor:** `auipc rs imm` (`Semantics/Instruction.lean`): `AUIPC rs, imm`: `$rs = PC + (imm << 16)` (PCREL, bits 20..16 = 11110; AUIPC, p.48).
- **Step arm:** `Semantics/Exec/Immediate.lean`.
- **Proofs:** spec theorem `auipc_spec_raw` (`Semantics/Specs/PcRel.lean`); refinement of the manual's Operation: `Refine.auipc_refines` (`Semantics/Refine/PcRel.lean`).
- **Tests:** 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

### aluipc

- **Manual:** MD00086 Vol II-A Rev 6.06, ALUIPC (Aligned Add Upper Immediate to PC), p.43.
- **Constructor:** `aluipc rs imm` (`Semantics/Instruction.lean`): `ALUIPC rs, imm`: `$rs = ~0x0FFFF & (PC + sign_extend(imm << 16))` (PCREL, bits 20..16 = 11111; ALUIPC, p.43).
- **Step arm:** `Semantics/Exec/Immediate.lean`.
- **Proofs:** spec theorem `aluipc_spec_raw` (`Semantics/Specs/PcRel.lean`); refinement of the manual's Operation: `Refine.aluipc_refines` (`Semantics/Refine/PcRel.lean`).
- **Tests:** 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

## Loads and stores

### lw

- **Manual:** MD00086 Vol II-A Rev 6.06, LW (Load Word), p.235.
- **Constructor:** `lw rs rt imm` (`Semantics/Instruction.lean`): `$rt = MEM32[$rs + offset]`, word-aligned (opcode 0x23).
- **Step arm:** `Semantics/Exec/Memory.lean`.
- **Proofs:** spec theorem `lw_spec_raw` (`Semantics/Specs/Memory.lean`) and 3 more; refinement of the manual's Operation: `Refine.lw_refines` (`Semantics/Refine/Memory.lean`).
- **Tests:** 5 in tests/corpus, 4 in tests/asm, 15 in tests/oracle; 13 in-file `#guard`/`example` statements.

### sw

- **Manual:** MD00086 Vol II-A Rev 6.06, SW (Store Word), p.392.
- **Constructor:** `sw rs rt imm` (`Semantics/Instruction.lean`): `MEM32[$rs + offset] = $rt`, word-aligned (opcode 0x2b).
- **Step arm:** `Semantics/Exec/Memory.lean`.
- **Proofs:** spec theorem `sw_spec_raw` (`Semantics/Specs/Memory.lean`) and 3 more; refinement of the manual's Operation: `Refine.sw_refines` (`Semantics/Refine/Memory.lean`).
- **Tests:** 1 in tests/corpus, 57 in tests/oracle; 16 in-file `#guard`/`example` statements.

### lb

- **Manual:** MD00086 Vol II-A Rev 6.06, LB (Load Byte), p.211.
- **Constructor:** `lb rs rt imm` (`Semantics/Instruction.lean`): `$rt = sext8(MEM8[$rs + offset])` (opcode 0x20).
- **Step arm:** `Semantics/Exec/Memory.lean`.
- **Proofs:** spec theorem `lb_spec_raw` (`Semantics/Specs/Memory.lean`); refinement of the manual's Operation: `Refine.lb_refines` (`Semantics/Refine/Memory.lean`).
- **Tests:** 1 in tests/corpus, 2 in tests/oracle; 7 in-file `#guard`/`example` statements.

### lbu

- **Manual:** MD00086 Vol II-A Rev 6.06, LBU (Load Byte Unsigned), p.213.
- **Constructor:** `lbu rs rt imm` (`Semantics/Instruction.lean`): `$rt = zext8(MEM8[$rs + offset])` (opcode 0x24).
- **Step arm:** `Semantics/Exec/Memory.lean`.
- **Proofs:** spec theorem `lbu_spec_raw` (`Semantics/Specs/Memory.lean`); refinement of the manual's Operation: `Refine.lbu_refines` (`Semantics/Refine/Memory.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 2 in tests/oracle; 6 in-file `#guard`/`example` statements.

### lh

- **Manual:** MD00086 Vol II-A Rev 6.06, LH (Load Halfword), p.219.
- **Constructor:** `lh rs rt imm` (`Semantics/Instruction.lean`): `$rt = sext16(MEM16[$rs + offset])`, halfword-aligned (opcode 0x21).
- **Step arm:** `Semantics/Exec/Memory.lean`.
- **Proofs:** spec theorem `lh_spec_raw` (`Semantics/Specs/Memory.lean`); refinement of the manual's Operation: `Refine.lh_refines` (`Semantics/Refine/Memory.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 4 in tests/oracle; 6 in-file `#guard`/`example` statements.

### lhu

- **Manual:** MD00086 Vol II-A Rev 6.06, LHU (Load Halfword Unsigned), p.221.
- **Constructor:** `lhu rs rt imm` (`Semantics/Instruction.lean`): `$rt = zext16(MEM16[$rs + offset])`, halfword-aligned (opcode 0x25).
- **Step arm:** `Semantics/Exec/Memory.lean`.
- **Proofs:** spec theorem `lhu_spec_raw` (`Semantics/Specs/Memory.lean`); refinement of the manual's Operation: `Refine.lhu_refines` (`Semantics/Refine/Memory.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/oracle; 5 in-file `#guard`/`example` statements.

### sh

- **Manual:** MD00086 Vol II-A Rev 6.06, SH (Store Halfword), p.373.
- **Constructor:** `sh rs rt imm` (`Semantics/Instruction.lean`): `MEM16[$rs + offset] = $rt[15:0]`, halfword-aligned (opcode 0x29).
- **Step arm:** `Semantics/Exec/Memory.lean`.
- **Proofs:** spec theorem `sh_spec_raw` (`Semantics/Specs/Memory.lean`); refinement of the manual's Operation: `Refine.sh_refines` (`Semantics/Refine/Memory.lean`).
- **Tests:** 1 in tests/corpus, 4 in tests/oracle; 6 in-file `#guard`/`example` statements.

### sb

- **Manual:** MD00086 Vol II-A Rev 6.06, SB (Store Byte), p.344-345.
- **Constructor:** `sb rs rt imm` (`Semantics/Instruction.lean`): `MEM8[$rs + offset] = $rt[7:0]`, no alignment requirement (opcode 0x28; MD00086 Rev 2.50 "SB").
- **Step arm:** `Semantics/Exec/Memory.lean`.
- **Proofs:** spec theorem `sb_spec_raw` (`Semantics/Specs/Memory.lean`) and 1 more; refinement of the manual's Operation: `Refine.sb_refines` (`Semantics/Refine/Memory.lean`).
- **Tests:** 1 in tests/asm, 3 in tests/oracle; 11 in-file `#guard`/`example` statements.

### ll

- **Manual:** MD00086 Vol II-A Rev 6.06, LL (Load Linked Word), p.223-224.
- **Constructor:** `ll rs rt imm` (`Semantics/Instruction.lean`): `$rt = MEM32[$rs + offset]`, word-aligned, and sets `State.llBit` (MD00086 Vol II-A Rev 6.06, LL, p.223). Release 6 encoding: SPECIAL3, `base` = bits 25..21, `rt`, a **9-bit** signed `offset` in bits 15..7, bit 6 = 0, funct `110110`; `imm` here is that raw 9-bit field. The pre-Release 6 opcode 0x30 is removed. A misaligned address is always an Address Error.
- **Step arm:** `Semantics/Exec/Atomic.lean`.
- **Proofs:** spec theorem `ll_spec_raw` (`Semantics/Specs/Atomic.lean`); refinement of the manual's Operation: `Refine.ll_refines` (`Semantics/Refine/Atomic.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 10 in tests/oracle; 14 in-file `#guard`/`example` statements.

### sc

- **Manual:** MD00086 Vol II-A Rev 6.06, SC (Store Conditional Word), p.347-350.
- **Constructor:** `sc rs rt imm` (`Semantics/Instruction.lean`): Conditionally `MEM32[$rs + offset] = $rt`, word-aligned, based on `State.llBit`: if set, performs the store and writes `1` to `$rt`; otherwise the store does not happen and `0` is written to `$rt`. Either way, clears `llBit` (MD00086 Vol II-A Rev 6.06, SC, p.347). Release 6 encoding: SPECIAL3, 9-bit signed `offset` in bits 15..7 (`imm` is that raw field), bit 6 = 0, funct `100110`; the pre-Release 6 opcode 0x38 is removed.
- **Step arm:** `Semantics/Exec/Atomic.lean`.
- **Proofs:** spec theorem `sc_spec_raw` (`Semantics/Specs/Atomic.lean`); refinement of the manual's Operation: `Refine.sc_refines` (`Semantics/Refine/Atomic.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 8 in tests/oracle; 8 in-file `#guard`/`example` statements.

## Branches with a delay slot, two registers

### beq

- **Manual:** MD00086 Vol II-A Rev 6.06, BEQ (Branch on Equal), p.72.
- **Constructor:** `beq rs rt imm` (`Semantics/Instruction.lean`): `if $rs == $rt then PC = PC_next + (sext16(imm) << 2)` (opcode 0x04).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `beq_spec_raw` (`Semantics/Specs/Branch.lean`) and 3 more; refinement of the manual's Operation: `Refine.beq_refines` (`Semantics/Refine/Branch.lean`).
- **Tests:** 2 in tests/corpus, 2 in tests/equiv, 1 in tests/asm, 20 in tests/oracle; 21 in-file `#guard`/`example` statements.

### bne

- **Manual:** MD00086 Vol II-A Rev 6.06, BNE (Branch on Not Equal), p.103.
- **Constructor:** `bne rs rt imm` (`Semantics/Instruction.lean`): `if $rs != $rt then PC = PC_next + (sext16(imm) << 2)` (opcode 0x05).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bne_spec_raw` (`Semantics/Specs/Branch.lean`) and 2 more; refinement of the manual's Operation: `Refine.bne_refines` (`Semantics/Refine/Branch.lean`).
- **Tests:** 3 in tests/corpus, 6 in tests/oracle; 10 in-file `#guard`/`example` statements.

## Branches with a delay slot, one register

### blez

- **Manual:** MD00086 Vol II-A Rev 6.06, BLEZ (Branch on Less Than or Equal to Zero), p.94.
- **Constructor:** `blez rs imm` (`Semantics/Instruction.lean`): `if $rs <= 0 then PC = PC_next + (sext16(imm) << 2)` (opcode 0x06).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `blez_spec_raw` (`Semantics/Specs/Branch.lean`) and 2 more; refinement of the manual's Operation: `Refine.blez_refines` (`Semantics/Refine/Branch.lean`).
- **Tests:** 2 in tests/corpus, 2 in tests/oracle; 6 in-file `#guard`/`example` statements.

### bgtz

- **Manual:** MD00086 Vol II-A Rev 6.06, BGTZ (Branch on Greater Than Zero), p.88.
- **Constructor:** `bgtz rs imm` (`Semantics/Instruction.lean`): `if $rs > 0 then PC = PC_next + (sext16(imm) << 2)` (opcode 0x07).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bgtz_spec_raw` (`Semantics/Specs/Branch.lean`) and 2 more; refinement of the manual's Operation: `Refine.bgtz_refines` (`Semantics/Refine/Branch.lean`).
- **Tests:** 2 in tests/corpus, 2 in tests/oracle; 4 in-file `#guard`/`example` statements.

## REGIMM branches with a delay slot

### bltz

- **Manual:** MD00086 Vol II-A Rev 6.06, BLTZ (Branch on Less Than Zero), p.97.
- **Constructor:** `bltz rs imm` (`Semantics/Instruction.lean`): `if $rs < 0 then PC = PC_next + (sext16(imm) << 2)`, signed (opcode 0x01, `rt` field = 0x00 `BLTZ`).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bltz_spec_raw` (`Semantics/Specs/Branch.lean`) and 2 more; refinement of the manual's Operation: `Refine.bltz_refines` (`Semantics/Refine/Branch.lean`).
- **Tests:** 1 in tests/corpus, 11 in tests/oracle; 6 in-file `#guard`/`example` statements.

### bgez

- **Manual:** MD00086 Vol II-A Rev 6.06, BGEZ (Branch on Greater Than or Equal to Zero), p.75.
- **Constructor:** `bgez rs imm` (`Semantics/Instruction.lean`): `if $rs >= 0 then PC = PC_next + (sext16(imm) << 2)`, signed (opcode 0x01, `rt` field = 0x01 `BGEZ`).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bgez_spec_raw` (`Semantics/Specs/Branch.lean`) and 2 more; refinement of the manual's Operation: `Refine.bgez_refines` (`Semantics/Refine/Branch.lean`).
- **Tests:** 1 in tests/corpus, 2 in tests/oracle; 7 in-file `#guard`/`example` statements.

### nal

- **Manual:** MD00086 Vol II-A Rev 6.06, NAL (No-op and Link), p.306.
- **Constructor:** `nal imm` (`Semantics/Instruction.lean`): `NAL`: `$ra = PC + 8`, a not-taken branch with a delay slot (REGIMM, `rs` = 0, `rt` field = 0x10; MD00086 Vol II-A Rev 6.06, NAL, p.306: "NAL is considered to be a not-taken branch, with a delay slot"; `imm` = the ignored 16-bit offset field). Release 6 keeps only this `rs = 0` case of the pre-Release 6 BLTZAL ("The pre-Release 6 instruction BLTZAL when rs is not GPR[0], is removed in Release 6, and is required to signal a Reserved Instruction exception", p.306).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `nal_spec_raw` (`Semantics/Specs/Branch.lean`) and 1 more; refinement of the manual's Operation: `Refine.nal_refines` (`Semantics/Refine/Branch.lean`).
- **Tests:** 3 in tests/oracle; 11 in-file `#guard`/`example` statements.

### bal

- **Manual:** MD00086 Vol II-A Rev 6.06, BAL (Branch and Link), p.50-51.
- **Constructor:** `bal imm` (`Semantics/Instruction.lean`): `BAL`: `$ra = PC + 8`, then branch to `PC_next + (sext16(imm) << 2)` after the delay slot (REGIMM, `rs` = 0, `rt` field = 0x11; MD00086 Vol II-A Rev 6.06, BAL, p.50). "Release 6 keeps the BAL special case of BGEZAL, but removes all other instances of BGEZAL. BGEZAL with rs any register other than GPR[0] is required to signal a Reserved Instruction exception" (p.50).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bal_spec_raw` (`Semantics/Specs/Branch.lean`) and 1 more; refinement of the manual's Operation: `Refine.bal_refines` (`Semantics/Refine/Branch.lean`).
- **Tests:** 2 in tests/oracle; 11 in-file `#guard`/`example` statements.

## SYNCI

### synci

- **Manual:** MD00086 Vol II-A Rev 6.06, SYNCI (Synchronize Caches to Make Instruction Writes Effective), p.412-414.
- **Constructor:** `synci rs imm` (`Semantics/Instruction.lean`): Hint to flush the instruction cache at `$rs + sext16(offset)`, for self-modifying code / JIT compilers (opcode 0x01 REGIMM, `rt` field = `0x1f` `SYNCI`). This simulator has no instruction-cache model, so `Step.lean` computes the address (exactly like `lw`/`sw`) but never uses it for anything -- a documented no-op, not a silently-dropped cache effect.
- **Step arm:** `Semantics/Exec/Memory.lean`.
- **Proofs:** spec theorem `synci_spec_raw` (`Semantics/Specs/Memory.lean`); refinement of the manual's Operation: `Refine.synci_refines` (`Semantics/Refine/Memory.lean`).
- **Tests:** 2 in tests/oracle; 5 in-file `#guard`/`example` statements.

## Jumps (J, JAL)

### j

- **Manual:** MD00086 Vol II-A Rev 6.06, J (Jump), p.194.
- **Constructor:** `j target` (`Semantics/Instruction.lean`): `PC = (PC_next & 0xF0000000) | (target << 2)` (opcode 0x02).
- **Step arm:** `Semantics/Exec/Jump.lean`.
- **Proofs:** spec theorem `j_spec_raw` (`Semantics/Specs/Jump.lean`); refinement of the manual's Operation: `Refine.j_refines` (`Semantics/Refine/Jump.lean`).
- **Tests:** 1 in tests/corpus, 2 in tests/equiv, 3 in tests/oracle; 11 in-file `#guard`/`example` statements.

### jal

- **Manual:** MD00086 Vol II-A Rev 6.06, JAL (Jump and Link), p.195.
- **Constructor:** `jal target` (`Semantics/Instruction.lean`): `$ra = PC_next; PC = (PC_next & 0xF0000000) | (target << 2)` (opcode 0x03).
- **Step arm:** `Semantics/Exec/Jump.lean`.
- **Proofs:** spec theorem `jal_spec_raw` (`Semantics/Specs/Jump.lean`) and 1 more; refinement of the manual's Operation: `Refine.jal_refines` (`Semantics/Refine/Jump.lean`).
- **Tests:** 2 in tests/corpus, 8 in tests/asm, 4 in tests/oracle; 5 in-file `#guard`/`example` statements.

## SYSCALL

### syscall

- **Manual:** MD00086 Vol II-A Rev 6.06, SYSCALL (System Call), p.415.
- **Constructor:** `syscall code` (`Semantics/Instruction.lean`): System call (opcode 0, funct 0x0c); `code` = bits 25..6, ignored by execution. The environment-call number is `$v0` (services 1/4/10/11).
- **Step arm:** `Semantics/Exec/Syscall.lean`.
- **Proofs:** spec theorem `syscall_spec_raw` (`Semantics/Specs/Syscall.lean`) and 3 more; refinement of the manual's Operation: `Refine.syscall_refines` (`Semantics/Refine/Syscall.lean`).
- **Tests:** 29 in tests/corpus, 12 in tests/equiv, 13 in tests/asm, 93 in tests/oracle; 19 in-file `#guard`/`example` statements.

## Conditional traps

### teq

- **Manual:** MD00086 Vol II-A Rev 6.06, TEQ (Trap if Equal), p.416.
- **Constructor:** `teq rs rt code` (`Semantics/Instruction.lean`): `if $rs == $rt then trap` (opcode 0, funct 0x34). `code` = bits 15..6, ignored by execution.
- **Step arm:** `Semantics/Exec/Trap.lean`.
- **Proofs:** spec theorem `teq_spec_raw` (`Semantics/Specs/Trap.lean`); refinement of the manual's Operation: `Refine.teq_refines` (`Semantics/Refine/Trap.lean`).
- **Tests:** 2 in tests/corpus, 1 in tests/asm, 8 in tests/oracle; 10 in-file `#guard`/`example` statements.

### tne

- **Manual:** MD00086 Vol II-A Rev 6.06, TNE (Trap if Not Equal), p.438.
- **Constructor:** `tne rs rt code` (`Semantics/Instruction.lean`): `if $rs != $rt then trap` (opcode 0, funct 0x36). `code` = bits 15..6, ignored by execution.
- **Step arm:** `Semantics/Exec/Trap.lean`.
- **Proofs:** spec theorem `tne_spec_raw` (`Semantics/Specs/Trap.lean`); refinement of the manual's Operation: `Refine.tne_refines` (`Semantics/Refine/Trap.lean`).
- **Tests:** 2 in tests/corpus, 2 in tests/oracle; 4 in-file `#guard`/`example` statements.

### tlt

- **Manual:** MD00086 Vol II-A Rev 6.06, TLT (Trap if Less Than), p.434.
- **Constructor:** `tlt rs rt code` (`Semantics/Instruction.lean`): `if $rs < $rt then trap`, signed (opcode 0, funct 0x32). `code` = bits 15..6, ignored by execution.
- **Step arm:** `Semantics/Exec/Trap.lean`.
- **Proofs:** spec theorem `tlt_spec_raw` (`Semantics/Specs/Trap.lean`); refinement of the manual's Operation: `Refine.tlt_refines` (`Semantics/Refine/Trap.lean`).
- **Tests:** 2 in tests/corpus, 2 in tests/oracle; 4 in-file `#guard`/`example` statements.

### tge

- **Manual:** MD00086 Vol II-A Rev 6.06, TGE (Trap if Greater or Equal), p.418.
- **Constructor:** `tge rs rt code` (`Semantics/Instruction.lean`): `if $rs >= $rt then trap`, signed (opcode 0, funct 0x30). `code` = bits 15..6, ignored by execution.
- **Step arm:** `Semantics/Exec/Trap.lean`.
- **Proofs:** spec theorem `tge_spec_raw` (`Semantics/Specs/Trap.lean`); refinement of the manual's Operation: `Refine.tge_refines` (`Semantics/Refine/Trap.lean`).
- **Tests:** 2 in tests/corpus, 2 in tests/oracle; 4 in-file `#guard`/`example` statements.

### tltu

- **Manual:** MD00086 Vol II-A Rev 6.06, TLTU (Trap if Less Than Unsigned), p.437.
- **Constructor:** `tltu rs rt code` (`Semantics/Instruction.lean`): `if $rs <u $rt then trap`, unsigned (opcode 0, funct 0x33). `code` = bits 15..6, ignored by execution.
- **Step arm:** `Semantics/Exec/Trap.lean`.
- **Proofs:** spec theorem `tltu_spec_raw` (`Semantics/Specs/Trap.lean`); refinement of the manual's Operation: `Refine.tltu_refines` (`Semantics/Refine/Trap.lean`).
- **Tests:** 2 in tests/corpus, 2 in tests/oracle; 3 in-file `#guard`/`example` statements.

### tgeu

- **Manual:** MD00086 Vol II-A Rev 6.06, TGEU (Trap if Greater or Equal Unsigned), p.421.
- **Constructor:** `tgeu rs rt code` (`Semantics/Instruction.lean`): `if $rs >=u $rt then trap`, unsigned (opcode 0, funct 0x31). `code` = bits 15..6, ignored by execution.
- **Step arm:** `Semantics/Exec/Trap.lean`.
- **Proofs:** spec theorem `tgeu_spec_raw` (`Semantics/Specs/Trap.lean`); refinement of the manual's Operation: `Refine.tgeu_refines` (`Semantics/Refine/Trap.lean`).
- **Tests:** 2 in tests/corpus, 2 in tests/oracle; 5 in-file `#guard`/`example` statements.

### break

- **Manual:** MD00086 Vol II-A Rev 6.06, BREAK (Breakpoint), p.109.
- **Constructor:** `break code` (`Semantics/Instruction.lean`): Unconditional Breakpoint exception (opcode 0, funct 0x0d); `code` = bits 25..6, "available for use as software parameters" (MD00086 Vol II-A Rev 6.06, BREAK, p.109).
- **Step arm:** `Semantics/Exec/Trap.lean`.
- **Proofs:** spec theorem `break_spec_raw` (`Semantics/Specs/Trap.lean`); refinement of the manual's Operation: `Refine.break_refines` (`Semantics/Refine/Trap.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 13 in tests/oracle; 23 in-file `#guard`/`example` statements.

### sync

- **Manual:** MD00086 Vol II-A Rev 6.06, SYNC (Synchronize Shared Memory), p.407-411.
- **Constructor:** `sync stype` (`Semantics/Instruction.lean`): Memory-ordering barrier (opcode 0, funct 0x0f); `stype` = bits 10..6. A no-op in this single-hart model, for every `stype`.
- **Step arm:** `Semantics/Exec/Memory.lean`.
- **Proofs:** spec theorem `sync_spec_raw` (`Semantics/Specs/Memory.lean`); refinement of the manual's Operation: `Refine.sync_refines` (`Semantics/Refine/Memory.lean`).
- **Tests:** 3 in tests/oracle; 10 in-file `#guard`/`example` statements.

### pref

- **Manual:** MD00086 Vol II-A Rev 6.06, PREF (Prefetch), p.321-324.
- **Constructor:** `pref rs hint imm` (`Semantics/Instruction.lean`): Prefetch (SPECIAL3, funct `110101`; `hint` = bits 20..16, a **9-bit** signed `offset` in bits 15..7 (`imm` is that raw field), bit 6 = 0; the pre-Release 6 opcode 0x33 is removed). "Any action, including doing nothing, is permitted"; "PREF does not cause addressing-related exceptions" (MD00086 Vol II-A Rev 6.06, PREF, p.321). A no-op here.
- **Step arm:** `Semantics/Exec/Memory.lean`.
- **Proofs:** spec theorem `pref_spec_raw` (`Semantics/Specs/Memory.lean`); refinement of the manual's Operation: `Refine.pref_refines` (`Semantics/Refine/Memory.lean`).
- **Tests:** 1 in tests/asm, 3 in tests/oracle; 8 in-file `#guard`/`example` statements.

## Coprocessor 0 and system instructions

### mfc0

- **Manual:** MD00086 Vol II-A Rev 6.06, MFC0 (Move from Coprocessor 0), p.266.
- **Constructor:** `mfc0 rt rd sel` (`Semantics/Instruction.lean`): `$rt = ` CP0 register `(rd, sel)` (`rs`-field = `MF` = 0x00), for every `(rd, sel)`: a register the model does not implement reads 0 (Release 6, MFC0 p.266).
- **Step arm:** `Semantics/Exec/Cp0.lean`.
- **Proofs:** spec theorem `mfc0_spec_raw` (`Semantics/Specs/Cp0.lean`) and 4 more; refinement of the manual's Operation: `Refine.mfc0_refines` (`Semantics/Refine/Cp0.lean`).
- **Tests:** 5 in tests/asm, 74 in tests/oracle; 71 in-file `#guard`/`example` statements.

### mtc0

- **Manual:** MD00086 Vol II-A Rev 6.06, MTC0 (Move to Coprocessor 0), p.290-291.
- **Constructor:** `mtc0 rt rd sel` (`Semantics/Instruction.lean`): CP0 register `(rd, sel) := $rt` (`rs`-field = `MT` = 0x04), through the register's write mask (`Step.lean`). Same scoping as `mfc0`.
- **Step arm:** `Semantics/Exec/Cp0.lean`.
- **Proofs:** spec theorem `mtc0_spec_raw` (`Semantics/Specs/Cp0.lean`) and 10 more; refinement of the manual's Operation: `Refine.mtc0_refines` (`Semantics/Refine/Cp0.lean`).
- **Tests:** 4 in tests/asm, 74 in tests/oracle; 53 in-file `#guard`/`example` statements.

### di

- **Manual:** MD00086 Vol II-A Rev 6.06, DI (Disable Interrupts), p.164.
- **Constructor:** `di rt` (`Semantics/Instruction.lean`): Disable interrupts: `$rt = Status; Status.IE = 0` (`rs`-field = `MFMC0` = 0x0b, `rd` = 12, `sc` = bit 5 = 0; MD00086 Vol II-A Rev 6.06, DI, p.164).
- **Step arm:** `Semantics/Exec/Cp0.lean`.
- **Proofs:** spec theorem `di_spec_raw` (`Semantics/Specs/Cp0.lean`); refinement of the manual's Operation: `Refine.di_refines` (`Semantics/Refine/Cp0.lean`).
- **Tests:** 1 in tests/asm, 3 in tests/oracle; 5 in-file `#guard`/`example` statements.

### ei

- **Manual:** MD00086 Vol II-A Rev 6.06, EI (Enable Interrupts), p.176.
- **Constructor:** `ei rt` (`Semantics/Instruction.lean`): Enable interrupts: `$rt = Status; Status.IE = 1` (as `di`, `sc` = 1; MD00086 Vol II-A Rev 6.06, EI, p.176).
- **Step arm:** `Semantics/Exec/Cp0.lean`.
- **Proofs:** spec theorem `ei_spec_raw` (`Semantics/Specs/Cp0.lean`); refinement of the manual's Operation: `Refine.ei_refines` (`Semantics/Refine/Cp0.lean`).
- **Tests:** 1 in tests/asm, 3 in tests/oracle; 7 in-file `#guard`/`example` statements.

### eret

- **Manual:** MD00086 Vol II-A Rev 6.06, ERET (Exception Return), p.177-178.
- **Constructor:** `eret` (`Semantics/Instruction.lean`): Exception return: `PC := cp0Epc`, `Status.EXL := 0` (opcode 0x10 COP0, `rs`-field = `CO` = 0x10, `funct` = 0x18). No operands. Real MIPS32: **not** a delay-slotted instruction — it takes effect immediately, an architectural exception to the general branch/jump delay-slot rule (see `Step.lean`'s execution semantics and `docs/spec/INSTRUCTION-REF.md`).
- **Step arm:** `Semantics/Exec/System.lean`.
- **Proofs:** spec theorem `eret_spec_raw` (`Semantics/Specs/Cp0.lean`) and 3 more; refinement of the manual's Operation: `Refine.eret_refines` (`Semantics/Refine/System.lean`).
- **Tests:** 2 in tests/asm, 57 in tests/oracle; 11 in-file `#guard`/`example` statements.

### wait

- **Manual:** MD00086 Vol II-A Rev 6.06, WAIT (Enter Standby Mode), p.442-443.
- **Constructor:** `wait code` (`Semantics/Instruction.lean`): Enter standby mode (opcode 0x10 COP0, bit 25 = `CO` = 1, `funct` = 0x20); `code` = the 19-bit implementation-dependent field, bits 24..6. Completes, then stops the processor until an interrupt request restarts it (`State.standby`; MD00086 Vol II-A Rev 6.06, WAIT, p.442).
- **Step arm:** `Semantics/Exec/System.lean`.
- **Proofs:** spec theorem `wait_spec_raw` (`Semantics/Specs/Cp0.lean`) and 1 more; refinement of the manual's Operation: `Refine.wait_refines` (`Semantics/Refine/System.lean`).
- **Tests:** 3 in tests/oracle; 14 in-file `#guard`/`example` statements.

### rdpgpr

- **Manual:** MD00086 Vol II-A Rev 6.06, RDPGPR (Read GPR from Previous Shadow Set), p.335.
- **Constructor:** `rdpgpr rd rt` (`Semantics/Instruction.lean`): Read GPR from previous shadow set: `GPR[rd] ← SGPR[SRSCtl.PSS, rt]` (COP0, `rs`-field = `RDPGPR` = 0x0a, bits 10..0 zero; MD00086 Vol II-A Rev 6.06, RDPGPR, p.335, "MIPS32 Release 2"). With only the normal GPRs (`SRSCtl.HSS = 0`) a register move.
- **Step arm:** `Semantics/Exec/Cp0.lean`.
- **Proofs:** spec theorem `rdpgpr_spec_raw` (`Semantics/Specs/Cp0.lean`); refinement of the manual's Operation: `Refine.rdpgpr_refines` (`Semantics/Refine/Cp0.lean`).
- **Tests:** 1 in tests/oracle; 6 in-file `#guard`/`example` statements.

### wrpgpr

- **Manual:** MD00086 Vol II-A Rev 6.06, WRPGPR (Write to GPR in Previous Shadow Set), p.444.
- **Constructor:** `wrpgpr rd rt` (`Semantics/Instruction.lean`): Write GPR to previous shadow set: `SGPR[SRSCtl.PSS, rd] ← GPR[rt]` (COP0, `rs`-field = `WRPGPR` = 0x0e, bits 10..0 zero; MD00086 Vol II-A Rev 6.06, WRPGPR, p.444, "MIPS32 Release 2"). With only the normal GPRs a register move.
- **Step arm:** `Semantics/Exec/Cp0.lean`.
- **Proofs:** spec theorem `wrpgpr_spec_raw` (`Semantics/Specs/Cp0.lean`); refinement of the manual's Operation: `Refine.wrpgpr_refines` (`Semantics/Refine/Cp0.lean`).
- **Tests:** 1 in tests/oracle; 7 in-file `#guard`/`example` statements.

## Coprocessor 1 moves and branches

### mfc1

- **Manual:** MD00086 Vol II-A Rev 6.06, MFC1 (Move Word From Floating Point), p.267.
- **Constructor:** `mfc1 rt fs` (`Semantics/Instruction.lean`): `$rt = FPR[fs]` raw low word (COP1, `rs` = `MF` = 0x00).
- **Step arm:** `Semantics/Exec/FpuMove.lean`.
- **Proofs:** spec theorem `mfc1_spec_raw` (`Semantics/Specs/FpuMove.lean`); refinement of the manual's Operation: `Refine.mfc1_refines` (`Semantics/Refine/FpuMove.lean`).
- **Tests:** 2 in tests/corpus, 7 in tests/asm, 38 in tests/oracle; 5 in-file `#guard`/`example` statements.

### mtc1

- **Manual:** MD00086 Vol II-A Rev 6.06, MTC1 (Move Word to Floating Point), p.292.
- **Constructor:** `mtc1 rt fs` (`Semantics/Instruction.lean`): `FPR[fs] = $rt` raw word (COP1, `rs` = `MT` = 0x04).
- **Step arm:** `Semantics/Exec/FpuMove.lean`.
- **Proofs:** spec theorem `mtc1_spec_raw` (`Semantics/Specs/FpuMove.lean`); refinement of the manual's Operation: `Refine.mtc1_refines` (`Semantics/Refine/FpuMove.lean`).
- **Tests:** 2 in tests/corpus, 6 in tests/asm, 48 in tests/oracle; 5 in-file `#guard`/`example` statements.

### mfhc1

- **Manual:** MD00086 Vol II-A Rev 6.06, MFHC1 (Move Word From High Half of Floating Point Register), p.271.
- **Constructor:** `mfhc1 rt fs` (`Semantics/Instruction.lean`): `$rt = ` high word of the double in `fs`, i.e. `FPR[fs+1]` (COP1, `rs` = `MFH` = 0x03).
- **Step arm:** `Semantics/Exec/FpuMove.lean`.
- **Proofs:** spec theorem `mfhc1_spec_raw` (`Semantics/Specs/FpuMove.lean`); refinement of the manual's Operation: `Refine.mfhc1_refines` (`Semantics/Refine/FpuMove.lean`).
- **Tests:** 1 in tests/asm, 22 in tests/oracle; 7 in-file `#guard`/`example` statements.

### mthc1

- **Manual:** MD00086 Vol II-A Rev 6.06, MTHC1 (Move Word to High Half of Floating Point Register), p.295.
- **Constructor:** `mthc1 rt fs` (`Semantics/Instruction.lean`): High word of the double in `fs` (`FPR[fs+1]`) `= $rt` (COP1, `rs` = `MTH` = 0x07).
- **Step arm:** `Semantics/Exec/FpuMove.lean`.
- **Proofs:** spec theorem `mthc1_spec_raw` (`Semantics/Specs/FpuMove.lean`); refinement of the manual's Operation: `Refine.mthc1_refines` (`Semantics/Refine/FpuMove.lean`).
- **Tests:** 2 in tests/asm, 37 in tests/oracle; 8 in-file `#guard`/`example` statements.

### cfc1

- **Manual:** MD00086 Vol II-A Rev 6.06, CFC1 (Move Control Word From Floating Point), p.129-130.
- **Constructor:** `cfc1 rt fs` (`Semantics/Instruction.lean`): `$rt = FP_Control[fs]` (COP1, `rs` = `CF` = 0x02): FIR 0, FCCR 25, FEXR 26, FENR 28, FCSR 31.
- **Step arm:** `Semantics/Exec/FpuControl.lean`.
- **Proofs:** spec theorem `cfc1_spec_raw` (`Semantics/Specs/FpuControl.lean`) and 1 more; refinement of the manual's Operation: `Refine.cfc1_refines` (`Semantics/Refine/FpuControl.lean`).
- **Tests:** 5 in tests/asm, 47 in tests/oracle; 14 in-file `#guard`/`example` statements.

### ctc1

- **Manual:** MD00086 Vol II-A Rev 6.06, CTC1 (Move Control Word to Floating Point), p.149-151.
- **Constructor:** `ctc1 rt fs` (`Semantics/Instruction.lean`): `FP_Control[fs] = $rt` (COP1, `rs` = `CT` = 0x06), then CheckFPException.
- **Step arm:** `Semantics/Exec/FpuControl.lean`.
- **Proofs:** spec theorem `ctc1_spec_raw` (`Semantics/Specs/FpuControl.lean`) and 1 more; refinement of the manual's Operation: `Refine.ctc1_refines` (`Semantics/Refine/FpuControl.lean`).
- **Tests:** 4 in tests/asm, 49 in tests/oracle; 19 in-file `#guard`/`example` statements.

### lwc1

- **Manual:** MD00086 Vol II-A Rev 6.06, LWC1 (Load Word to Floating Point), p.236.
- **Constructor:** `lwc1 rs ft imm` (`Semantics/Instruction.lean`): `FPR[ft] = MEM32[$rs + sext(imm)]` (opcode 0x31).
- **Step arm:** `Semantics/Exec/FpuMemory.lean`.
- **Proofs:** spec theorem `lwc1_spec_raw` (`Semantics/Specs/FpuMemory.lean`) and 1 more; refinement of the manual's Operation: `Refine.lwc1_refines` (`Semantics/Refine/FpuMemory.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 5 in tests/oracle; 6 in-file `#guard`/`example` statements.

### swc1

- **Manual:** MD00086 Vol II-A Rev 6.06, SWC1 (Store Word from Floating Point), p.393.
- **Constructor:** `swc1 rs ft imm` (`Semantics/Instruction.lean`): `MEM32[$rs + sext(imm)] = FPR[ft]` (opcode 0x39).
- **Step arm:** `Semantics/Exec/FpuMemory.lean`.
- **Proofs:** spec theorem `swc1_spec_raw` (`Semantics/Specs/FpuMemory.lean`) and 1 more; refinement of the manual's Operation: `Refine.swc1_refines` (`Semantics/Refine/FpuMemory.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 3 in tests/oracle; 5 in-file `#guard`/`example` statements.

### ldc1

- **Manual:** MD00086 Vol II-A Rev 6.06, LDC1 (Load Doubleword to Floating Point), p.215.
- **Constructor:** `ldc1 rs ft imm` (`Semantics/Instruction.lean`): `{FPR[ft+1],FPR[ft]} = MEM64[$rs + sext(imm)]`, doubleword-aligned (opcode 0x35).
- **Step arm:** `Semantics/Exec/FpuMemory.lean`.
- **Proofs:** spec theorem `ldc1_spec_raw` (`Semantics/Specs/FpuMemory.lean`); refinement of the manual's Operation: `Refine.ldc1_refines` (`Semantics/Refine/FpuMemory.lean`).
- **Tests:** 1 in tests/corpus, 2 in tests/asm, 6 in tests/oracle; 9 in-file `#guard`/`example` statements.

### sdc1

- **Manual:** MD00086 Vol II-A Rev 6.06, SDC1 (Store Doubleword from Floating Point), p.362.
- **Constructor:** `sdc1 rs ft imm` (`Semantics/Instruction.lean`): `MEM64[$rs + sext(imm)] = {FPR[ft+1],FPR[ft]}`, doubleword-aligned (opcode 0x3d).
- **Step arm:** `Semantics/Exec/FpuMemory.lean`.
- **Proofs:** spec theorem `sdc1_spec_raw` (`Semantics/Specs/FpuMemory.lean`); refinement of the manual's Operation: `Refine.sdc1_refines` (`Semantics/Refine/FpuMemory.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 8 in tests/oracle; 8 in-file `#guard`/`example` statements.

## FPU arithmetic, single

### add.s

- **Manual:** MD00086 Vol II-A Rev 6.06, ADD.fmt (Floating Point Add), p.34.
- **Assembler form:** `add.s`.
- **Constructor:** `addS fd fs ft` (`Semantics/Instruction.lean`): `fd = fs + ft` (funct 0x00).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `addS_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.addS_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 1 in tests/corpus, 2 in tests/asm, 12 in tests/oracle; 14 in-file `#guard`/`example` statements.

### sub.s

- **Manual:** MD00086 Vol II-A Rev 6.06, SUB.fmt (Floating Point Subtract), p.389.
- **Assembler form:** `sub.s`.
- **Constructor:** `subS fd fs ft` (`Semantics/Instruction.lean`): `fd = fs − ft` (funct 0x01).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `subS_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.subS_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 7 in tests/oracle; 3 in-file `#guard`/`example` statements.

### mul.s

- **Manual:** MD00086 Vol II-A Rev 6.06, MUL.fmt (Floating Point Multiply), p.302.
- **Assembler form:** `mul.s`.
- **Constructor:** `mulS fd fs ft` (`Semantics/Instruction.lean`): `fd = fs × ft` (funct 0x02).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `mulS_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.mulS_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 1 in tests/corpus, 10 in tests/oracle; 8 in-file `#guard`/`example` statements.

### div.s

- **Manual:** MD00086 Vol II-A Rev 6.06, DIV.fmt (Floating Point Divide), p.170.
- **Assembler form:** `div.s`.
- **Constructor:** `divS fd fs ft` (`Semantics/Instruction.lean`): `fd = fs / ft` (funct 0x03).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `divS_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.divS_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 1 in tests/corpus, 3 in tests/asm, 10 in tests/oracle; 11 in-file `#guard`/`example` statements.

### sqrt.s

- **Manual:** MD00086 Vol II-A Rev 6.06, SQRT.fmt (Floating Point Square Root), p.382.
- **Assembler form:** `sqrt.s`.
- **Constructor:** `sqrtS fd fs` (`Semantics/Instruction.lean`): `fd = sqrt fs` (funct 0x04).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `sqrtS_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.sqrtS_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 6 in tests/oracle; 6 in-file `#guard`/`example` statements.

### abs.s

- **Manual:** MD00086 Vol II-A Rev 6.06, ABS.fmt (Floating Point Absolute Value), p.32.
- **Assembler form:** `abs.s`.
- **Constructor:** `absS fd fs` (`Semantics/Instruction.lean`): `fd = |fs|`, non-arithmetic with `FCSR.ABS2008 = 1` (funct 0x05).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `absS_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.absS_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 3 in tests/oracle; 7 in-file `#guard`/`example` statements.

### mov.s

- **Manual:** MD00086 Vol II-A Rev 6.06, MOV.fmt (Floating Point Move), p.275.
- **Assembler form:** `mov.s`.
- **Constructor:** `movS fd fs` (`Semantics/Instruction.lean`): `fd = fs`, non-arithmetic (funct 0x06).
- **Step arm:** `Semantics/Exec/FpuMove.lean`.
- **Proofs:** spec theorem `movS_spec_raw` (`Semantics/Specs/FpuMove.lean`); refinement of the manual's Operation: `Refine.movS_refines` (`Semantics/Refine/FpuMove.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 4 in tests/oracle; 4 in-file `#guard`/`example` statements.

### neg.s

- **Manual:** MD00086 Vol II-A Rev 6.06, NEG.fmt (Floating Point Negate), p.307.
- **Assembler form:** `neg.s`.
- **Constructor:** `negS fd fs` (`Semantics/Instruction.lean`): `fd = −fs`, non-arithmetic with `FCSR.ABS2008 = 1` (funct 0x07).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `negS_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.negS_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 1 in tests/corpus, 3 in tests/oracle; 7 in-file `#guard`/`example` statements.

### recip.s

- **Manual:** MD00086 Vol II-A Rev 6.06, RECIP.fmt (Reciprocal Approximation), p.336.
- **Assembler form:** `recip.s`.
- **Constructor:** `recipS fd fs` (`Semantics/Instruction.lean`): `fd = 1.0 / fs` (funct 0x15).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `recipS_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.recipS_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 1 in tests/asm, 2 in tests/oracle; 5 in-file `#guard`/`example` statements.

### rsqrt.s

- **Manual:** MD00086 Vol II-A Rev 6.06, RSQRT.fmt (Reciprocal Square Root Approximation), p.343.
- **Assembler form:** `rsqrt.s`.
- **Constructor:** `rsqrtS fd fs` (`Semantics/Instruction.lean`): `fd = 1.0 / sqrt fs` (funct 0x16).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `rsqrtS_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.rsqrtS_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 1 in tests/asm, 2 in tests/oracle; 4 in-file `#guard`/`example` statements.

### round.w.s

- **Manual:** MD00086 Vol II-A Rev 6.06, ROUND.W.fmt (Floating Point Round to Word Fixed Point), p.342.
- **Assembler form:** `round.w.s`.
- **Constructor:** `roundWS fd fs` (`Semantics/Instruction.lean`): Single → word, round to nearest even (funct 0x0c).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `roundWS_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.roundWS_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 3 in tests/oracle; 5 in-file `#guard`/`example` statements.

### trunc.w.s

- **Manual:** MD00086 Vol II-A Rev 6.06, TRUNC.W.fmt (Floating Point Truncate to Word Fixed Point), p.441.
- **Assembler form:** `trunc.w.s`.
- **Constructor:** `truncWS fd fs` (`Semantics/Instruction.lean`): Single → word, round toward zero (funct 0x0d).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `truncWS_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.truncWS_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 3 in tests/oracle; 8 in-file `#guard`/`example` statements.

### ceil.w.s

- **Manual:** MD00086 Vol II-A Rev 6.06, CEIL.W.fmt (Floating Point Ceiling Convert to Word Fixed Point), p.128.
- **Assembler form:** `ceil.w.s`.
- **Constructor:** `ceilWS fd fs` (`Semantics/Instruction.lean`): Single → word, round toward +∞ (funct 0x0e).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `ceilWS_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.ceilWS_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 3 in tests/oracle; 3 in-file `#guard`/`example` statements.

### floor.w.s

- **Manual:** MD00086 Vol II-A Rev 6.06, FLOOR.W.fmt (Floating Point Floor Convert to Word Fixed Point), p.186.
- **Assembler form:** `floor.w.s`.
- **Constructor:** `floorWS fd fs` (`Semantics/Instruction.lean`): Single → word, round toward −∞ (funct 0x0f).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `floorWS_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.floorWS_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 3 in tests/oracle; 3 in-file `#guard`/`example` statements.

### cvt.w.s

- **Manual:** MD00086 Vol II-A Rev 6.06, CVT.W.fmt (Floating Point Convert to Word Fixed Point), p.160.
- **Assembler form:** `cvt.w.s`.
- **Constructor:** `cvtWS fd fs` (`Semantics/Instruction.lean`): Single → word, rounding per FCSR.RM (funct 0x24).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `cvtWS_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.cvtWS_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/corpus, 2 in tests/asm, 8 in tests/oracle; 11 in-file `#guard`/`example` statements.

### cvt.d.s

- **Manual:** MD00086 Vol II-A Rev 6.06, CVT.D.fmt (Floating Point Convert to Double Floating Point), p.153.
- **Assembler form:** `cvt.d.s`.
- **Constructor:** `cvtDS fd fs` (`Semantics/Instruction.lean`): Single → double (fmt = S, funct 0x21).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `cvtDS_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.cvtDS_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/corpus, 5 in tests/oracle; 6 in-file `#guard`/`example` statements.

### cvt.s.w

- **Manual:** MD00086 Vol II-A Rev 6.06, CVT.S.fmt (Floating Point Convert to Single Floating Point), p.159.
- **Assembler form:** `cvt.s.w`.
- **Constructor:** `cvtSW fd fs` (`Semantics/Instruction.lean`): Word → single, rounding per FCSR.RM (fmt = W = 0x14, funct 0x20).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `cvtSW_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.cvtSW_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/corpus, 2 in tests/oracle; 5 in-file `#guard`/`example` statements.

### cvt.d.w

- **Manual:** MD00086 Vol II-A Rev 6.06, CVT.D.fmt (Floating Point Convert to Double Floating Point), p.153.
- **Assembler form:** `cvt.d.w`.
- **Constructor:** `cvtDW fd fs` (`Semantics/Instruction.lean`): Word → double, exact (fmt = W, funct 0x21).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `cvtDW_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.cvtDW_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/corpus, 2 in tests/oracle; 4 in-file `#guard`/`example` statements.

## FPU arithmetic, double

### add.d

- **Manual:** MD00086 Vol II-A Rev 6.06, ADD.fmt (Floating Point Add), p.34.
- **Assembler form:** `add.d`.
- **Constructor:** `addD fd fs ft` (`Semantics/Instruction.lean`): `fd = fs + ft` (funct 0x00).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `addD_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.addD_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 5 in tests/oracle; 6 in-file `#guard`/`example` statements.

### sub.d

- **Manual:** MD00086 Vol II-A Rev 6.06, SUB.fmt (Floating Point Subtract), p.389.
- **Assembler form:** `sub.d`.
- **Constructor:** `subD fd fs ft` (`Semantics/Instruction.lean`): `fd = fs − ft` (funct 0x01).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `subD_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.subD_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 1 in tests/corpus, 4 in tests/oracle; 2 in-file `#guard`/`example` statements.

### mul.d

- **Manual:** MD00086 Vol II-A Rev 6.06, MUL.fmt (Floating Point Multiply), p.302.
- **Assembler form:** `mul.d`.
- **Constructor:** `mulD fd fs ft` (`Semantics/Instruction.lean`): `fd = fs × ft` (funct 0x02).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `mulD_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.mulD_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 1 in tests/corpus, 6 in tests/oracle; 2 in-file `#guard`/`example` statements.

### div.d

- **Manual:** MD00086 Vol II-A Rev 6.06, DIV.fmt (Floating Point Divide), p.170.
- **Assembler form:** `div.d`.
- **Constructor:** `divD fd fs ft` (`Semantics/Instruction.lean`): `fd = fs / ft` (funct 0x03).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `divD_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.divD_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 1 in tests/corpus, 4 in tests/oracle; 4 in-file `#guard`/`example` statements.

### sqrt.d

- **Manual:** MD00086 Vol II-A Rev 6.06, SQRT.fmt (Floating Point Square Root), p.382.
- **Assembler form:** `sqrt.d`.
- **Constructor:** `sqrtD fd fs` (`Semantics/Instruction.lean`): `fd = sqrt fs` (funct 0x04).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `sqrtD_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.sqrtD_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/asm, 5 in tests/oracle; 4 in-file `#guard`/`example` statements.

### abs.d

- **Manual:** MD00086 Vol II-A Rev 6.06, ABS.fmt (Floating Point Absolute Value), p.32.
- **Assembler form:** `abs.d`.
- **Constructor:** `absD fd fs` (`Semantics/Instruction.lean`): `fd = |fs|`, non-arithmetic with `FCSR.ABS2008 = 1` (funct 0x05).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `absD_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.absD_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 1 in tests/corpus, 2 in tests/oracle; 4 in-file `#guard`/`example` statements.

### mov.d

- **Manual:** MD00086 Vol II-A Rev 6.06, MOV.fmt (Floating Point Move), p.275.
- **Assembler form:** `mov.d`.
- **Constructor:** `movD fd fs` (`Semantics/Instruction.lean`): `fd = fs`, non-arithmetic (funct 0x06).
- **Step arm:** `Semantics/Exec/FpuMove.lean`.
- **Proofs:** spec theorem `movD_spec_raw` (`Semantics/Specs/FpuMove.lean`); refinement of the manual's Operation: `Refine.movD_refines` (`Semantics/Refine/FpuMove.lean`).
- **Tests:** 1 in tests/corpus, 1 in tests/oracle; 3 in-file `#guard`/`example` statements.

### neg.d

- **Manual:** MD00086 Vol II-A Rev 6.06, NEG.fmt (Floating Point Negate), p.307.
- **Assembler form:** `neg.d`.
- **Constructor:** `negD fd fs` (`Semantics/Instruction.lean`): `fd = −fs`, non-arithmetic with `FCSR.ABS2008 = 1` (funct 0x07).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `negD_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.negD_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 1 in tests/corpus, 2 in tests/oracle; 4 in-file `#guard`/`example` statements.

### recip.d

- **Manual:** MD00086 Vol II-A Rev 6.06, RECIP.fmt (Reciprocal Approximation), p.336.
- **Assembler form:** `recip.d`.
- **Constructor:** `recipD fd fs` (`Semantics/Instruction.lean`): `fd = 1.0 / fs` (funct 0x15).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `recipD_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.recipD_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 2 in tests/oracle; 2 in-file `#guard`/`example` statements.

### rsqrt.d

- **Manual:** MD00086 Vol II-A Rev 6.06, RSQRT.fmt (Reciprocal Square Root Approximation), p.343.
- **Assembler form:** `rsqrt.d`.
- **Constructor:** `rsqrtD fd fs` (`Semantics/Instruction.lean`): `fd = 1.0 / sqrt fs` (funct 0x16).
- **Step arm:** `Semantics/Exec/FpuArith.lean`.
- **Proofs:** spec theorem `rsqrtD_spec_raw` (`Semantics/Specs/FpuArith.lean`); refinement of the manual's Operation: `Refine.rsqrtD_refines` (`Semantics/Refine/FpuArith.lean`).
- **Tests:** 2 in tests/oracle; 4 in-file `#guard`/`example` statements.

### round.w.d

- **Manual:** MD00086 Vol II-A Rev 6.06, ROUND.W.fmt (Floating Point Round to Word Fixed Point), p.342.
- **Assembler form:** `round.w.d`.
- **Constructor:** `roundWD fd fs` (`Semantics/Instruction.lean`): Double → word, round to nearest even (funct 0x0c).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `roundWD_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.roundWD_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/asm, 3 in tests/oracle; 6 in-file `#guard`/`example` statements.

### trunc.w.d

- **Manual:** MD00086 Vol II-A Rev 6.06, TRUNC.W.fmt (Floating Point Truncate to Word Fixed Point), p.441.
- **Assembler form:** `trunc.w.d`.
- **Constructor:** `truncWD fd fs` (`Semantics/Instruction.lean`): Double → word, round toward zero (funct 0x0d).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `truncWD_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.truncWD_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/asm, 3 in tests/oracle; 4 in-file `#guard`/`example` statements.

### ceil.w.d

- **Manual:** MD00086 Vol II-A Rev 6.06, CEIL.W.fmt (Floating Point Ceiling Convert to Word Fixed Point), p.128.
- **Assembler form:** `ceil.w.d`.
- **Constructor:** `ceilWD fd fs` (`Semantics/Instruction.lean`): Double → word, round toward +∞ (funct 0x0e).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `ceilWD_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.ceilWD_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/asm, 3 in tests/oracle; 4 in-file `#guard`/`example` statements.

### floor.w.d

- **Manual:** MD00086 Vol II-A Rev 6.06, FLOOR.W.fmt (Floating Point Floor Convert to Word Fixed Point), p.186.
- **Assembler form:** `floor.w.d`.
- **Constructor:** `floorWD fd fs` (`Semantics/Instruction.lean`): Double → word, round toward −∞ (funct 0x0f).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `floorWD_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.floorWD_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/asm, 3 in tests/oracle; 4 in-file `#guard`/`example` statements.

### cvt.w.d

- **Manual:** MD00086 Vol II-A Rev 6.06, CVT.W.fmt (Floating Point Convert to Word Fixed Point), p.160.
- **Assembler form:** `cvt.w.d`.
- **Constructor:** `cvtWD fd fs` (`Semantics/Instruction.lean`): Double → word, rounding per FCSR.RM (funct 0x24).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `cvtWD_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.cvtWD_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/corpus, 4 in tests/oracle; 5 in-file `#guard`/`example` statements.

### cvt.s.d

- **Manual:** MD00086 Vol II-A Rev 6.06, CVT.S.fmt (Floating Point Convert to Single Floating Point), p.159.
- **Assembler form:** `cvt.s.d`.
- **Constructor:** `cvtSD fd fs` (`Semantics/Instruction.lean`): Double → single, rounding per FCSR.RM (fmt = D, funct 0x20).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `cvtSD_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.cvtSD_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/corpus, 5 in tests/oracle; 4 in-file `#guard`/`example` statements.

### eretnc

- **Manual:** MD00086 Vol II-A Rev 6.06, ERETNC (Exception Return No Clear), p.179-180.
- **Constructor:** `eretnc` (`Semantics/Instruction.lean`): `ERETNC`: exception return without clearing `LLbit` (MD00086 Vol II-A Rev 6.06, ERETNC, p.179-180: COP0, `CO` = 1, bits 24..7 zero, bit 6 = 1, funct `ERET` = 0x18). "ERETNC is identical to ERET except that an ERETNC will not clear the LLbit"; required by `Config5.LLB = 1` ("ERETNC instruction added", MD00090 Vol III Rev 6.02 Table 9.69, p.264). A CTI.
- **Step arm:** `Semantics/Exec/System.lean`.
- **Proofs:** spec theorem `eretnc_spec_raw` (`Semantics/Specs/Cp0.lean`) and 2 more; refinement of the manual's Operation: `Refine.eretnc_refines` (`Semantics/Refine/System.lean`).
- **Tests:** 2 in tests/oracle; 8 in-file `#guard`/`example` statements.

### sigrie

- **Manual:** MD00086 Vol II-A Rev 6.06, SIGRIE (Signal Reserved Instruction Exception), p.375.
- **Constructor:** `sigrie code` (`Semantics/Instruction.lean`): `SIGRIE code`: signal a Reserved Instruction exception (MD00086 Vol II-A Rev 6.06, SIGRIE, p.375: REGIMM, `rs` = 0, `rt` = `SIGRIE` = 0x17, 16-bit `code` in bits 15..0, "available for software use"). "MIPS32 Release 6"; "required as of Release 6".
- **Step arm:** `Semantics/Exec/Trap.lean`.
- **Proofs:** spec theorem `sigrie_spec_raw` (`Semantics/Specs/Trap.lean`); refinement of the manual's Operation: `Refine.sigrie_refines` (`Semantics/Refine/Trap.lean`).
- **Tests:** 1 in tests/oracle; 6 in-file `#guard`/`example` statements.

### cache

- **Manual:** MD00086 Vol II-A Rev 6.06, CACHE (Perform Cache Operation), p.114-121.
- **Constructor:** `cache base op off` (`Semantics/Instruction.lean`): `CACHE op, offset(base)`: perform cache operation `op` (MD00086 Vol II-A Rev 6.06, CACHE, p.114-120, Release 6 diagram: SPECIAL3, `base` 25..21, `op` 20..16, 9-bit `offset` 15..7, `0` bit 6, funct `CACHE` = 0x25). The model has no cache: "The operation of this instruction is UNDEFINED for any operation/cache combination that is not implemented. In Release 6, the instruction in this case should perform no operation" (p.119). A coprocessor-0 instruction for the usability check ("A COP0 or Cache instruction", MD00090 Vol III Rev 6.02 §6.2.22, p.100).
- **Step arm:** `Semantics/Exec/System.lean`.
- **Proofs:** spec theorem `cache_spec_raw` (`Semantics/Specs/Cp0.lean`) and 1 more; refinement of the manual's Operation: `Refine.cache_refines` (`Semantics/Refine/System.lean`).
- **Tests:** 1 in tests/oracle; 9 in-file `#guard`/`example` statements.

## Release 6 compact branches and jumps (no delay slot)

### bc

- **Manual:** MD00086 Vol II-A Rev 6.06, BC (Branch, Compact), p.53.
- **Constructor:** `bc off` (`Semantics/Instruction.lean`): `BC offset`: `PC ← PC + 4 + sext(offset ‖ 00)` (opcode `110010`, 26-bit offset; BC, p.53).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.bc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 3 in tests/oracle; 1 in-file `#guard`/`example` statements.

### balc

- **Manual:** MD00086 Vol II-A Rev 6.06, BALC (Branch and Link, Compact), p.52.
- **Constructor:** `balc off` (`Semantics/Instruction.lean`): `BALC offset`: `GPR[31] ← PC + 4`, then as `bc` (opcode `111010`; BALC, p.52).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `balc_spec_raw` (`Semantics/Specs/CompactBranch.lean`) and 1 more; refinement of the manual's Operation: `Refine.balc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 1 in tests/oracle; 2 in-file `#guard`/`example` statements.

### beqc

- **Manual:** MD00086 Vol II-A Rev 6.06, B<cond>C (Compact Compare-and-Branch Instructions), p.82-85.
- **Constructor:** `beqc rs rt off` (`Semantics/Instruction.lean`): `BEQC rs, rt, offset`: branch if `GPR[rs] = GPR[rt]` (POP10 `001000`, `0 < rs < rt`; B<cond>C, p.82-85).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `beqc_spec_raw` (`Semantics/Specs/CompactBranch.lean`) and 3 more; refinement of the manual's Operation: `Refine.beqc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 2 in tests/oracle; 3 in-file `#guard`/`example` statements.

### bnec

- **Manual:** MD00086 Vol II-A Rev 6.06, B<cond>C (Compact Compare-and-Branch Instructions), p.82-85.
- **Constructor:** `bnec rs rt off` (`Semantics/Instruction.lean`): `BNEC rs, rt, offset`: branch if `GPR[rs] ≠ GPR[rt]` (POP30 `011000`, `0 < rs < rt`; p.82-85).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bnec_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.bnec_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

### bltc

- **Manual:** MD00086 Vol II-A Rev 6.06, B<cond>C (Compact Compare-and-Branch Instructions), p.82-85.
- **Constructor:** `bltc rs rt off` (`Semantics/Instruction.lean`): `BLTC rs, rt, offset`: branch if `GPR[rs] < GPR[rt]`, signed (POP27 `010111`, `rs ≠ 0`, `rt ≠ 0`, `rs ≠ rt`; p.82-85).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bltc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.bltc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 1 in tests/oracle; 3 in-file `#guard`/`example` statements.

### bgec

- **Manual:** MD00086 Vol II-A Rev 6.06, B<cond>C (Compact Compare-and-Branch Instructions), p.82-85.
- **Constructor:** `bgec rs rt off` (`Semantics/Instruction.lean`): `BGEC rs, rt, offset`: branch if `GPR[rs] ≥ GPR[rt]`, signed (POP26 `010110`, `rs ≠ 0`, `rt ≠ 0`, `rs ≠ rt`; p.82-85).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bgec_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.bgec_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 1 in tests/oracle; 3 in-file `#guard`/`example` statements.

### bltuc

- **Manual:** MD00086 Vol II-A Rev 6.06, B<cond>C (Compact Compare-and-Branch Instructions), p.82-85.
- **Constructor:** `bltuc rs rt off` (`Semantics/Instruction.lean`): `BLTUC rs, rt, offset`: branch if `GPR[rs] < GPR[rt]`, unsigned (POP07 `000111`, `rs ≠ 0`, `rt ≠ 0`, `rs ≠ rt`; p.82-85).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bltuc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.bltuc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 1 in tests/oracle; 3 in-file `#guard`/`example` statements.

### bgeuc

- **Manual:** MD00086 Vol II-A Rev 6.06, B<cond>C (Compact Compare-and-Branch Instructions), p.82-85.
- **Constructor:** `bgeuc rs rt off` (`Semantics/Instruction.lean`): `BGEUC rs, rt, offset`: branch if `GPR[rs] ≥ GPR[rt]`, unsigned (POP06 `000110`, `rs ≠ 0`, `rt ≠ 0`, `rs ≠ rt`; p.82-85).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bgeuc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.bgeuc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 1 in tests/oracle; 3 in-file `#guard`/`example` statements.

### blezc

- **Manual:** MD00086 Vol II-A Rev 6.06, B<cond>C (Compact Compare-and-Branch Instructions), p.82-85.
- **Constructor:** `blezc rt off` (`Semantics/Instruction.lean`): `BLEZC rt, offset`: branch if `GPR[rt] ≤ 0` (POP26, `rs = 0`, `rt ≠ 0`; p.82-85).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `blezc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.blezc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

### bgezc

- **Manual:** MD00086 Vol II-A Rev 6.06, B<cond>C (Compact Compare-and-Branch Instructions), p.82-85.
- **Constructor:** `bgezc rt off` (`Semantics/Instruction.lean`): `BGEZC rt, offset`: branch if `GPR[rt] ≥ 0` (POP26, `rs = rt ≠ 0`; p.82-85).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bgezc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.bgezc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 2 in tests/oracle; 1 in-file `#guard`/`example` statements.

### bgtzc

- **Manual:** MD00086 Vol II-A Rev 6.06, B<cond>C (Compact Compare-and-Branch Instructions), p.82-85.
- **Constructor:** `bgtzc rt off` (`Semantics/Instruction.lean`): `BGTZC rt, offset`: branch if `GPR[rt] > 0` (POP27, `rs = 0`, `rt ≠ 0`; p.82-85).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bgtzc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.bgtzc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

### bltzc

- **Manual:** MD00086 Vol II-A Rev 6.06, B<cond>C (Compact Compare-and-Branch Instructions), p.82-85.
- **Constructor:** `bltzc rt off` (`Semantics/Instruction.lean`): `BLTZC rt, offset`: branch if `GPR[rt] < 0` (POP27, `rs = rt ≠ 0`; p.82-85).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bltzc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.bltzc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 2 in tests/oracle; 1 in-file `#guard`/`example` statements.

### beqzc

- **Manual:** MD00086 Vol II-A Rev 6.06, B<cond>C (Compact Compare-and-Branch Instructions), p.82-85.
- **Constructor:** `beqzc rs off` (`Semantics/Instruction.lean`): `BEQZC rs, offset`: branch if `GPR[rs] = 0` (POP66 `110110`, `rs ≠ 0`, 21-bit offset; p.82-85).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `beqzc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.beqzc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 1 in tests/oracle; 2 in-file `#guard`/`example` statements.

### bnezc

- **Manual:** MD00086 Vol II-A Rev 6.06, B<cond>C (Compact Compare-and-Branch Instructions), p.82-85.
- **Constructor:** `bnezc rs off` (`Semantics/Instruction.lean`): `BNEZC rs, offset`: branch if `GPR[rs] ≠ 0` (POP76 `111110`, `rs ≠ 0`, 21-bit offset; p.82-85).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bnezc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.bnezc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 3 in tests/oracle; 2 in-file `#guard`/`example` statements.

### blezalc

- **Manual:** MD00086 Vol II-A Rev 6.06, B{LE,GE,GT,LT,EQ,NE}ZALC (Compact Zero-Compare and Branch-and-Link Instructions), p.77-79.
- **Constructor:** `blezalc rt off` (`Semantics/Instruction.lean`): `BLEZALC rt, offset`: `GPR[31] ← PC + 4`; branch if `GPR[rt] ≤ 0` (POP06, `rs = 0`, `rt ≠ 0`; B{LE,GE,GT,LT,EQ,NE}ZALC, p.77-79).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `blezalc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.blezalc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 1 in tests/oracle; 2 in-file `#guard`/`example` statements.

### bgezalc

- **Manual:** MD00086 Vol II-A Rev 6.06, B{LE,GE,GT,LT,EQ,NE}ZALC (Compact Zero-Compare and Branch-and-Link Instructions), p.77-79.
- **Constructor:** `bgezalc rt off` (`Semantics/Instruction.lean`): `BGEZALC rt, offset`: link; branch if `GPR[rt] ≥ 0` (POP06, `rs = rt ≠ 0`; p.77-79).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bgezalc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.bgezalc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 1 in tests/oracle; 2 in-file `#guard`/`example` statements.

### bgtzalc

- **Manual:** MD00086 Vol II-A Rev 6.06, B{LE,GE,GT,LT,EQ,NE}ZALC (Compact Zero-Compare and Branch-and-Link Instructions), p.77-79.
- **Constructor:** `bgtzalc rt off` (`Semantics/Instruction.lean`): `BGTZALC rt, offset`: link; branch if `GPR[rt] > 0` (POP07, `rs = 0`, `rt ≠ 0`; p.77-79).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bgtzalc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.bgtzalc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

### bltzalc

- **Manual:** MD00086 Vol II-A Rev 6.06, B{LE,GE,GT,LT,EQ,NE}ZALC (Compact Zero-Compare and Branch-and-Link Instructions), p.77-79.
- **Constructor:** `bltzalc rt off` (`Semantics/Instruction.lean`): `BLTZALC rt, offset`: link; branch if `GPR[rt] < 0` (POP07, `rs = rt ≠ 0`; p.77-79).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bltzalc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.bltzalc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

### beqzalc

- **Manual:** MD00086 Vol II-A Rev 6.06, B{LE,GE,GT,LT,EQ,NE}ZALC (Compact Zero-Compare and Branch-and-Link Instructions), p.77-79.
- **Constructor:** `beqzalc rt off` (`Semantics/Instruction.lean`): `BEQZALC rt, offset`: link; branch if `GPR[rt] = 0` (POP10, `rs = 0`, `rt ≠ 0`; p.77-79).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `beqzalc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.beqzalc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 1 in tests/oracle; 3 in-file `#guard`/`example` statements.

### bnezalc

- **Manual:** MD00086 Vol II-A Rev 6.06, B{LE,GE,GT,LT,EQ,NE}ZALC (Compact Zero-Compare and Branch-and-Link Instructions), p.77-79.
- **Constructor:** `bnezalc rt off` (`Semantics/Instruction.lean`): `BNEZALC rt, offset`: link; branch if `GPR[rt] ≠ 0` (POP30, `rs = 0`, `rt ≠ 0`; p.77-79).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bnezalc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.bnezalc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

### bovc

- **Manual:** MD00086 Vol II-A Rev 6.06, BOVC BNVC (Branch on Overflow, Compact; Branch on No Overflow, Compact), p.107-108.
- **Constructor:** `bovc rs rt off` (`Semantics/Instruction.lean`): `BOVC rs, rt, offset`: branch if `GPR[rs] + GPR[rt]` overflows 32-bit signed (POP10, `rs ≥ rt`; BOVC, p.107-108).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bovc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.bovc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 2 in tests/oracle; 6 in-file `#guard`/`example` statements.

### bnvc

- **Manual:** MD00086 Vol II-A Rev 6.06, BOVC BNVC (Branch on Overflow, Compact; Branch on No Overflow, Compact), p.107-108.
- **Constructor:** `bnvc rs rt off` (`Semantics/Instruction.lean`): `BNVC rs, rt, offset`: branch if `GPR[rs] + GPR[rt]` does not overflow (POP30, `rs ≥ rt`; BNVC, p.107-108).
- **Step arm:** `Semantics/Exec/Branch.lean`.
- **Proofs:** spec theorem `bnvc_spec_raw` (`Semantics/Specs/CompactBranch.lean`); refinement of the manual's Operation: `Refine.bnvc_refines` (`Semantics/Refine/CompactBranch.lean`).
- **Tests:** 2 in tests/oracle; 2 in-file `#guard`/`example` statements.

### jic

- **Manual:** MD00086 Vol II-A Rev 6.06, JIC (Jump Indexed, Compact), p.205.
- **Constructor:** `jic rt off` (`Semantics/Instruction.lean`): `JIC rt, offset`: `PC ← GPR[rt] + sext(offset)` (POP66, `rs = 0`; JIC, p.205).
- **Step arm:** `Semantics/Exec/Jump.lean`.
- **Proofs:** spec theorem `jic_spec_raw` (`Semantics/Specs/Jump.lean`); refinement of the manual's Operation: `Refine.jic_refines` (`Semantics/Refine/Jump.lean`).
- **Tests:** 1 in tests/oracle; 3 in-file `#guard`/`example` statements.

### jialc

- **Manual:** MD00086 Vol II-A Rev 6.06, JIALC (Jump Indexed and Link, Compact), p.203-204.
- **Constructor:** `jialc rt off` (`Semantics/Instruction.lean`): `JIALC rt, offset`: `GPR[31] ← PC + 4`, then as `jic` (POP76, `rs = 0`; JIALC, p.203).
- **Step arm:** `Semantics/Exec/Jump.lean`.
- **Proofs:** spec theorem `jialc_spec_raw` (`Semantics/Specs/Jump.lean`) and 1 more; refinement of the manual's Operation: `Refine.jialc_refines` (`Semantics/Refine/Jump.lean`).
- **Tests:** 1 in tests/oracle; 1 in-file `#guard`/`example` statements.

## FPU longword (L) conversions

### cvt.l.s

- **Manual:** MD00086 Vol II-A Rev 6.06, CVT.L.fmt (Floating Point Convert to Long Fixed Point), p.154-155.
- **Assembler form:** `cvt.l.s`.
- **Constructor:** `cvtLS fd fs` (`Semantics/Instruction.lean`): `CVT.L.S`: single → longword, rounding per FCSR.RM (fmt = S, funct 0x25; MD00086 Vol II-A Rev 6.06, CVT.L.fmt, p.154).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `cvtLS_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.cvtLS_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 2 in tests/oracle; 12 in-file `#guard`/`example` statements.

### cvt.l.d

- **Manual:** MD00086 Vol II-A Rev 6.06, CVT.L.fmt (Floating Point Convert to Long Fixed Point), p.154-155.
- **Assembler form:** `cvt.l.d`.
- **Constructor:** `cvtLD fd fs` (`Semantics/Instruction.lean`): `CVT.L.D`: double → longword, rounding per FCSR.RM (fmt = D, funct 0x25; p.154).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `cvtLD_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.cvtLD_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 2 in tests/oracle; 11 in-file `#guard`/`example` statements.

### round.l.s

- **Manual:** MD00086 Vol II-A Rev 6.06, ROUND.L.fmt (Floating Point Round to Long Fixed Point), p.341.
- **Assembler form:** `round.l.s`.
- **Constructor:** `roundLS fd fs` (`Semantics/Instruction.lean`): `ROUND.L.S`: single → longword, round to nearest even (fmt = S, funct 0x08; p.341).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `roundLS_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.roundLS_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/oracle; 7 in-file `#guard`/`example` statements.

### round.l.d

- **Manual:** MD00086 Vol II-A Rev 6.06, ROUND.L.fmt (Floating Point Round to Long Fixed Point), p.341.
- **Assembler form:** `round.l.d`.
- **Constructor:** `roundLD fd fs` (`Semantics/Instruction.lean`): `ROUND.L.D` (fmt = D, funct 0x08; p.341).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `roundLD_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.roundLD_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 2 in tests/oracle; 5 in-file `#guard`/`example` statements.

### trunc.l.s

- **Manual:** MD00086 Vol II-A Rev 6.06, TRUNC.L.fmt (Floating Point Truncate to Long Fixed Point), p.440.
- **Assembler form:** `trunc.l.s`.
- **Constructor:** `truncLS fd fs` (`Semantics/Instruction.lean`): `TRUNC.L.S`: single → longword, round toward zero (fmt = S, funct 0x09; p.440).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `truncLS_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.truncLS_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 2 in tests/oracle; 8 in-file `#guard`/`example` statements.

### trunc.l.d

- **Manual:** MD00086 Vol II-A Rev 6.06, TRUNC.L.fmt (Floating Point Truncate to Long Fixed Point), p.440.
- **Assembler form:** `trunc.l.d`.
- **Constructor:** `truncLD fd fs` (`Semantics/Instruction.lean`): `TRUNC.L.D` (fmt = D, funct 0x09; p.440).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `truncLD_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.truncLD_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/oracle; 5 in-file `#guard`/`example` statements.

### ceil.l.s

- **Manual:** MD00086 Vol II-A Rev 6.06, CEIL.L.fmt (Fixed Point Ceiling Convert to Long Fixed Point), p.127.
- **Assembler form:** `ceil.l.s`.
- **Constructor:** `ceilLS fd fs` (`Semantics/Instruction.lean`): `CEIL.L.S`: single → longword, round toward +∞ (fmt = S, funct 0x0a; p.127).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `ceilLS_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.ceilLS_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 2 in tests/oracle; 7 in-file `#guard`/`example` statements.

### ceil.l.d

- **Manual:** MD00086 Vol II-A Rev 6.06, CEIL.L.fmt (Fixed Point Ceiling Convert to Long Fixed Point), p.127.
- **Assembler form:** `ceil.l.d`.
- **Constructor:** `ceilLD fd fs` (`Semantics/Instruction.lean`): `CEIL.L.D` (fmt = D, funct 0x0a; p.127).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `ceilLD_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.ceilLD_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/oracle; 6 in-file `#guard`/`example` statements.

### floor.l.s

- **Manual:** MD00086 Vol II-A Rev 6.06, FLOOR.L.fmt (Floating Point Floor Convert to Long Fixed Point), p.185.
- **Assembler form:** `floor.l.s`.
- **Constructor:** `floorLS fd fs` (`Semantics/Instruction.lean`): `FLOOR.L.S`: single → longword, round toward −∞ (fmt = S, funct 0x0b; p.185).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `floorLS_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.floorLS_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 1 in tests/oracle; 6 in-file `#guard`/`example` statements.

### floor.l.d

- **Manual:** MD00086 Vol II-A Rev 6.06, FLOOR.L.fmt (Floating Point Floor Convert to Long Fixed Point), p.185.
- **Assembler form:** `floor.l.d`.
- **Constructor:** `floorLD fd fs` (`Semantics/Instruction.lean`): `FLOOR.L.D` (fmt = D, funct 0x0b; p.185).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `floorLD_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.floorLD_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 2 in tests/oracle; 7 in-file `#guard`/`example` statements.

### cvt.s.l

- **Manual:** MD00086 Vol II-A Rev 6.06, CVT.S.fmt (Floating Point Convert to Single Floating Point), p.159.
- **Assembler form:** `cvt.s.l`.
- **Constructor:** `cvtSL fd fs` (`Semantics/Instruction.lean`): `CVT.S.L`: longword → single, rounding per FCSR.RM (fmt = L = 0x15, funct 0x20; CVT.S.fmt, p.159).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `cvtSL_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.cvtSL_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 2 in tests/oracle; 9 in-file `#guard`/`example` statements.

### cvt.d.l

- **Manual:** MD00086 Vol II-A Rev 6.06, CVT.D.fmt (Floating Point Convert to Double Floating Point), p.153.
- **Assembler form:** `cvt.d.l`.
- **Constructor:** `cvtDL fd fs` (`Semantics/Instruction.lean`): `CVT.D.L`: longword → double, rounding per FCSR.RM (fmt = L, funct 0x21; CVT.D.fmt, p.153).
- **Step arm:** `Semantics/Exec/FpuConvert.lean`.
- **Proofs:** spec theorem `cvtDL_spec_raw` (`Semantics/Specs/FpuConvert.lean`); refinement of the manual's Operation: `Refine.cvtDL_refines` (`Semantics/Refine/FpuConvert.lean`).
- **Tests:** 2 in tests/oracle; 10 in-file `#guard`/`example` statements.

## The Release 6 FPU instructions (CMP.cond, SEL, MIN/MAX, MADDF/MSUBF, RINT, CLASS, ...)

### cmp.cond.s

- **Manual:** MD00086 Vol II-A Rev 6.06, CMP.condn.fmt (Floating Point Compare Setting Mask), p.136-140.
- **Assembler forms:** `cmp.af.s`, `cmp.eq.s`, `cmp.le.s`, `cmp.lt.s`, `cmp.ne.s`, `cmp.or.s`, `cmp.saf.s`, `cmp.seq.s`, `cmp.sle.s`, `cmp.slt.s`, `cmp.sne.s`, `cmp.sor.s`, `cmp.sueq.s`, `cmp.sule.s`, `cmp.sult.s`, `cmp.sun.s`, `cmp.sune.s`, `cmp.ueq.s`, `cmp.ule.s`, `cmp.ult.s`, `cmp.un.s`, `cmp.une.s`.
- **Constructor:** `cmpS cond fd fs ft` (`Semantics/Instruction.lean`): `CMP.condn.S fd, fs, ft`: `FPR[fd] ← FPR[fs] compare_cond FPR[ft]` as a 32-bit mask of all ones or all zeros (COP1, `rs` = 10100, bit 5 = 0, `condn` in bits 4..0; CMP.condn.fmt, p.136-140). `cond` is the `condn` field; only the 22 values of Table A.17 (p.457) are instructions (`cmpCondnOK`). The mnemonics are `cmp.af.s`, `cmp.un.s`, `cmp.eq.s`, `cmp.ueq.s`, `cmp.lt.s`, `cmp.ult.s`, `cmp.le.s`, `cmp.ule.s`, `cmp.saf.s`, `cmp.sun.s`, `cmp.seq.s`, `cmp.sueq.s`, `cmp.slt.s`, `cmp.sult.s`, `cmp.sle.s`, `cmp.sule.s`, `cmp.or.s`, `cmp.une.s`, `cmp.ne.s`, `cmp.sor.s`, `cmp.sune.s`, `cmp.sne.s`.
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `cmpS_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.cmpS_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 1 in tests/oracle; 82 in-file `#guard`/`example` statements.

### cmp.cond.d

- **Manual:** MD00086 Vol II-A Rev 6.06, CMP.condn.fmt (Floating Point Compare Setting Mask), p.136-140.
- **Assembler forms:** `cmp.af.d`, `cmp.eq.d`, `cmp.le.d`, `cmp.lt.d`, `cmp.ne.d`, `cmp.or.d`, `cmp.saf.d`, `cmp.seq.d`, `cmp.sle.d`, `cmp.slt.d`, `cmp.sne.d`, `cmp.sor.d`, `cmp.sueq.d`, `cmp.sule.d`, `cmp.sult.d`, `cmp.sun.d`, `cmp.sune.d`, `cmp.ueq.d`, `cmp.ule.d`, `cmp.ult.d`, `cmp.un.d`, `cmp.une.d`.
- **Constructor:** `cmpD cond fd fs ft` (`Semantics/Instruction.lean`): `CMP.condn.D fd, fs, ft`: as `cmpS`, a 64-bit mask (COP1, `rs` = 10101; p.136-140). The mnemonics are `cmp.af.d`, `cmp.un.d`, `cmp.eq.d`, `cmp.ueq.d`, `cmp.lt.d`, `cmp.ult.d`, `cmp.le.d`, `cmp.ule.d`, `cmp.saf.d`, `cmp.sun.d`, `cmp.seq.d`, `cmp.sueq.d`, `cmp.slt.d`, `cmp.sult.d`, `cmp.sle.d`, `cmp.sule.d`, `cmp.or.d`, `cmp.une.d`, `cmp.ne.d`, `cmp.sor.d`, `cmp.sune.d`, `cmp.sne.d`.
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `cmpD_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.cmpD_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 1 in tests/oracle; 70 in-file `#guard`/`example` statements.

### bc1eqz

- **Manual:** MD00086 Vol II-A Rev 6.06, BC1EQZ BC1NEZ (Branch if Coprocessor 1 (FPU) Register Bit 0 Equal/Not Equal to Zero), p.54-55.
- **Constructor:** `bc1eqz ft off` (`Semantics/Instruction.lean`): `BC1EQZ ft, offset`: branch with a delay slot if bit 0 of `FPR[ft]` is 0 (COP1, `rs` = 01001, 16-bit `offset`; BC1EQZ BC1NEZ, p.54-55). A CTI.
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `bc1eqz_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.bc1eqz_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 2 in tests/oracle; 8 in-file `#guard`/`example` statements.

### bc1nez

- **Manual:** MD00086 Vol II-A Rev 6.06, BC1EQZ BC1NEZ (Branch if Coprocessor 1 (FPU) Register Bit 0 Equal/Not Equal to Zero), p.54-55.
- **Constructor:** `bc1nez ft off` (`Semantics/Instruction.lean`): `BC1NEZ ft, offset`: branch with a delay slot if bit 0 of `FPR[ft]` is 1 (COP1, `rs` = 01101; p.54-55). A CTI.
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `bc1nez_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.bc1nez_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 2 in tests/oracle; 7 in-file `#guard`/`example` statements.

### sel.s

- **Manual:** MD00086 Vol II-A Rev 6.06, SEL.fmt (Select floating point values with FPR condition), p.368.
- **Assembler form:** `sel.s`.
- **Constructor:** `selS fd fs ft` (`Semantics/Instruction.lean`): `SEL.S fd, fs, ft`: `FPR[fd] ← FPR[fd].bit0 ? FPR[ft] : FPR[fs]` (fmt = S, funct 0x10; SEL.fmt, p.368).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `selS_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.selS_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 1 in tests/oracle; 6 in-file `#guard`/`example` statements.

### sel.d

- **Manual:** MD00086 Vol II-A Rev 6.06, SEL.fmt (Select floating point values with FPR condition), p.368.
- **Assembler form:** `sel.d`.
- **Constructor:** `selD fd fs ft` (`Semantics/Instruction.lean`): `SEL.D` (fmt = D, funct 0x10; p.368).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `selD_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.selD_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 1 in tests/oracle; 4 in-file `#guard`/`example` statements.

### seleqz.s

- **Manual:** MD00086 Vol II-A Rev 6.06, SELEQZ.fmt SELNEQZ.fmt (Select floating point value or zero with FPR condition.), p.371-372.
- **Assembler form:** `seleqz.s`.
- **Constructor:** `seleqzS fd fs ft` (`Semantics/Instruction.lean`): `SELEQZ.S fd, fs, ft`: `FPR[fd] ← FPR[ft].bit0 ? 0 : FPR[fs]` (fmt = S, funct 0x14; SELEQZ.fmt SELNEQZ.fmt, p.371).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `seleqzS_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.seleqzS_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 1 in tests/oracle; 5 in-file `#guard`/`example` statements.

### seleqz.d

- **Manual:** MD00086 Vol II-A Rev 6.06, SELEQZ.fmt SELNEQZ.fmt (Select floating point value or zero with FPR condition.), p.371-372.
- **Assembler form:** `seleqz.d`.
- **Constructor:** `seleqzD fd fs ft` (`Semantics/Instruction.lean`): `SELEQZ.D` (fmt = D, funct 0x14; p.371).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `seleqzD_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.seleqzD_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 1 in tests/oracle; 5 in-file `#guard`/`example` statements.

### selnez.s

- **Manual:** MD00086 Vol II-A Rev 6.06, SELEQZ.fmt SELNEQZ.fmt (Select floating point value or zero with FPR condition.), p.371-372.
- **Assembler form:** `selnez.s`.
- **Constructor:** `selnezS fd fs ft` (`Semantics/Instruction.lean`): `SELNEZ.S fd, fs, ft`: `FPR[fd] ← FPR[ft].bit0 ? FPR[fs] : 0` (fmt = S, funct 0x17; p.371).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `selnezS_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.selnezS_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 1 in tests/oracle; 5 in-file `#guard`/`example` statements.

### selnez.d

- **Manual:** MD00086 Vol II-A Rev 6.06, SELEQZ.fmt SELNEQZ.fmt (Select floating point value or zero with FPR condition.), p.371-372.
- **Assembler form:** `selnez.d`.
- **Constructor:** `selnezD fd fs ft` (`Semantics/Instruction.lean`): `SELNEZ.D` (fmt = D, funct 0x17; p.371).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `selnezD_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.selnezD_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 1 in tests/oracle; 4 in-file `#guard`/`example` statements.

### maddf.s

- **Manual:** MD00086 Vol II-A Rev 6.06, MADDF.fmt MSUBF.fmt (Floating Point Fused Multiply Add, Floating Point Fused Multiply Subtract), p.259-260.
- **Assembler form:** `maddf.s`.
- **Constructor:** `maddfS fd fs ft` (`Semantics/Instruction.lean`): `MADDF.S fd, fs, ft`: `FPR[fd] ← FPR[fd] + FPR[fs] × FPR[ft]`, fused (fmt = S, funct 0x18; MADDF.fmt MSUBF.fmt, p.259-260).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `maddfS_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.maddfS_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 2 in tests/oracle; 5 in-file `#guard`/`example` statements.

### maddf.d

- **Manual:** MD00086 Vol II-A Rev 6.06, MADDF.fmt MSUBF.fmt (Floating Point Fused Multiply Add, Floating Point Fused Multiply Subtract), p.259-260.
- **Assembler form:** `maddf.d`.
- **Constructor:** `maddfD fd fs ft` (`Semantics/Instruction.lean`): `MADDF.D` (fmt = D, funct 0x18; p.259-260).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `maddfD_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.maddfD_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 1 in tests/oracle; 3 in-file `#guard`/`example` statements.

### msubf.s

- **Manual:** MD00086 Vol II-A Rev 6.06, MADDF.fmt MSUBF.fmt (Floating Point Fused Multiply Add, Floating Point Fused Multiply Subtract), p.259-260.
- **Assembler form:** `msubf.s`.
- **Constructor:** `msubfS fd fs ft` (`Semantics/Instruction.lean`): `MSUBF.S fd, fs, ft`: `FPR[fd] ← FPR[fd] − FPR[fs] × FPR[ft]`, fused (fmt = S, funct 0x19; p.259-260).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `msubfS_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.msubfS_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 1 in tests/oracle; 4 in-file `#guard`/`example` statements.

### msubf.d

- **Manual:** MD00086 Vol II-A Rev 6.06, MADDF.fmt MSUBF.fmt (Floating Point Fused Multiply Add, Floating Point Fused Multiply Subtract), p.259-260.
- **Assembler form:** `msubf.d`.
- **Constructor:** `msubfD fd fs ft` (`Semantics/Instruction.lean`): `MSUBF.D` (fmt = D, funct 0x19; p.259-260).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `msubfD_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.msubfD_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 1 in tests/oracle; 5 in-file `#guard`/`example` statements.

### max.s

- **Manual:** MD00086 Vol II-A Rev 6.06, MAX.fmt MIN.fmt MAXA.fmt MINA.fmt (Scalar Floating-Point Max/Min/maxNumMag/minNumMag), p.262-265.
- **Assembler form:** `max.s`.
- **Constructor:** `maxS fd fs ft` (`Semantics/Instruction.lean`): `MAX.S fd, fs, ft`: `maxNum(FPR[fs], FPR[ft])` (fmt = S, funct 0x1e; MAX.fmt MIN.fmt MAXA.fmt MINA.fmt, p.262-265).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `maxS_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.maxS_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 2 in tests/oracle; 6 in-file `#guard`/`example` statements.

### max.d

- **Manual:** MD00086 Vol II-A Rev 6.06, MAX.fmt MIN.fmt MAXA.fmt MINA.fmt (Scalar Floating-Point Max/Min/maxNumMag/minNumMag), p.262-265.
- **Assembler form:** `max.d`.
- **Constructor:** `maxD fd fs ft` (`Semantics/Instruction.lean`): `MAX.D` (fmt = D, funct 0x1e; p.262-265).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `maxD_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.maxD_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 2 in tests/oracle; 4 in-file `#guard`/`example` statements.

### min.s

- **Manual:** MD00086 Vol II-A Rev 6.06, MAX.fmt MIN.fmt MAXA.fmt MINA.fmt (Scalar Floating-Point Max/Min/maxNumMag/minNumMag), p.262-265.
- **Assembler form:** `min.s`.
- **Constructor:** `minS fd fs ft` (`Semantics/Instruction.lean`): `MIN.S fd, fs, ft`: `minNum(FPR[fs], FPR[ft])` (fmt = S, funct 0x1c; p.262-265).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `minS_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.minS_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 2 in tests/oracle; 6 in-file `#guard`/`example` statements.

### min.d

- **Manual:** MD00086 Vol II-A Rev 6.06, MAX.fmt MIN.fmt MAXA.fmt MINA.fmt (Scalar Floating-Point Max/Min/maxNumMag/minNumMag), p.262-265.
- **Assembler form:** `min.d`.
- **Constructor:** `minD fd fs ft` (`Semantics/Instruction.lean`): `MIN.D` (fmt = D, funct 0x1c; p.262-265).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `minD_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.minD_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 2 in tests/oracle; 4 in-file `#guard`/`example` statements.

### maxa.s

- **Manual:** MD00086 Vol II-A Rev 6.06, MAX.fmt MIN.fmt MAXA.fmt MINA.fmt (Scalar Floating-Point Max/Min/maxNumMag/minNumMag), p.262-265.
- **Assembler form:** `maxa.s`.
- **Constructor:** `maxaS fd fs ft` (`Semantics/Instruction.lean`): `MAXA.S fd, fs, ft`: `maxNumMag(FPR[fs], FPR[ft])` (fmt = S, funct 0x1f; p.262-265).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `maxaS_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.maxaS_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 2 in tests/oracle; 4 in-file `#guard`/`example` statements.

### maxa.d

- **Manual:** MD00086 Vol II-A Rev 6.06, MAX.fmt MIN.fmt MAXA.fmt MINA.fmt (Scalar Floating-Point Max/Min/maxNumMag/minNumMag), p.262-265.
- **Assembler form:** `maxa.d`.
- **Constructor:** `maxaD fd fs ft` (`Semantics/Instruction.lean`): `MAXA.D` (fmt = D, funct 0x1f; p.262-265).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `maxaD_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.maxaD_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 2 in tests/oracle; 5 in-file `#guard`/`example` statements.

### mina.s

- **Manual:** MD00086 Vol II-A Rev 6.06, MAX.fmt MIN.fmt MAXA.fmt MINA.fmt (Scalar Floating-Point Max/Min/maxNumMag/minNumMag), p.262-265.
- **Assembler form:** `mina.s`.
- **Constructor:** `minaS fd fs ft` (`Semantics/Instruction.lean`): `MINA.S fd, fs, ft`: `minNumMag(FPR[fs], FPR[ft])` (fmt = S, funct 0x1d; p.262-265).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `minaS_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.minaS_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 2 in tests/oracle; 5 in-file `#guard`/`example` statements.

### mina.d

- **Manual:** MD00086 Vol II-A Rev 6.06, MAX.fmt MIN.fmt MAXA.fmt MINA.fmt (Scalar Floating-Point Max/Min/maxNumMag/minNumMag), p.262-265.
- **Assembler form:** `mina.d`.
- **Constructor:** `minaD fd fs ft` (`Semantics/Instruction.lean`): `MINA.D` (fmt = D, funct 0x1d; p.262-265).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `minaD_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.minaD_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 2 in tests/oracle; 4 in-file `#guard`/`example` statements.

### class.s

- **Manual:** MD00086 Vol II-A Rev 6.06, CLASS.fmt (Scalar Floating-Point Class Mask), p.132-133.
- **Assembler form:** `class.s`.
- **Constructor:** `classS fd fs` (`Semantics/Instruction.lean`): `CLASS.S fd, fs`: the 10-bit class mask of `FPR[fs]` (fmt = S, `ft` = 0, funct 0x1b; CLASS.fmt, p.132-133).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `classS_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.classS_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 1 in tests/oracle; 7 in-file `#guard`/`example` statements.

### class.d

- **Manual:** MD00086 Vol II-A Rev 6.06, CLASS.fmt (Scalar Floating-Point Class Mask), p.132-133.
- **Assembler form:** `class.d`.
- **Constructor:** `classD fd fs` (`Semantics/Instruction.lean`): `CLASS.D` (fmt = D, funct 0x1b; p.132-133).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `classD_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.classD_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 1 in tests/oracle; 6 in-file `#guard`/`example` statements.

### rint.s

- **Manual:** MD00086 Vol II-A Rev 6.06, RINT.fmt (Floating-Point Round to Integral), p.337-338.
- **Assembler form:** `rint.s`.
- **Constructor:** `rintS fd fs` (`Semantics/Instruction.lean`): `RINT.S fd, fs`: round to an integral value in the same format, per FCSR.RM (fmt = S, `ft` = 0, funct 0x1a; RINT.fmt, p.337-338).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `rintS_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.rintS_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 1 in tests/oracle; 7 in-file `#guard`/`example` statements.

### rint.d

- **Manual:** MD00086 Vol II-A Rev 6.06, RINT.fmt (Floating-Point Round to Integral), p.337-338.
- **Assembler form:** `rint.d`.
- **Constructor:** `rintD fd fs` (`Semantics/Instruction.lean`): `RINT.D` (fmt = D, funct 0x1a; p.337-338).
- **Step arm:** `Semantics/Exec/FpuR6.lean`.
- **Proofs:** spec theorem `rintD_spec_raw` (`Semantics/Specs/FpuR6.lean`); refinement of the manual's Operation: `Refine.rintD_refines` (`Semantics/Refine/FpuR6.lean`).
- **Tests:** 1 in tests/oracle; 5 in-file `#guard`/`example` statements.

## DVP and EVP

### dvp

- **Manual:** MD00086 Vol II-A Rev 6.06, DVP (Disable Virtual Processor), p.172-174.
- **Constructor:** `dvp rt` (`Semantics/Instruction.lean`): `DVP rt`: disable the other virtual processors (MD00086 Vol II-A Rev 6.06, DVP, p.172-173: COP0, `rs` = `MFMC0` = 01011, `rt` 20..16, bits 15..6 zero, bit 5 `sc` = 1, bits 4..3 zero, bits 2..0 = 100). "For implementations that do not support multi-threading (Config5VP=0), this instruction must be treated as a NOP instruction" (p.172); this profile has `Config5.VP = 0` (MD00090 Vol III Rev 6.02 Table 9.69, p.263; DECISIONS D5), so it is a no-op: `GPR[rt]` is not written. A coprocessor-0 instruction ("If access to Coprocessor 0 is not enabled, a Coprocessor Unusable Exception is signaled", p.172).
- **Step arm:** `Semantics/Exec/Cp0.lean`.
- **Proofs:** spec theorem `dvp_spec_raw` (`Semantics/Specs/Cp0.lean`); refinement of the manual's Operation: `Refine.dvp_refines` (`Semantics/Refine/System.lean`).
- **Tests:** 1 in tests/oracle; 4 in-file `#guard`/`example` statements.

### evp

- **Manual:** MD00086 Vol II-A Rev 6.06, EVP (Enable Virtual Processor), p.181-183.
- **Constructor:** `evp rt` (`Semantics/Instruction.lean`): `EVP rt`: enable the virtual processors (MD00086 Vol II-A Rev 6.06, EVP, p.181-182: as DVP with `sc` = 0). With `Config5.VP = 0` "this instruction must be treated as a NOP instruction" (p.181); a coprocessor-0 instruction.
- **Step arm:** `Semantics/Exec/Cp0.lean`.
- **Proofs:** spec theorem `evp_spec_raw` (`Semantics/Specs/Cp0.lean`); refinement of the manual's Operation: `Refine.evp_refines` (`Semantics/Refine/System.lean`).
- **Tests:** 1 in tests/oracle; 4 in-file `#guard`/`example` statements.

## Removed in Release 6

These pages of MD00086 Vol II-A Rev 6.06 carry "removed in Release 6" (or their encoding is reused by an R6 instruction). The model does
not decode them. A word in COP1 space raises Coprocessor Unusable (`CE = 1`) if `Status.CU1 = 0`, else Reserved Instruction; in COP0 space
Coprocessor Unusable (`CE = 0`) outside Kernel Mode, else Reserved Instruction; any other word raises Reserved Instruction.

| Mnemonic | Title | Page (Vol II-A Rev 6.06) | The word in the model |
|---|---|---|---|
| ADDI | Add Immediate Word | 35 | opcode reused by POP10 (BOVC/BEQC/BEQZALC; B<cond>C p.84 "BEQC reuses the opcode assigned to pre-Release 6 ADDI") |
| ALNV.PS | Floating Point Align Variable | 451 | pre-R6 encoding does not decode |
| BC1F | Branch on FP False | 56 | pre-R6 encoding does not decode |
| BC1FL | Branch on FP False Likely | 58 | pre-R6 encoding does not decode |
| BC1T | Branch on FP True | 60 | pre-R6 encoding does not decode |
| BC1TL | Branch on FP True Likely | 62 | pre-R6 encoding does not decode |
| BC2F | Branch on COP2 False | 66 | pre-R6 encoding does not decode |
| BC2FL | Branch on COP2 False Likely | 67 | pre-R6 encoding does not decode |
| BC2T | Branch on COP2 True | 69 | pre-R6 encoding does not decode |
| BC2TL | Branch on COP2 True Likely | 70 | pre-R6 encoding does not decode |
| BEQL | Branch on Equal Likely | 73 | pre-R6 encoding does not decode |
| BGEZAL | Branch on Greater Than or Equal to Zero and Link | 76 | pre-R6 encoding does not decode |
| BGEZALL | Branch on Greater Than or Equal to Zero and Link Likely | 80 | pre-R6 encoding does not decode |
| BGEZL | Branch on Greater Than or Equal to Zero Likely | 86 | pre-R6 encoding does not decode |
| BGTZL | Branch on Greater Than Zero Likely | 89 | opcode reused by POP27 (BGTZC/BLTZC/BLTC) when rt != 0; BGTZL form (rt = 0) is RI |
| BLEZL | Branch on Less Than or Equal to Zero Likely | 95 | opcode reused by POP26 when rt != 0; BLEZL form (rt=0) is RI |
| BLTZAL | Branch on Less Than Zero and Link | 98 | pre-R6 encoding does not decode |
| BLTZALL | Branch on Less Than Zero and Link Likely | 99 | pre-R6 encoding does not decode |
| BLTZL | Branch on Less Than Zero Likely | 101 | pre-R6 encoding does not decode |
| BNEL | Branch on Not Equal Likely | 104 | pre-R6 encoding does not decode |
| C.cond.fmt | Floating Point Compare | 110 | pre-R6 encoding does not decode |
| CVT.PS.S | Floating Point Convert Pair to Paired Single | 456 | pre-R6 encoding does not decode |
| CVT.S.PL | Floating Point Convert Pair Lower to Single Floating Point | 157 | pre-R6 encoding does not decode |
| CVT.S.PU | Floating Point Convert Pair Upper to Single Floating Point | 158 | pre-R6 encoding does not decode |
| DDIV | Doubleword Divide | 161 | pre-R6 encoding does not decode |
| DDIVU | Doubleword Divide Unsigned | 162 | pre-R6 encoding does not decode |
| DIV | Divide Word | 165 | pre-R6 encoding does not decode |
| DIVU | Divide Unsigned Word | 171 | pre-R6 encoding does not decode |
| JALX | Jump and Link Exchange | 201 | pre-R6 encoding does not decode |
| LDXC1 | Load Doubleword Indexed to Floating Point | 218 | pre-R6 encoding does not decode |
| LUXC1 | Load Doubleword Indexed Unaligned to Floating Point | 234 | pre-R6 encoding does not decode |
| LWL | Load Word Left | 241 | pre-R6 encoding does not decode |
| LWLE | Load Word Left EVA | 243 | pre-R6 encoding does not decode |
| LWR | Load Word Right | 248 | pre-R6 encoding does not decode |
| LWRE | Load Word Right EVA | 252 | pre-R6 encoding does not decode |
| LWXC1 | Load Word Indexed to Floating Point | 254 | pre-R6 encoding does not decode |
| MADD | Multiply and Add Word to Hi, Lo | 255 | pre-R6 encoding does not decode |
| MADD.fmt | Floating Point Multiply Add | 256 | pre-R6 encoding does not decode |
| MADDU | Multiply and Add Unsigned Word to Hi,Lo | 261 | pre-R6 encoding does not decode |
| MFHI | Move From HI Register | 273 | pre-R6 encoding does not decode |
| MFLO | Move From LO Register | 274 | pre-R6 encoding does not decode |
| MOVF | Move Conditional on Floating Point False | 276 | pre-R6 encoding does not decode |
| MOVF.fmt | Floating Point Move Conditional on Floating Point False | 277 | pre-R6 encoding does not decode |
| MOVN | Move Conditional on Not Zero | 279 | pre-R6 encoding does not decode |
| MOVN.fmt | Floating Point Move Conditional on Not Zero | 280 | pre-R6 encoding does not decode |
| MOVT | Move Conditional on Floating Point True | 281 | pre-R6 encoding does not decode |
| MOVT.fmt | Floating Point Move Conditional on Floating Point True | 282 | pre-R6 encoding does not decode |
| MOVZ | Move Conditional on Zero | 284 | pre-R6 encoding does not decode |
| MOVZ.fmt | Floating Point Move Conditional on Zero | 285 | pre-R6 encoding does not decode |
| MSUB | Multiply and Subtract Word to Hi, Lo | 286 | pre-R6 encoding does not decode |
| MSUB.fmt | Floating Point Multiply Subtract | 287 | pre-R6 encoding does not decode |
| MSUBU | Multiply and Subtract Word to Hi,Lo | 289 | pre-R6 encoding does not decode |
| MTHI | Move to HI Register | 297 | pre-R6 encoding does not decode |
| MTLO | Move to LO Register | 298 | pre-R6 encoding does not decode |
| MUL | Multiply Word to GPR | 299 | pre-R6 encoding does not decode |
| MULT | Multiply Word | 303 | pre-R6 encoding does not decode |
| MULTU | Multiply Unsigned Word | 304 | pre-R6 encoding does not decode |
| NMADD.fmt | Floating Point Negative Multiply Add | 308 | pre-R6 encoding does not decode |
| NMSUB.fmt | Floating Point Negative Multiply Subtract | 310 | pre-R6 encoding does not decode |
| PLL.PS | Pair Lower Lower | 319 | pre-R6 encoding does not decode |
| PLU.PS | Pair Lower Upper | 320 | pre-R6 encoding does not decode |
| PREFX | Prefetch Indexed | 329 | pre-R6 encoding does not decode |
| PUL.PS | Pair Upper Lower | 330 | pre-R6 encoding does not decode |
| PUU.PS | Pair Upper Upper | 331 | pre-R6 encoding does not decode |
| SDXC1 | Store Doubleword Indexed from Floating Point | 364 | pre-R6 encoding does not decode |
| SUXC1 | Store Doubleword Indexed Unaligned from Floating Point | 391 | pre-R6 encoding does not decode |
| SWL | Store Word Left | 397 | pre-R6 encoding does not decode |
| SWLE | Store Word Left EVA | 399 | pre-R6 encoding does not decode |
| SWR | Store Word Right | 401 | pre-R6 encoding does not decode |
| SWRE | Store Word Right EVA | 404 | pre-R6 encoding does not decode |
| SWXC1 | Store Word Indexed from Floating Point | 406 | pre-R6 encoding does not decode |
| TEQI | Trap if Equal Immediate | 417 | pre-R6 encoding does not decode |
| TGEI | Trap if Greater or Equal Immediate | 419 | pre-R6 encoding does not decode |
| TGEIU | Trap if Greater or Equal Immediate Unsigned | 420 | pre-R6 encoding does not decode |
| TLTI | Trap if Less Than Immediate | 435 | pre-R6 encoding does not decode |
| TLTIU | Trap if Less Than Immediate Unsigned | 436 | pre-R6 encoding does not decode |
| TNEI | Trap if Not Equal Immediate | 439 | pre-R6 encoding does not decode |
