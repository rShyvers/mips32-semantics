import Semantics.Instruction

/-!
# Tests for `Semantics/Instruction.lean` (decode / encode)

Moved verbatim out of `Semantics/Instruction.lean` (reviewability restructuring): the definition file now holds definitions only.
Hand-computed words decode to the expected constructor, `encode` produces the expected word,
and round trips hold on concrete instances. The general round-trip theorem is
`decode_encode` in `Semantics/Specs/DecodeSpec.lean`.
-/


-- Each instruction: hand-computed word (from INSTRUCTION-REF encodings,
-- distinct nontrivial field values) decodes to the expected variant.

-- R-type reg/reg/reg: rs=29, rt=8, rd=3
example : decode (mkRT 29#32 8#32 3#32 0#32 0x20#32) = some (.add 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x21#32) = some (.addu 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x22#32) = some (.sub 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x23#32) = some (.subu 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x24#32) = some (.and 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x25#32) = some (.or 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x26#32) = some (.xor 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x27#32) = some (.nor 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x2a#32) = some (.slt 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x2b#32) = some (.sltu 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x0b#32) = none := by decide  -- removed in R6 (was `movn`)
example : decode (mkRT 29#32 8#32 3#32 0#32 0x0a#32) = none := by decide  -- removed in R6 (was `movz`)

-- R-type shift: rd=3, rt=8, shamt=5 (rs unused/0)
example : decode (mkRT 0#32 8#32 3#32 5#32 0x00#32) = some (.sll 3#32 8#32 5#32) := by decide
example : decode (mkRT 0#32 8#32 3#32 5#32 0x02#32) = some (.srl 3#32 8#32 5#32) := by decide
example : decode (mkRT 0#32 8#32 3#32 5#32 0x03#32) = some (.sra 3#32 8#32 5#32) := by decide

-- R-type variable shift: rd=3, rt=8, rs=29 (shamt field unused/0)
example : decode (mkRT 29#32 8#32 3#32 0#32 0x04#32) = some (.sllv 3#32 8#32 29#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x06#32) = some (.srlv 3#32 8#32 29#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x07#32) = some (.srav 3#32 8#32 29#32) := by decide

-- Removed in Release 6 (decodes to `none`): R-type mult/div: rs=29, rt=8
example : decode (mkRT 29#32 8#32 0#32 0#32 0x18#32) = none := by decide  -- removed in R6 (was `mult`)
example : decode (mkRT 29#32 8#32 0#32 0#32 0x19#32) = none := by decide  -- removed in R6 (was `multu`)
example : decode (mkRT 29#32 8#32 0#32 0#32 0x1a#32) = none := by decide  -- removed in R6 (was `div`)
example : decode (mkRT 29#32 8#32 0#32 0#32 0x1b#32) = none := by decide  -- removed in R6 (was `divu`)

-- Removed in Release 6 (decodes to `none`): R-type move: rd=3
example : decode (mkRT 0#32 0#32 3#32 0#32 0x12#32) = none := by decide  -- removed in R6 (was `mflo`)
example : decode (mkRT 0#32 0#32 3#32 0#32 0x10#32) = none := by decide  -- removed in R6 (was `mfhi`)

-- Removed in Release 6 (decodes to `none`): R-type move, write direction: rs=29 (same field shape as jr)
example : decode (mkRT 29#32 0#32 0#32 0#32 0x11#32) = none := by decide  -- removed in R6 (was `mthi`)
example : decode (mkRT 29#32 0#32 0#32 0#32 0x13#32) = none := by decide  -- removed in R6 (was `mtlo`)

-- syscall: opcode 0, funct 0x0c, all other fields 0
example : decode (mkRT 0#32 0#32 0#32 0#32 0x0c#32) = some (.syscall 0#32) := by decide

-- Release 6 bit-count: SPECIAL, rs=29, rt=0, rd=3, sa=1, funct 0x11 (CLO) / 0x10 (CLZ)
-- (MD00086 Vol II-A Rev 6.06, CLO p.134, CLZ p.135).
example : decode (mkRT 29#32 0#32 3#32 1#32 0x11#32) = some (.clo 29#32 3#32) := by decide
example : decode (mkRT 29#32 0#32 3#32 1#32 0x10#32) = some (.clz 29#32 3#32) := by decide
example : decode 0x03a01851#32 = some (.clo 29#32 3#32) := by decide              -- clo $3,$29
example : decode (mkRT 29#32 1#32 3#32 1#32 0x11#32) = none := by decide          -- clo, rt ≠ 0
-- the pre-Release 6 SPECIAL2 encodings (opcode 0x1c) do not decode: SPECIAL2 is removed.
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 3#32 3#32 0#32 0x21#32) = none := by decide
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 3#32 3#32 0#32 0x20#32) = none := by decide
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 17#32 3#32 0#32 0x21#32) = none := by decide

-- Removed in Release 6 (decodes to `none`): SPECIAL2 GPR multiply: rs=29, rt=8, rd=3 (plain rs/rt/rd shape, no duplication quirk)
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 3#32 0#32 0x02#32) = none := by decide  -- removed in R6 (was `mul`)

-- Removed in Release 6 (decodes to `none`): SPECIAL2 multiply-accumulate: rs=29, rt=8 (same rs/rt shape as mult/multu)
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x00#32) = none := by decide  -- removed in R6 (was `madd`)
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x01#32) = none := by decide  -- removed in R6 (was `maddu`)
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x04#32) = none := by decide  -- removed in R6 (was `msub`)
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x05#32) = none := by decide  -- removed in R6 (was `msubu`)

-- SPECIAL3 BSHFL sign-extend/byte-swap: rd=3, rt=8, sub-field selects seb/seh/wsbh
example : decode ((0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x10#32 0x20#32) = some (.seb 3#32 8#32) := by decide
example : decode ((0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x18#32 0x20#32) = some (.seh 3#32 8#32) := by decide
example : decode ((0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x02#32 0x20#32) = some (.wsbh 3#32 8#32) := by decide
-- an unrecognized BSHFL sub-field (neither seb/seh/wsbh's) is out of v1+ scope → none
#guard decode ((0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x03#32 0x20#32) = none

-- rotr/rotrv (MIPS32r2): rd=3, rt=8, sa=5 / rs=29 -- share srl/srlv's
-- opcode/funct but overload the rs/shamt field to select rotate.
example : decode (mkRT 0x01#32 8#32 3#32 5#32 0x02#32) = some (.rotr 3#32 8#32 5#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0x01#32 0x06#32) = some (.rotrv 3#32 8#32 29#32) := by decide
-- rs=0 under funct 0x02 still decodes to plain srl (existing behavior unchanged)
example : decode (mkRT 0#32 8#32 3#32 5#32 0x02#32) = some (.srl 3#32 8#32 5#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x06#32) = some (.srlv 3#32 8#32 29#32) := by decide

-- ext/ins (MIPS32r2 bitfield extract/insert): rt=8, rs=29, pos=6, size=10
-- (so the raw `shamt` field is 6, and the raw `rd`-position field is
-- `size-1=9` for ext but `pos+size-1=15` for ins)
example : decode ((0x1f#32 <<< 26) ||| mkRT 29#32 8#32 9#32 6#32 0x00#32) = some (.ext 8#32 29#32 6#32 10#32) := by decide
example : decode ((0x1f#32 <<< 26) ||| mkRT 29#32 8#32 15#32 6#32 0x04#32) = some (.ins 8#32 29#32 6#32 10#32) := by decide
-- break: opcode 0, funct 0x0d, all other fields 0
example : decode (mkRT 0#32 0#32 0#32 0#32 0x0d#32) = some (.break 0#32) := by decide

-- sync: opcode 0, funct 0x0f, all other fields 0
example : decode (mkRT 0#32 0#32 0#32 0#32 0x0f#32) = some (.sync 0#32) := by decide
-- sync decodes the same way regardless of the (unmodeled) `stype` field,
-- here carried in the raw `shamt`-position bits (e.g. `stype = 0x10`,
-- a real MIPS32 "load ordering" hint value)
example : decode (mkRT 0#32 0#32 0#32 0x10#32 0x0f#32) = some (.sync 0x10#32) := by decide

-- R-type trap-on-condition: rs=29, rt=8
example : decode (mkRT 29#32 8#32 0#32 0#32 0x34#32) = some (.teq 29#32 8#32 0#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x36#32) = some (.tne 29#32 8#32 0#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x32#32) = some (.tlt 29#32 8#32 0#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x30#32) = some (.tge 29#32 8#32 0#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x33#32) = some (.tltu 29#32 8#32 0#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x31#32) = some (.tgeu 29#32 8#32 0#32) := by decide

-- I-type arith/logic: rs=29, rt=8, imm=0x1234
example : decode (mkIT 0x08#32 29#32 8#32 0x1234#32) = none := by decide  -- removed in R6 (was `addi`)
example : decode (mkIT 0x09#32 29#32 8#32 0x1234#32) = some (.addiu 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0a#32 29#32 8#32 0x1234#32) = some (.slti 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0b#32 29#32 8#32 0x1234#32) = some (.sltiu 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0c#32 29#32 8#32 0x1234#32) = some (.andi 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0d#32 29#32 8#32 0x1234#32) = some (.ori 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0e#32 29#32 8#32 0x1234#32) = some (.xori 29#32 8#32 0x1234#32) := by decide

-- aui (opcode 0x0f): rs=29, rt=8, imm=0x1234; `lui $8, 0x1234` is `aui $8, $0, 0x1234`
-- (MD00086 Vol II-A Rev 6.06, AUI p.47)
example : decode (mkIT 0x0f#32 0#32 8#32 0x1234#32) = some (.aui 0#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0f#32 29#32 8#32 0x1234#32) = some (.aui 29#32 8#32 0x1234#32) := by decide
example : decode 0x3c081234#32 = some (.aui 0#32 8#32 0x1234#32) := by decide     -- lui $8, 0x1234
example : encode (.aui 29#32 8#32 0x1234#32) = mkIT 0x0f#32 29#32 8#32 0x1234#32 := by decide
example : decode (encode (.aui 29#32 8#32 0x8001#32)) = some (.aui 29#32 8#32 0x8001#32) := by decide

-- load/store: rs=29 (base), rt=8 (dest/src), imm=0x1234 (offset)
example : decode (mkIT 0x23#32 29#32 8#32 0x1234#32) = some (.lw 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x2b#32 29#32 8#32 0x1234#32) = some (.sw 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x20#32 29#32 8#32 0x1234#32) = some (.lb 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x24#32 29#32 8#32 0x1234#32) = some (.lbu 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x21#32 29#32 8#32 0x1234#32) = some (.lh 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x25#32 29#32 8#32 0x1234#32) = some (.lhu 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x29#32 29#32 8#32 0x1234#32) = some (.sh 29#32 8#32 0x1234#32) := by decide

-- ll/sc (Release 6): SPECIAL3, base=29, rt=8, 9-bit offset 0x123 in bits 15..7, bit 6 = 0,
-- funct 0x36 (LL) / 0x26 (SC) (MD00086 Vol II-A Rev 6.06, LL p.223, SC p.347)
example : decode 0x7fa891b6#32 = some (.ll 29#32 8#32 0x123#32) := by decide
example : decode 0x7fa891a6#32 = some (.sc 29#32 8#32 0x123#32) := by decide
example : decode 0x7c620436#32 = some (.ll 3#32 2#32 8#32) := by decide           -- ll $2, 8($3)
example : decode 0x7c620476#32 = none := by decide                                -- ll, bit 6 = 1
-- the pre-Release 6 encodings (opcodes 0x30/0x38) do not decode
example : decode (mkIT 0x30#32 29#32 8#32 0x1234#32) = none := by decide
example : decode (mkIT 0x38#32 29#32 8#32 0x1234#32) = none := by decide

-- Removed in Release 6 (decodes to `none`): lwl/lwr/swl/swr: rs=29 (base), rt=8 (dest/src), imm=0x1234 (offset) --
-- identical field layout to lw/sw
example : decode (mkIT 0x22#32 29#32 8#32 0x1234#32) = none := by decide  -- removed in R6 (was `lwl`)
example : decode (mkIT 0x26#32 29#32 8#32 0x1234#32) = none := by decide  -- removed in R6 (was `lwr`)
example : decode (mkIT 0x2a#32 29#32 8#32 0x1234#32) = none := by decide  -- removed in R6 (was `swl`)
example : decode (mkIT 0x2e#32 29#32 8#32 0x1234#32) = none := by decide  -- removed in R6 (was `swr`)

-- branch reg/reg: rs=29, rt=8, imm=0x1234
example : decode (mkIT 0x04#32 29#32 8#32 0x1234#32) = some (.beq 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x05#32 29#32 8#32 0x1234#32) = some (.bne 29#32 8#32 0x1234#32) := by decide

-- branch reg-only: rs=29, imm=0x1234 (rt fixed 0)
example : decode (mkIT 0x06#32 29#32 0#32 0x1234#32) = some (.blez 29#32 0x1234#32) := by decide
example : decode (mkIT 0x07#32 29#32 0#32 0x1234#32) = some (.bgtz 29#32 0x1234#32) := by decide

-- Removed in Release 6 (decodes to `none`): "branch likely" family: same field shapes as beq/bne/blez/bgtz, opcodes
-- 0x14..0x17 (MIPS-COVERAGE-GAPS.md \u00a73.3).
example : decode (mkIT 0x14#32 29#32 8#32 0x1234#32) = none := by decide  -- removed in R6 (was `beql`)
example : decode (mkIT 0x15#32 29#32 8#32 0x1234#32) = none := by decide  -- removed in R6 (was `bnel`)
example : decode (mkIT 0x16#32 29#32 0#32 0x1234#32) = none := by decide  -- removed in R6 (was `blezl`)
example : decode (mkIT 0x17#32 29#32 0#32 0x1234#32) = none := by decide  -- removed in R6 (was `bgtzl`)

-- REGIMM zero-comparison branches: opcode 0x01, rs=29, imm=0x1234, rt field
-- selects bltz/bgez (bltzal/bgezal with rs ≠ 0: removed in Release 6, decode to `none`)
example : decode (mkIT 0x01#32 29#32 0x00#32 0x1234#32) = some (.bltz 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x01#32 0x1234#32) = some (.bgez 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x10#32 0x1234#32) = none := by decide  -- removed in R6 (was `bltzal`)
example : decode (mkIT 0x01#32 29#32 0x11#32 0x1234#32) = none := by decide  -- removed in R6 (was `bgezal`)
-- Removed in Release 6 (decodes to `none`): REGIMM branch-likely zero-comparison family: same opcode 0x01, rt field
-- 0x02/0x03/0x12/0x13 selects bltzl/bgezl/bltzall/bgezall.
example : decode (mkIT 0x01#32 29#32 0x02#32 0x1234#32) = none := by decide  -- removed in R6 (was `bltzl`)
example : decode (mkIT 0x01#32 29#32 0x03#32 0x1234#32) = none := by decide  -- removed in R6 (was `bgezl`)
example : decode (mkIT 0x01#32 29#32 0x12#32 0x1234#32) = none := by decide  -- removed in R6 (was `bltzall`)
example : decode (mkIT 0x01#32 29#32 0x13#32 0x1234#32) = none := by decide  -- removed in R6 (was `bgezall`)
-- Removed in Release 6 (decodes to `none`): REGIMM trap-immediate family: same opcode 0x01, `rt` field selects
-- teqi/tnei/tgei/tgeiu/tlti/tltiu (real MIPS32 ISA, MD00086 Rev 2.50 §3.2,
-- Table 3-2 -- see docs/spec/MIPS-COVERAGE-GAPS.md §3.8).
example : decode (mkIT 0x01#32 29#32 0x0c#32 0x1234#32) = none := by decide  -- removed in R6 (was `teqi`)
example : decode (mkIT 0x01#32 29#32 0x0e#32 0x1234#32) = none := by decide  -- removed in R6 (was `tnei`)
example : decode (mkIT 0x01#32 29#32 0x08#32 0x1234#32) = none := by decide  -- removed in R6 (was `tgei`)
example : decode (mkIT 0x01#32 29#32 0x09#32 0x1234#32) = none := by decide  -- removed in R6 (was `tgeiu`)
example : decode (mkIT 0x01#32 29#32 0x0a#32 0x1234#32) = none := by decide  -- removed in R6 (was `tlti`)
example : decode (mkIT 0x01#32 29#32 0x0b#32 0x1234#32) = none := by decide  -- removed in R6 (was `tltiu`)
-- synci: same opcode 0x01, `rt` field fixed 0x1f (real MIPS32 MIPS32r2
-- addition, docs/spec/MIPS-COVERAGE-GAPS.md §3.7), `rs, imm` shape
-- identical to `blez`/`bgtz`.
example : decode (mkIT 0x01#32 29#32 0x1f#32 0x1234#32) = some (.synci 29#32 0x1234#32) := by decide
-- a REGIMM word with an unrecognized rt field (0x1d is reserved in the
-- real MIPS32 REGIMM table -- not one of bltz/bgez/bltzal/bgezal/the trap
-- family/synci above) decodes to none
#guard decode (mkIT 0x01#32 29#32 0x1d#32 0x1234#32) = none

-- J-type: target = 0x3ffffff (all 26 bits)
example : decode ((0x02#32 <<< 26) ||| mkJT 0x3ffffff#32) = some (.j 0x3ffffff#32) := by decide
example : decode ((0x03#32 <<< 26) ||| mkJT 0x3ffffff#32) = some (.jal 0x3ffffff#32) := by decide

-- Coprocessor 1 (FPU): mtc1/mfc1 (fmt=MT/MF, rt=8, fs=3). Unlike plain
-- R-type, COP1 words need opcode 0x11 OR'd in explicitly over `mkRT`'s
-- (always-0) opcode field.
example : decode ((0x11#32 <<< 26) ||| mkRT 0x00#32 8#32 3#32 0#32 0#32) = some (.mfc1 8#32 3#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x04#32 8#32 3#32 0#32 0#32) = some (.mtc1 8#32 3#32) := by decide
-- lwc1/swc1: rs=29 (base), ft=5, imm=0x1234 (identical layout to lw/sw)
example : decode (mkIT 0x31#32 29#32 5#32 0x1234#32) = some (.lwc1 29#32 5#32 0x1234#32) := by decide
example : decode (mkIT 0x39#32 29#32 5#32 0x1234#32) = some (.swc1 29#32 5#32 0x1234#32) := by decide
-- add.s/sub.s/mul.s/div.s: fmt=S, ft=6, fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 8#32 0x00#32) = some (.addS 8#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 8#32 0x01#32) = some (.subS 8#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 8#32 0x02#32) = some (.mulS 8#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 8#32 0x03#32) = some (.divS 8#32 7#32 6#32) := by decide
-- mov.s/cvt.w.s: fmt=S, fs=7, fd=8 (ft-position fixed 0)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x06#32) = some (.movS 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x24#32) = some (.cvtWS 8#32 7#32) := by decide
-- cvt.s.w: fmt=W, fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x14#32 0#32 7#32 8#32 0x20#32) = some (.cvtSW 8#32 7#32) := by decide
-- Removed in Release 6 (decodes to `none`): c.eq.s/c.lt.s/c.le.s: fmt=S, fs=7, ft=6, fd-position (cc) fixed 0
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x32#32) = none := by decide  -- removed in R6 (was `cCondS`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x3c#32) = none := by decide  -- removed in R6 (was `cCondS`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x3e#32) = none := by decide  -- removed in R6 (was `cCondS`)
-- c.eq.s with a nonzero cc field → none (C.cond.fmt is removed in Release 6 in any case)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 1#32 0x32#32) = none := by decide
-- sqrt.s/abs.s/neg.s: fmt=S, fs=7, fd=8 (ft-position fixed 0)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x04#32) = some (.sqrtS 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x05#32) = some (.absS 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x07#32) = some (.negS 8#32 7#32) := by decide
-- round.w.s/trunc.w.s/ceil.w.s/floor.w.s: fmt=S, fs=7, fd=8 (ft-position fixed 0)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x0c#32) = some (.roundWS 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x0d#32) = some (.truncWS 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x0e#32) = some (.ceilWS 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x0f#32) = some (.floorWS 8#32 7#32) := by decide
-- Removed in Release 6 (decodes to `none`): c.f.s/c.un.s/c.ueq.s/c.olt.s/c.ult.s/c.ole.s/c.ule.s: fmt=S, fs=7, ft=6, fd-position (cc) fixed 0
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x30#32) = none := by decide  -- removed in R6 (was `cCondS`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x31#32) = none := by decide  -- removed in R6 (was `cCondS`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x33#32) = none := by decide  -- removed in R6 (was `cCondS`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x34#32) = none := by decide  -- removed in R6 (was `cCondS`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x35#32) = none := by decide  -- removed in R6 (was `cCondS`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x36#32) = none := by decide  -- removed in R6 (was `cCondS`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x37#32) = none := by decide  -- removed in R6 (was `cCondS`)
-- c.un.s with a nonzero cc field → none (C.cond.fmt is removed in Release 6 in any case)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 1#32 0x31#32) = none := by decide

-- ldc1/sdc1: rs=29 (base), ft=5, imm=0x1234 (identical layout to lwc1/swc1)
example : decode (mkIT 0x35#32 29#32 5#32 0x1234#32) = some (.ldc1 29#32 5#32 0x1234#32) := by decide
example : decode (mkIT 0x3d#32 29#32 5#32 0x1234#32) = some (.sdc1 29#32 5#32 0x1234#32) := by decide
-- add.d/sub.d/mul.d/div.d: fmt=D, ft=6, fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 8#32 0x00#32) = some (.addD 8#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 8#32 0x01#32) = some (.subD 8#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 8#32 0x02#32) = some (.mulD 8#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 8#32 0x03#32) = some (.divD 8#32 7#32 6#32) := by decide
-- mov.d/sqrt.d/abs.d/neg.d/cvt.w.d: fmt=D, fs=7, fd=8 (ft-position fixed 0)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x06#32) = some (.movD 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x04#32) = some (.sqrtD 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x05#32) = some (.absD 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x07#32) = some (.negD 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x24#32) = some (.cvtWD 8#32 7#32) := by decide
-- cvt.d.s: fmt=S (source is single), fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x21#32) = some (.cvtDS 8#32 7#32) := by decide
-- cvt.s.d: fmt=D (source is double), fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x20#32) = some (.cvtSD 8#32 7#32) := by decide
-- cvt.d.w: fmt=W (source is a word), fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x14#32 0#32 7#32 8#32 0x21#32) = some (.cvtDW 8#32 7#32) := by decide
-- Removed in Release 6 (decodes to `none`): c.eq.d/c.lt.d/c.le.d/c.f.d/c.un.d/c.ueq.d/c.olt.d/c.ult.d/c.ole.d/c.ule.d:
-- fmt=D, fs=7, ft=6, fd-position (cc) fixed 0
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x32#32) = none := by decide  -- removed in R6 (was `cCondD`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x3c#32) = none := by decide  -- removed in R6 (was `cCondD`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x3e#32) = none := by decide  -- removed in R6 (was `cCondD`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x30#32) = none := by decide  -- removed in R6 (was `cCondD`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x31#32) = none := by decide  -- removed in R6 (was `cCondD`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x33#32) = none := by decide  -- removed in R6 (was `cCondD`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x34#32) = none := by decide  -- removed in R6 (was `cCondD`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x35#32) = none := by decide  -- removed in R6 (was `cCondD`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x36#32) = none := by decide  -- removed in R6 (was `cCondD`)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x37#32) = none := by decide  -- removed in R6 (was `cCondD`)
-- c.eq.d with a nonzero cc field → none (C.cond.fmt is removed in Release 6 in any case)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 1#32 0x32#32) = none := by decide

-- cfc1/mfc1 share the same (rt, fs) field shape, distinguished by the
-- rs-position sub-opcode (CF=0x02 vs MF=0x00); ctc1/mtc1 likewise (CT=0x06 vs MT=0x04)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x02#32 8#32 3#32 0#32 0#32) = some (.cfc1 8#32 3#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x06#32 8#32 3#32 0#32 0#32) = some (.ctc1 8#32 3#32) := by decide
-- Removed in Release 6 (decodes to `none`): bc1t/bc1f: fmt=BC1, tf=1/0, offset=0x1234
example : decode (mkIT 0x11#32 0x08#32 1#32 0x1234#32) = none := by decide  -- removed in R6 (was `bc1t`)
example : decode (mkIT 0x11#32 0x08#32 0#32 0x1234#32) = none := by decide  -- removed in R6 (was `bc1f`)
-- Removed in Release 6 (decodes to `none`): BC1 with nd = 1 (rt-field bit 1) is the branch-likely form; bits 20..18 are cc
example : decode (mkIT 0x11#32 0x08#32 2#32 0x1234#32) = none := by decide  -- removed in R6 (was `bc1fl`)
example : decode (mkIT 0x11#32 0x08#32 3#32 0x1234#32) = none := by decide  -- removed in R6 (was `bc1tl`)
example : decode (mkIT 0x11#32 0x08#32 0x1d#32 0x1234#32) = none := by decide  -- removed in R6 (was `bc1t`)

-- `encode ∘ decode` round-trips, spanning R / I / J / branch / syscall
example : encode (.add 29#32 8#32 3#32) = mkRT 29#32 8#32 3#32 0#32 0x20#32 := by decide
example : encode (.lw 29#32 8#32 0x1234#32) = mkIT 0x23#32 29#32 8#32 0x1234#32 := by decide
example : encode (.beq 29#32 8#32 0x1234#32) = mkIT 0x04#32 29#32 8#32 0x1234#32 := by decide
example : encode (.j 0x3ffffff#32) = (0x02#32 <<< 26) ||| mkJT 0x3ffffff#32 := by decide
example : encode (.syscall 0#32) = mkRT 0#32 0#32 0#32 0#32 0x0c#32 := by decide
example : encode (.sll 3#32 8#32 5#32) = mkRT 0#32 8#32 3#32 5#32 0x00#32 := by decide
example : encode (.clo 29#32 3#32) = mkRT 29#32 0#32 3#32 1#32 0x11#32 := by decide
example : encode (.clz 29#32 3#32) = mkRT 29#32 0#32 3#32 1#32 0x10#32 := by decide
example : encode (.seb 3#32 8#32) = (0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x10#32 0x20#32 := by decide
example : encode (.wsbh 3#32 8#32) = (0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x02#32 0x20#32 := by decide
example : encode (.rotr 3#32 8#32 5#32) = mkRT 0x01#32 8#32 3#32 5#32 0x02#32 := by decide
example : encode (.rotrv 3#32 8#32 29#32) = mkRT 29#32 8#32 3#32 0x01#32 0x06#32 := by decide
example : encode (.ext 8#32 29#32 6#32 10#32) = (0x1f#32 <<< 26) ||| mkRT 29#32 8#32 9#32 6#32 0x00#32 := by decide
example : encode (.ins 8#32 29#32 6#32 10#32) = (0x1f#32 <<< 26) ||| mkRT 29#32 8#32 15#32 6#32 0x04#32 := by decide
example : encode (.sllv 3#32 8#32 29#32) = mkRT 29#32 8#32 3#32 0#32 0x04#32 := by decide
example : encode (.jalr 29#32 3#32) = mkRT 29#32 0#32 3#32 0#32 0x09#32 := by decide
example : encode (.jalrHb 29#32 3#32) = mkRT 29#32 0#32 3#32 0x10#32 0x09#32 := by decide
-- full round trip for every new instruction (decode ∘ encode = id on the field values we store)
example : decode (encode (.clo 29#32 3#32)) = some (.clo 29#32 3#32) := by decide
example : decode (encode (.clz 29#32 3#32)) = some (.clz 29#32 3#32) := by decide
example : decode (encode (.seb 3#32 8#32)) = some (.seb 3#32 8#32) := by decide
example : decode (encode (.seh 3#32 8#32)) = some (.seh 3#32 8#32) := by decide
example : decode (encode (.wsbh 3#32 8#32)) = some (.wsbh 3#32 8#32) := by decide
example : decode (encode (.rotr 3#32 8#32 5#32)) = some (.rotr 3#32 8#32 5#32) := by decide
example : decode (encode (.rotrv 3#32 8#32 29#32)) = some (.rotrv 3#32 8#32 29#32) := by decide
example : decode (encode (.ext 8#32 29#32 6#32 10#32)) = some (.ext 8#32 29#32 6#32 10#32) := by decide
example : decode (encode (.ins 8#32 29#32 6#32 10#32)) = some (.ins 8#32 29#32 6#32 10#32) := by decide
-- ext/ins round-trip edge cases: pos=0 (size=32, the full word) and
-- pos+size=32 (touches the top bit) -- both satisfy the real `pos+size<=32`
-- constraint so the `rd`-position field packs/unpacks without truncation.
example : decode (encode (.ext 8#32 29#32 0#32 32#32)) = some (.ext 8#32 29#32 0#32 32#32) := by decide
example : decode (encode (.ins 8#32 29#32 20#32 12#32)) = some (.ins 8#32 29#32 20#32 12#32) := by decide
example : decode (encode (.sllv 3#32 8#32 29#32)) = some (.sllv 3#32 8#32 29#32) := by decide
example : decode (encode (.srlv 3#32 8#32 29#32)) = some (.srlv 3#32 8#32 29#32) := by decide
example : decode (encode (.srav 3#32 8#32 29#32)) = some (.srav 3#32 8#32 29#32) := by decide
example : decode (encode (.jalr 29#32 3#32)) = some (.jalr 29#32 3#32) := by decide
example : decode (encode (.jalrHb 29#32 3#32)) = some (.jalrHb 29#32 3#32) := by decide
example : encode (.break 0#32) = mkRT 0#32 0#32 0#32 0#32 0x0d#32 := by decide
example : encode (.teq 29#32 8#32 0#32) = mkRT 29#32 8#32 0#32 0#32 0x34#32 := by decide

-- `decode (encode ...)` round-trips for every new trap/break instruction
example : decode (encode (.teq 29#32 8#32 0#32)) = some (.teq 29#32 8#32 0#32) := by decide
example : decode (encode (.tne 29#32 8#32 0#32)) = some (.tne 29#32 8#32 0#32) := by decide
example : decode (encode (.tlt 29#32 8#32 0#32)) = some (.tlt 29#32 8#32 0#32) := by decide
example : decode (encode (.tge 29#32 8#32 0#32)) = some (.tge 29#32 8#32 0#32) := by decide
example : decode (encode (.tltu 29#32 8#32 0#32)) = some (.tltu 29#32 8#32 0#32) := by decide
example : decode (encode (.tgeu 29#32 8#32 0#32)) = some (.tgeu 29#32 8#32 0#32) := by decide
example : decode (encode (.break 0#32)) = some (.break 0#32) := by decide

-- sync/synci: encode matches the hand-computed word, and decode (encode i) = some i
example : encode (.sync 0#32) = mkRT 0#32 0#32 0#32 0#32 0x0f#32 := by decide
example : encode (.synci 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x1f#32 0x1234#32 := by decide
example : decode (encode (.sync 0#32)) = some (.sync 0#32) := by decide
example : decode (encode (.synci 29#32 0x1234#32)) = some (.synci 29#32 0x1234#32) := by decide

-- Coprocessor 1 (FPU): full `decode (encode i) = some i` round-trips
example : decode (encode (.mfc1 8#32 3#32)) = some (.mfc1 8#32 3#32) := by decide
example : decode (encode (.mtc1 8#32 3#32)) = some (.mtc1 8#32 3#32) := by decide
example : decode (encode (.lwc1 29#32 5#32 0x1234#32)) = some (.lwc1 29#32 5#32 0x1234#32) := by decide
example : decode (encode (.swc1 29#32 5#32 0x1234#32)) = some (.swc1 29#32 5#32 0x1234#32) := by decide
example : decode (encode (.addS 8#32 7#32 6#32)) = some (.addS 8#32 7#32 6#32) := by decide
example : decode (encode (.subS 8#32 7#32 6#32)) = some (.subS 8#32 7#32 6#32) := by decide
example : decode (encode (.mulS 8#32 7#32 6#32)) = some (.mulS 8#32 7#32 6#32) := by decide
example : decode (encode (.divS 8#32 7#32 6#32)) = some (.divS 8#32 7#32 6#32) := by decide
example : decode (encode (.movS 8#32 7#32)) = some (.movS 8#32 7#32) := by decide
example : decode (encode (.cvtSW 8#32 7#32)) = some (.cvtSW 8#32 7#32) := by decide
example : decode (encode (.cvtWS 8#32 7#32)) = some (.cvtWS 8#32 7#32) := by decide
example : decode (encode (.sqrtS 8#32 7#32)) = some (.sqrtS 8#32 7#32) := by decide
example : decode (encode (.absS 8#32 7#32)) = some (.absS 8#32 7#32) := by decide
example : decode (encode (.negS 8#32 7#32)) = some (.negS 8#32 7#32) := by decide
example : decode (encode (.roundWS 8#32 7#32)) = some (.roundWS 8#32 7#32) := by decide
example : decode (encode (.truncWS 8#32 7#32)) = some (.truncWS 8#32 7#32) := by decide
example : decode (encode (.ceilWS 8#32 7#32)) = some (.ceilWS 8#32 7#32) := by decide
example : decode (encode (.floorWS 8#32 7#32)) = some (.floorWS 8#32 7#32) := by decide
example : decode (encode (.cfc1 8#32 3#32)) = some (.cfc1 8#32 3#32) := by decide
example : decode (encode (.ctc1 8#32 3#32)) = some (.ctc1 8#32 3#32) := by decide

-- Coprocessor 1 (FPU), double-precision: full `decode (encode i) = some i` round-trips
example : decode (encode (.ldc1 29#32 5#32 0x1234#32)) = some (.ldc1 29#32 5#32 0x1234#32) := by decide
example : decode (encode (.sdc1 29#32 5#32 0x1234#32)) = some (.sdc1 29#32 5#32 0x1234#32) := by decide
example : decode (encode (.addD 8#32 7#32 6#32)) = some (.addD 8#32 7#32 6#32) := by decide
example : decode (encode (.subD 8#32 7#32 6#32)) = some (.subD 8#32 7#32 6#32) := by decide
example : decode (encode (.mulD 8#32 7#32 6#32)) = some (.mulD 8#32 7#32 6#32) := by decide
example : decode (encode (.divD 8#32 7#32 6#32)) = some (.divD 8#32 7#32 6#32) := by decide
example : decode (encode (.movD 8#32 7#32)) = some (.movD 8#32 7#32) := by decide
example : decode (encode (.cvtDS 8#32 7#32)) = some (.cvtDS 8#32 7#32) := by decide
example : decode (encode (.cvtSD 8#32 7#32)) = some (.cvtSD 8#32 7#32) := by decide
example : decode (encode (.cvtDW 8#32 7#32)) = some (.cvtDW 8#32 7#32) := by decide
example : decode (encode (.cvtWD 8#32 7#32)) = some (.cvtWD 8#32 7#32) := by decide
example : decode (encode (.sqrtD 8#32 7#32)) = some (.sqrtD 8#32 7#32) := by decide
example : decode (encode (.absD 8#32 7#32)) = some (.absD 8#32 7#32) := by decide
example : decode (encode (.negD 8#32 7#32)) = some (.negD 8#32 7#32) := by decide

-- REGIMM zero-comparison branches: full decode(encode i) = some i round-trips
example : decode (encode (.bltz 29#32 0x1234#32)) = some (.bltz 29#32 0x1234#32) := by decide
example : decode (encode (.bgez 29#32 0x1234#32)) = some (.bgez 29#32 0x1234#32) := by decide
-- ll/sc: encode matches the hand-computed word, and decode (encode i) = some i
example : encode (.ll 29#32 8#32 0x123#32) = 0x7fa891b6#32 := by decide
example : encode (.sc 29#32 8#32 0x123#32) = 0x7fa891a6#32 := by decide
example : encode (.ll 3#32 2#32 8#32) = 0x7c620436#32 := by decide
example : decode (encode (.ll 29#32 8#32 0x1ff#32)) = some (.ll 29#32 8#32 0x1ff#32) := by decide
example : decode (encode (.sc 29#32 8#32 0x100#32)) = some (.sc 29#32 8#32 0x100#32) := by decide

-- unknown opcodes → none
#guard decode (mkIT 0x3a#32 0#32 0#32 0#32) = none  -- opcode 0x3a (W3: Release 6 BALC, BALC p.52; not decoded yet)
-- opcode 0x11 (COP1) is implemented for the fmt/funct combinations below;
-- an unrecognized fmt (not MF/MT/BC1/S/W) still decodes to `none`.
#guard decode (mkIT 0x11#32 0x1f#32 0#32 0#32) = none
-- opcodes 0x16/0x17 (pre-Release 6 blezl/bgtzl) and 0x12/0x13 (COP2, COP1X) do not decode
-- (W3: Release 6 reuses 0x16/0x17 for the compact branches, B<cond>C p.82).
#guard decode (mkIT 0x12#32 0#32 0#32 0#32) = none
-- Removed in Release 6 (decodes to `none`): opcode 0x13 (COP1X): funct 0x05 `luxc1` / 0x0d `suxc1` (UNPREDICTABLE with
-- FR = 0) and the paired-single functs are not modeled
#guard decode (mkIT 0x13#32 0#32 0#32 0x05#32) = none
#guard decode (mkIT 0x13#32 0#32 0#32 0x0d#32) = none
#guard decode (mkIT 0x13#32 0#32 0#32 0x26#32) = none
-- opcode 0x1c (SPECIAL2) is removed in Release 6: no funct decodes.
#guard decode (mkIT 0x1c#32 0#32 0#32 0x3f#32) = none
#guard decode (mkIT 0x1d#32 0#32 0#32 0#32) = none

-- unknown functs under opcode 0 → none
-- Removed in Release 6 (decodes to `none`): funct 0x01 is `MOVCI` (movf/movt); bit 17 or bits 10..6 nonzero → none
#guard decode (mkRT 0#32 0#32 0#32 0#32 0x01#32) = none  -- removed in R6 (was `movf`)
#guard decode (mkRT 0#32 2#32 0#32 0#32 0x01#32) = none
#guard decode (mkRT 0#32 0#32 0#32 1#32 0x01#32) = none
#guard decode (mkRT 0#32 0#32 0#32 0#32 0x3f#32) = none

-- a few key decodes
#guard decode (mkRT 29#32 8#32 3#32 0#32 0x20#32) = some (.add 29#32 8#32 3#32)
#guard decode (mkIT 0x23#32 29#32 8#32 0x1234#32) = some (.lw 29#32 8#32 0x1234#32)
#guard decode ((0x02#32 <<< 26) ||| mkJT 0x3ffffff#32) = some (.j 0x3ffffff#32)
#guard decode (mkRT 0#32 0#32 0#32 0#32 0x0c#32) = some (.syscall 0#32)
#guard decode (mkRT 29#32 8#32 0#32 0#32 0x34#32) = some (.teq 29#32 8#32 0#32)
#guard decode (mkRT 0#32 0#32 0#32 0#32 0x0d#32) = some (.break 0#32)

-- funct 0x35 sits between teq (0x34) and tne (0x36) and is reserved/unused
-- in the real MIPS32 trap family; no mnemonic maps to it.
#guard decode (mkRT 0#32 0#32 0#32 0#32 0x35#32) = none
#guard decode (encode (.addS 8#32 7#32 6#32)) = some (.addS 8#32 7#32 6#32)
#guard decode (encode (.addD 8#32 7#32 6#32)) = some (.addD 8#32 7#32 6#32)
#guard decode (encode (.ldc1 29#32 5#32 0x1234#32)) = some (.ldc1 29#32 5#32 0x1234#32)

-- Coprocessor 0 (CP0) register move / execution control: mfc0/mtc0/eret/wait
-- (docs/spec/MIPS-COVERAGE-GAPS.md §3.10A). rt=8 (GPR), rd=13 (Cause).
example : decode ((0x10#32 <<< 26) ||| mkRT 0x00#32 8#32 13#32 0#32 0#32) = some (.mfc0 8#32 13#32 0#32) := by decide
example : decode ((0x10#32 <<< 26) ||| mkRT 0x04#32 8#32 13#32 0#32 0#32) = some (.mtc0 8#32 13#32 0#32) := by decide
example : decode ((0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x18#32) = some .eret := by decide
example : decode ((0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x20#32) = some (.wait 0#32) := by decide

-- encode produces the exact hand-computed words above.
example : encode (.mfc0 8#32 13#32 0#32) = (0x10#32 <<< 26) ||| mkRT 0x00#32 8#32 13#32 0#32 0#32 := by decide
example : encode (.mtc0 8#32 13#32 0#32) = (0x10#32 <<< 26) ||| mkRT 0x04#32 8#32 13#32 0#32 0#32 := by decide
example : encode .eret = (0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x18#32 := by decide
example : encode (.wait 0#32) = (0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x20#32 := by decide

-- full decode ∘ encode round trips for Status/Cause/EPC (BadVAddr/ErrorEPC are below).
example : decode (encode (.mfc0 8#32 12#32 0#32)) = some (.mfc0 8#32 12#32 0#32) := by decide
example : decode (encode (.mfc0 8#32 13#32 0#32)) = some (.mfc0 8#32 13#32 0#32) := by decide
example : decode (encode (.mfc0 8#32 14#32 0#32)) = some (.mfc0 8#32 14#32 0#32) := by decide
example : decode (encode (.mtc0 8#32 12#32 0#32)) = some (.mtc0 8#32 12#32 0#32) := by decide
example : decode (encode (.mtc0 8#32 13#32 0#32)) = some (.mtc0 8#32 13#32 0#32) := by decide
example : decode (encode (.mtc0 8#32 14#32 0#32)) = some (.mtc0 8#32 14#32 0#32) := by decide
example : decode (encode .eret) = some .eret := by decide
example : decode (encode (.wait 0#32)) = some (.wait 0#32) := by decide

-- an unrecognized COP0 `rs`-field (not MF/MT/CO) decodes to `none`.
#guard decode (mkIT 0x10#32 0x08#32 0#32 0#32) = none
-- a CO-sub-format word with an unrecognized `funct` (not eret's 0x18 or
-- wait's 0x20) decodes to `none`.
#guard decode ((0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x01#32) = none

-- ## Strict decoding (reserved fields must be zero) and `sb`

-- `sb`: opcode 0x28.
example : decode (mkIT 0x28#32 29#32 8#32 0x1234#32) = some (.sb 29#32 8#32 0x1234#32) := by decide
example : decode (encode (.sb 29#32 8#32 0xffff#32)) = some (.sb 29#32 8#32 0xffff#32) := by decide
example : decode 0xa1090003#32 = some (.sb 8#32 9#32 3#32) := by decide  -- sb $t1, 3($t0)

-- Nonzero must-be-zero fields do not decode.
example : decode (mkRT 29#32 8#32 3#32 1#32 0x20#32) = none := by decide      -- add, shamt ≠ 0
example : decode (mkRT 29#32 8#32 3#32 0#32 0x18#32) = none := by decide      -- mult, rd ≠ 0
example : decode (mkRT 1#32 0#32 3#32 0#32 0x10#32) = none := by decide       -- mfhi, rs ≠ 0
example : decode (mkRT 0#32 1#32 3#32 0#32 0x10#32) = none := by decide       -- mfhi, rt ≠ 0
example : decode (mkIT 0x0f#32 1#32 8#32 0x1234#32) = some (.aui 1#32 8#32 0x1234#32) := by decide  -- aui, rs ≠ 0
example : decode (mkIT 0x06#32 29#32 1#32 0x1234#32) = none := by decide      -- blez, rt ≠ 0
example : decode (mkIT 0x07#32 29#32 1#32 0x1234#32) = none := by decide      -- bgtz, rt ≠ 0
example : decode (mkIT 0x16#32 29#32 1#32 0x1234#32) = none := by decide      -- blezl, rt ≠ 0
example : decode (mkIT 0x17#32 29#32 1#32 0x1234#32) = none := by decide      -- bgtzl, rt ≠ 0
example : decode (mkRT 29#32 1#32 0#32 0#32 0x08#32) = none := by decide      -- jr, rt ≠ 0
example : decode (mkRT 29#32 0#32 1#32 0#32 0x08#32) = none := by decide      -- jr, rd ≠ 0
example : decode ((0x1f#32 <<< 26) ||| mkRT 1#32 8#32 3#32 0x10#32 0x20#32) = none := by decide  -- seb, rs ≠ 0
example : decode ((0x1f#32 <<< 26) ||| mkRT 1#32 8#32 3#32 0x18#32 0x20#32) = none := by decide  -- seh, rs ≠ 0
example : decode ((0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 1#32 0x18#32) = none := by decide  -- eret, CO bits ≠ 0
example : decode ((0x10#32 <<< 26) ||| mkRT 0x11#32 0#32 0#32 0#32 0x18#32) = none := by decide  -- eret, CO bits ≠ 0
-- `srl`/`rotr` are selected by bit 21 alone, with bits 25..22 zero; likewise
-- `srlv`/`rotrv` by bit 6 with bits 10..7 zero.
example : decode (mkRT 2#32 8#32 3#32 5#32 0x02#32) = none := by decide
example : decode (mkRT 3#32 8#32 3#32 5#32 0x02#32) = none := by decide
example : decode (mkRT 29#32 8#32 3#32 2#32 0x06#32) = none := by decide
example : decode (mkRT 29#32 8#32 3#32 3#32 0x06#32) = none := by decide
-- `mfc0`/`mtc0`: an unmodeled `(rd, sel)` (e.g. `mfc0 $t0,$12,3` = SRSMap, UNPREDICTABLE with
-- `SRSCtl.HSS = 0`), nonzero bits 10..3, or an unmodeled register do not decode.
example : decode 0x40086003#32 = none := by decide                              -- mfc0 $t0,$12,3
example : decode 0x40886003#32 = none := by decide                              -- mtc0 $t0,$12,3
-- IntCtl (12,1) and SRSCtl (12,2) are modeled since wave 6 (F13, F16).
example : decode 0x40086001#32 = some (.mfc0 8#32 12#32 1#32) := by decide        -- mfc0 $t0,$12,1
example : decode 0x40886002#32 = some (.mtc0 8#32 12#32 2#32) := by decide        -- mtc0 $t0,$12,2
-- `rdpgpr $t0, $t1` / `wrpgpr $t0, $t1` (MD00086 Vol II-A Rev 6.06, RDPGPR p.335, WRPGPR p.444).
example : decode 0x41494000#32 = some (.rdpgpr 8#32 9#32) := by decide
example : decode 0x41c94000#32 = some (.wrpgpr 8#32 9#32) := by decide
example : encode (.rdpgpr 8#32 9#32) = 0x41494000#32 := by decide
example : encode (.wrpgpr 8#32 9#32) = 0x41c94000#32 := by decide
example : decode 0x41494001#32 = none := by decide                              -- bits 10..0 ≠ 0
example : decode 0x41c94040#32 = none := by decide                              -- bits 10..0 ≠ 0
example : decode 0x40086008#32 = none := by decide                              -- bit 3 set
example : decode ((0x10#32 <<< 26) ||| mkRT 0#32 8#32 1#32 0#32 0#32) = none := by decide  -- Random (1)
example : decode ((0x10#32 <<< 26) ||| mkRT 0#32 8#32 10#32 0#32 0#32) = none := by decide  -- EntryHi (10)
-- Count (9,0), Compare (11,0) and HWREna (7,0) are modeled since wave 5 (F12, F15).
example : decode ((0x10#32 <<< 26) ||| mkRT 0#32 8#32 9#32 0#32 0#32) = some (.mfc0 8#32 9#32 0#32) := by decide  -- Count
example : decode (encode (.mtc0 8#32 11#32 0#32)) = some (.mtc0 8#32 11#32 0#32) := by decide   -- Compare
example : decode (encode (.mtc0 8#32 7#32 0#32)) = some (.mtc0 8#32 7#32 0#32) := by decide     -- HWREna
example : decode (encode (.mfc0 8#32 7#32 0#32)) = some (.mfc0 8#32 7#32 0#32) := by decide     -- HWREna
-- `rdhwr` (SPECIAL3 funct 0x3b): `rdhwr $3, $29` is 0x7c03e83b (MD00086 Vol II-A Rev 6.06, RDHWR,
-- p.332); Release 6 adds `sel` in bits 8..6; `rs` and bits 10..9 must be zero.
example : encode (.rdhwr 3#32 29#32 0#32) = 0x7c03e83b#32 := by decide
example : decode 0x7c03e83b#32 = some (.rdhwr 3#32 29#32 0#32) := by decide
example : decode (encode (.rdhwr 8#32 2#32 0#32)) = some (.rdhwr 8#32 2#32 0#32) := by decide
example : decode (encode (.rdhwr 8#32 2#32 7#32)) = some (.rdhwr 8#32 2#32 7#32) := by decide
example : decode 0x7c03e87b#32 = some (.rdhwr 3#32 29#32 1#32) := by decide   -- sel = 1
example : decode 0x7c03ea3b#32 = none := by decide   -- bit 9 = 1
example : decode 0x7c23e83b#32 = none := by decide   -- rs = 1
example : decode (encode (.mfc0 8#32 8#32 0#32)) = some (.mfc0 8#32 8#32 0#32) := by decide     -- BadVAddr
example : decode (encode (.mfc0 8#32 30#32 0#32)) = some (.mfc0 8#32 30#32 0#32) := by decide   -- ErrorEPC
-- COP1 moves: bits 10..0 must be zero; unary ops: `ft` must be zero.
example : decode ((0x11#32 <<< 26) ||| mkRT 0x00#32 8#32 3#32 0#32 1#32) = none := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x04#32 8#32 3#32 1#32 0#32) = none := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x02#32 8#32 3#32 0#32 1#32) = none := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x06#32 8#32 3#32 0#32 1#32) = none := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 1#32 7#32 8#32 0x06#32) = none := by decide  -- mov.s, ft ≠ 0
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 1#32 7#32 8#32 0x04#32) = none := by decide  -- sqrt.d, ft ≠ 0
-- UNPREDICTABLE `ext`/`ins` field combinations do not decode.
example : decode ((0x1f#32 <<< 26) ||| mkRT 29#32 8#32 31#32 1#32 0x00#32) = none := by decide   -- ext lsb+msbd = 32
example : decode ((0x1f#32 <<< 26) ||| mkRT 29#32 8#32 3#32 6#32 0x04#32) = none := by decide    -- ins msb < lsb

-- Software `code` fields carried in the constructors, and the jr/jalr hint values (see `decode`'s docstring).
example : decode 0x42000020#32 = some (.wait 0#32) := by decide                                          -- wait, code 0
example : decode 0x43ffffe0#32 = some (.wait 0x7ffff#32) := by decide                                          -- wait, code all ones
example : decode 0x40000020#32 = none := by decide                                                -- CO bit clear
example : decode (mkRT 0#32 0#32 0#32 0x1f#32 0x0f#32) = some (.sync 0x1f#32) := by decide                 -- sync stype
example : decode (mkRT 0x1f#32 0x1f#32 0x1f#32 0x1f#32 0x0c#32) = some (.syscall 0xfffff#32) := by decide     -- syscall code
example : decode (mkRT 0x1f#32 0x1f#32 0x1f#32 0x1f#32 0x0d#32) = some (.break 0xfffff#32) := by decide       -- break code
example : decode (mkRT 29#32 8#32 0x1f#32 0x1f#32 0x34#32) = some (.teq 29#32 8#32 0x3ff#32) := by decide -- trap code
example : decode (mkRT 29#32 0#32 0#32 0x10#32 0x08#32) = none := by decide  -- removed in R6 (was `jrHb`)
example : decode (mkRT 29#32 0#32 31#32 0x10#32 0x09#32) = some (.jalrHb 29#32 31#32) := by decide -- jalr.hb
example : decode (mkRT 29#32 0#32 0#32 0x11#32 0x08#32) = none := by decide                   -- jr, hint 17
example : decode (mkRT 29#32 0#32 31#32 0x01#32 0x09#32) = none := by decide                  -- jalr, hint 1
-- `nop` / `ssnop` / `ehb` are `sll $0,$0,{0,1,3}`.
example : decode 0x00000000#32 = some (.sll 0#32 0#32 0#32) := by decide
example : decode 0x00000040#32 = some (.sll 0#32 0#32 1#32) := by decide
example : decode 0x000000c0#32 = some (.sll 0#32 0#32 3#32) := by decide

-- ## Tests: FCSR-era additions (cc fields, signaling compares, new instructions)

-- `C.cond.fmt` is removed in Release 6 (W6 adds CMP.cond.fmt): its words decode to `none`
example : decode 0x46062832#32 = none := by decide  -- removed in R6 (was `cCondS`)
example : decode 0x46262f3a#32 = none := by decide  -- removed in R6 (was `cCondD`)
-- bits 7..6 of a compare must be zero
example : decode 0x46062872#32 = none := by decide
example : decode 0x460628b2#32 = none := by decide

-- words hand-assembled from the field layouts on the manual pages (the conditional moves and the
-- COP1X instructions are removed in Release 6)
example : decode 0x0085100a#32 = none := by decide  -- removed in R6 (was `movz`)
example : decode 0x00801001#32 = none := by decide  -- removed in R6 (was `movf`)
example : decode 0x009d1001#32 = none := by decide  -- removed in R6 (was `movt`)
example : decode 0x46002091#32 = none := by decide  -- removed in R6 (was `movfS`)
example : decode 0x463d2091#32 = none := by decide  -- removed in R6 (was `movtD`)
example : decode 0x46052093#32 = none := by decide  -- removed in R6 (was `movnS`)
example : decode 0x46252092#32 = none := by decide  -- removed in R6 (was `movzD`)
example : decode 0x44682000#32 = some (.mfhc1 8#32 4#32) := by decide              -- mfhc1 $8,$f4
example : decode 0x44e82000#32 = some (.mthc1 8#32 4#32) := by decide              -- mthc1 $8,$f4
example : decode 0x4c850080#32 = none := by decide  -- removed in R6 (was `lwxc1`)
example : decode 0x4c850081#32 = none := by decide  -- removed in R6 (was `ldxc1`)
example : decode 0x4c851008#32 = none := by decide  -- removed in R6 (was `swxc1`)
example : decode 0x4c851009#32 = none := by decide  -- removed in R6 (was `sdxc1`)
example : decode 0x4c85080f#32 = none := by decide  -- removed in R6 (was `prefx`)
example : decode 0x4c8628a0#32 = none := by decide  -- removed in R6 (was `maddS`)
example : decode 0x4c8628a9#32 = none := by decide  -- removed in R6 (was `msubD`)
example : decode 0x4c8628b0#32 = none := by decide  -- removed in R6 (was `nmaddS`)
example : decode 0x4c8628b9#32 = none := by decide  -- removed in R6 (was `nmsubD`)
example : decode 0x46002095#32 = some (.recipS 2#32 4#32) := by decide             -- recip.s $f2,$f4
example : decode 0x46202096#32 = some (.rsqrtD 2#32 4#32) := by decide             -- rsqrt.d $f2,$f4
example : decode 0x4620208c#32 = some (.roundWD 2#32 4#32) := by decide            -- round.w.d
example : decode 0x4620208d#32 = some (.truncWD 2#32 4#32) := by decide
example : decode 0x4620208e#32 = some (.ceilWD 2#32 4#32) := by decide
example : decode 0x4620208f#32 = some (.floorWD 2#32 4#32) := by decide
example : decode 0x7c810835#32 = some (.pref 4#32 1#32 16#32) := by decide         -- pref 1,16($4)
example : encode (.pref 4#32 1#32 16#32) = 0x7c810835#32 := by decide
example : decode 0xcc810010#32 = none := by decide                                 -- pre-R6 PREF (0x33)
example : decode 0x41606000#32 = some (.di 0#32) := by decide                      -- di
example : decode 0x41686020#32 = some (.ei 8#32) := by decide                      -- ei $8
example : decode 0x41686800#32 = none := by decide                                 -- MFMC0, rd ≠ 12
example : decode 0x40087801#32 = some (.mfc0 8#32 15#32 1#32) := by decide         -- mfc0 $8,$15,1 (EBase)
example : decode 0x40888001#32 = some (.mtc0 8#32 16#32 1#32) := by decide         -- mtc0 $8,$16,1 (Config1)
example : decode 0x40087800#32 = some (.mfc0 8#32 15#32 0#32) := by decide         -- PRId
example : decode 0x40088002#32 = some (.mfc0 8#32 16#32 2#32) := by decide         -- mfc0 $8,$16,2 (Config2)
example : decode 0x40888003#32 = some (.mtc0 8#32 16#32 3#32) := by decide         -- mtc0 $8,$16,3 (Config3)
example : decode 0x40088004#32 = none := by decide                                 -- Config4: not implemented
example : decode 0x40087002#32 = none := by decide                                 -- (14,2): not modeled
example : decode 0x0000000c#32 = some (.syscall 0#32) := by decide
example : decode 0x0001234d#32 = some (.break 0x48d#32) := by decide               -- code 0x48d = 1165
example : decode 0x00a41df4#32 = some (.teq 5#32 4#32 0x77#32) := by decide        -- teq $5,$4,0x77
-- round trips of the new shapes (every field at a non-trivial value)
example : decode (encode (.syscall 0xabcde#32)) = some (.syscall 0xabcde#32) := by decide
example : decode (encode (.break 0xfffff#32)) = some (.break 0xfffff#32) := by decide
example : decode (encode (.tgeu 29#32 8#32 0x2aa#32)) = some (.tgeu 29#32 8#32 0x2aa#32) := by decide
example : decode (encode (.sync 0x1f#32)) = some (.sync 0x1f#32) := by decide
example : decode (encode (.wait 0x55555#32)) = some (.wait 0x55555#32) := by decide
example : decode (encode (.pref 29#32 30#32 0x101#32)) = some (.pref 29#32 30#32 0x101#32) := by decide
example : decode (encode (.di 9#32)) = some (.di 9#32) := by decide
example : decode (encode (.ei 9#32)) = some (.ei 9#32) := by decide
example : decode (encode (.mfc0 9#32 16#32 1#32)) = some (.mfc0 9#32 16#32 1#32) := by decide
example : decode (encode (.mfhc1 8#32 4#32)) = some (.mfhc1 8#32 4#32) := by decide
example : decode (encode (.mthc1 8#32 4#32)) = some (.mthc1 8#32 4#32) := by decide
example : decode (encode (.recipD 2#32 4#32)) = some (.recipD 2#32 4#32) := by decide
example : decode (encode (.rsqrtS 2#32 4#32)) = some (.rsqrtS 2#32 4#32) := by decide
example : decode (encode (.floorWD 2#32 4#32)) = some (.floorWD 2#32 4#32) := by decide
-- L-format conversions (fmt = L = 0x15, and cvt.l/round.l… functs) are not modeled
example : decode 0x46a02020#32 = none := by decide                                 -- cvt.s.l
example : decode 0x46002025#32 = none := by decide                                 -- cvt.l.s
example : decode 0x46002008#32 = none := by decide                                 -- round.l.s
-- paired-single (fmt = PS = 0x16) is not modeled
example : decode 0x46c62000#32 = none := by decide                                 -- add.ps

/-! ## Release 6 encodings

The retained, renamed and new constructors with Release 6 words (MD00086 Vol II-A Rev 6.06), a
`decode (encode i) = some i` round trip for every constructor not covered above, and one guard per
removed opcode group not covered above (removed encodings decode to `none`). -/

-- `jr $5` is `jalr $0, $5` = 0x00a00009 (JR p.207: "JR is defined to be JALR with the destination
-- register specifier rd set to 0"); `jr.hb $5` is `jalr.hb $0, $5`.
example : decode 0x00a00009#32 = some (.jalr 5#32 0#32) := by decide
example : encode (.jalr 5#32 0#32) = 0x00a00009#32 := by decide
example : decode 0x00a00409#32 = some (.jalrHb 5#32 0#32) := by decide
-- the pre-Release 6 JR encoding (funct 0x08) is removed
example : decode 0x00a00008#32 = none := by decide
example : decode 0x00a00408#32 = none := by decide
-- PAUSE = `sll $0, $0, 5` = 0x00000140 (PAUSE p.317); it is not an `sll`
example : decode 0x00000140#32 = some .pause := by decide
example : encode .pause = 0x00000140#32 := by decide
example : decode (mkRT 0#32 0#32 0#32 5#32 0x00#32) = some .pause := by decide
example : decode (mkRT 0#32 0#32 0#32 3#32 0x00#32) = some (.sll 0#32 0#32 3#32) := by decide  -- ehb
example : decode (mkRT 0#32 1#32 0#32 5#32 0x00#32) = some (.sll 0#32 1#32 5#32) := by decide
-- NAL = REGIMM rs = 0, rt = 0x10 (NAL p.306); BAL = REGIMM rs = 0, rt = 0x11 (BAL p.50)
example : decode 0x04101234#32 = some (.nal 0x1234#32) := by decide
example : decode 0x04111234#32 = some (.bal 0x1234#32) := by decide
example : encode (.nal 0x1234#32) = 0x04101234#32 := by decide
example : encode (.bal 0x1234#32) = 0x04111234#32 := by decide
-- BLTZAL/BGEZAL with rs ≠ 0 are removed
example : decode (mkIT 0x01#32 8#32 0x10#32 0x1234#32) = none := by decide
example : decode (mkIT 0x01#32 8#32 0x11#32 0x1234#32) = none := by decide

-- round trips (every constructor has one in this file)
example : decode (encode .pause) = some .pause := by decide
example : decode (encode (.nal 0xffff#32)) = some (.nal 0xffff#32) := by decide
example : decode (encode (.bal 0x8000#32)) = some (.bal 0x8000#32) := by decide
example : decode (encode (.add 29#32 8#32 3#32)) = some (.add 29#32 8#32 3#32) := by decide
example : decode (encode (.addu 29#32 8#32 3#32)) = some (.addu 29#32 8#32 3#32) := by decide
example : decode (encode (.sub 29#32 8#32 3#32)) = some (.sub 29#32 8#32 3#32) := by decide
example : decode (encode (.subu 29#32 8#32 3#32)) = some (.subu 29#32 8#32 3#32) := by decide
example : decode (encode (.and 29#32 8#32 3#32)) = some (.and 29#32 8#32 3#32) := by decide
example : decode (encode (.or 29#32 8#32 3#32)) = some (.or 29#32 8#32 3#32) := by decide
example : decode (encode (.xor 29#32 8#32 3#32)) = some (.xor 29#32 8#32 3#32) := by decide
example : decode (encode (.nor 29#32 8#32 3#32)) = some (.nor 29#32 8#32 3#32) := by decide
example : decode (encode (.slt 29#32 8#32 3#32)) = some (.slt 29#32 8#32 3#32) := by decide
example : decode (encode (.sltu 29#32 8#32 3#32)) = some (.sltu 29#32 8#32 3#32) := by decide
example : decode (encode (.sll 3#32 8#32 5#32)) = some (.sll 3#32 8#32 5#32) := by decide
example : decode (encode (.srl 3#32 8#32 5#32)) = some (.srl 3#32 8#32 5#32) := by decide
example : decode (encode (.sra 3#32 8#32 5#32)) = some (.sra 3#32 8#32 5#32) := by decide
example : decode (encode (.addiu 29#32 8#32 0x8001#32)) = some (.addiu 29#32 8#32 0x8001#32) := by decide
example : decode (encode (.slti 29#32 8#32 0x8001#32)) = some (.slti 29#32 8#32 0x8001#32) := by decide
example : decode (encode (.sltiu 29#32 8#32 0x8001#32)) = some (.sltiu 29#32 8#32 0x8001#32) := by decide
example : decode (encode (.andi 29#32 8#32 0x8001#32)) = some (.andi 29#32 8#32 0x8001#32) := by decide
example : decode (encode (.ori 29#32 8#32 0x8001#32)) = some (.ori 29#32 8#32 0x8001#32) := by decide
example : decode (encode (.xori 29#32 8#32 0x8001#32)) = some (.xori 29#32 8#32 0x8001#32) := by decide
example : decode (encode (.lw 29#32 8#32 0x8001#32)) = some (.lw 29#32 8#32 0x8001#32) := by decide
example : decode (encode (.sw 29#32 8#32 0x8001#32)) = some (.sw 29#32 8#32 0x8001#32) := by decide
example : decode (encode (.lb 29#32 8#32 0x8001#32)) = some (.lb 29#32 8#32 0x8001#32) := by decide
example : decode (encode (.lbu 29#32 8#32 0x8001#32)) = some (.lbu 29#32 8#32 0x8001#32) := by decide
example : decode (encode (.lh 29#32 8#32 0x8001#32)) = some (.lh 29#32 8#32 0x8001#32) := by decide
example : decode (encode (.lhu 29#32 8#32 0x8001#32)) = some (.lhu 29#32 8#32 0x8001#32) := by decide
example : decode (encode (.sh 29#32 8#32 0x8001#32)) = some (.sh 29#32 8#32 0x8001#32) := by decide
example : decode (encode (.beq 29#32 8#32 0x8001#32)) = some (.beq 29#32 8#32 0x8001#32) := by decide
example : decode (encode (.bne 29#32 8#32 0x8001#32)) = some (.bne 29#32 8#32 0x8001#32) := by decide
example : decode (encode (.blez 29#32 0x8001#32)) = some (.blez 29#32 0x8001#32) := by decide
example : decode (encode (.bgtz 29#32 0x8001#32)) = some (.bgtz 29#32 0x8001#32) := by decide
example : decode (encode (.j 0x2aaaaaa#32)) = some (.j 0x2aaaaaa#32) := by decide
example : decode (encode (.jal 0x2aaaaaa#32)) = some (.jal 0x2aaaaaa#32) := by decide
example : decode (encode (.rdpgpr 8#32 9#32)) = some (.rdpgpr 8#32 9#32) := by decide
example : decode (encode (.wrpgpr 8#32 9#32)) = some (.wrpgpr 8#32 9#32) := by decide
example : decode (encode (.recipS 2#32 4#32)) = some (.recipS 2#32 4#32) := by decide
example : decode (encode (.rsqrtD 2#32 4#32)) = some (.rsqrtD 2#32 4#32) := by decide
example : decode (encode (.roundWD 2#32 4#32)) = some (.roundWD 2#32 4#32) := by decide
example : decode (encode (.truncWD 2#32 4#32)) = some (.truncWD 2#32 4#32) := by decide
example : decode (encode (.ceilWD 2#32 4#32)) = some (.ceilWD 2#32 4#32) := by decide

-- removed opcode groups not covered above: SPECIAL2 (0x1c) MUL, COP1X (0x13) MADD.S, MOVCI
-- (SPECIAL funct 0x01), BC1 with cc ≠ 0
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 3#32 0#32 0x02#32) = none := by decide
example : decode 0x4c8628a0#32 = none := by decide
example : decode (mkRT 29#32 4#32 3#32 0#32 0x01#32) = none := by decide
example : decode (mkIT 0x11#32 0x08#32 0x1c#32 0x1234#32) = none := by decide
