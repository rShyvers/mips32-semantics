import Semantics.Instruction

/-!
# Tests for `Semantics/Instruction.lean` (decode / encode)

Hand-computed words decode to the expected constructor, `encode` produces the expected word,
and round trips hold on concrete instances. The checks are grouped in tables (`allTrue [..]`), one
per paragraph, each closed by `decide +kernel`. The general round-trip theorem is `decode_encode`
in `Semantics/Specs/DecodeSpec.lean`.
-/

/-- Every check of a table holds. Each table below is an `example` closed by `decide +kernel`: the
kernel evaluates every row (`decode w == expected`, `encode i == w`). -/
def allTrue (rows : List Bool) : Bool := rows.all id

-- Each instruction: hand-computed word (from INSTRUCTION-REF encodings,
-- distinct nontrivial field values) decodes to the expected variant.

-- R-type reg/reg/reg: rs=29, rt=8, rd=3
example : allTrue [
    decode (mkRT 29#32 8#32 3#32 0#32 0x20#32) == some (.add 29#32 8#32 3#32),
    decode (mkRT 29#32 8#32 3#32 0#32 0x21#32) == some (.addu 29#32 8#32 3#32),
    decode (mkRT 29#32 8#32 3#32 0#32 0x22#32) == some (.sub 29#32 8#32 3#32),
    decode (mkRT 29#32 8#32 3#32 0#32 0x23#32) == some (.subu 29#32 8#32 3#32),
    decode (mkRT 29#32 8#32 3#32 0#32 0x24#32) == some (.and 29#32 8#32 3#32),
    decode (mkRT 29#32 8#32 3#32 0#32 0x25#32) == some (.or 29#32 8#32 3#32),
    decode (mkRT 29#32 8#32 3#32 0#32 0x26#32) == some (.xor 29#32 8#32 3#32),
    decode (mkRT 29#32 8#32 3#32 0#32 0x27#32) == some (.nor 29#32 8#32 3#32),
    decode (mkRT 29#32 8#32 3#32 0#32 0x2a#32) == some (.slt 29#32 8#32 3#32),
    decode (mkRT 29#32 8#32 3#32 0#32 0x2b#32) == some (.sltu 29#32 8#32 3#32),
    decode (mkRT 29#32 8#32 3#32 0#32 0x0b#32) == none,  -- removed in R6 (was `movn`)
    decode (mkRT 29#32 8#32 3#32 0#32 0x0a#32) == none  -- removed in R6 (was `movz`)
  ] := by decide +kernel

-- R-type shift: rd=3, rt=8, shamt=5 (rs unused/0)
example : allTrue [
    decode (mkRT 0#32 8#32 3#32 5#32 0x00#32) == some (.sll 3#32 8#32 5#32),
    decode (mkRT 0#32 8#32 3#32 5#32 0x02#32) == some (.srl 3#32 8#32 5#32),
    decode (mkRT 0#32 8#32 3#32 5#32 0x03#32) == some (.sra 3#32 8#32 5#32)
  ] := by decide +kernel

-- R-type variable shift: rd=3, rt=8, rs=29 (shamt field unused/0)
example : allTrue [
    decode (mkRT 29#32 8#32 3#32 0#32 0x04#32) == some (.sllv 3#32 8#32 29#32),
    decode (mkRT 29#32 8#32 3#32 0#32 0x06#32) == some (.srlv 3#32 8#32 29#32),
    decode (mkRT 29#32 8#32 3#32 0#32 0x07#32) == some (.srav 3#32 8#32 29#32)
  ] := by decide +kernel

-- Removed in Release 6 (decodes to `none`): R-type mult/div: rs=29, rt=8
example : allTrue [
    decode (mkRT 29#32 8#32 0#32 0#32 0x18#32) == none,  -- removed in R6 (was `mult`)
    decode (mkRT 29#32 8#32 0#32 0#32 0x19#32) == none,  -- removed in R6 (was `multu`)
    decode (mkRT 29#32 8#32 0#32 0#32 0x1a#32) == none,  -- removed in R6 (was `div`)
    decode (mkRT 29#32 8#32 0#32 0#32 0x1b#32) == none  -- removed in R6 (was `divu`)
  ] := by decide +kernel

-- Removed in Release 6 (decodes to `none`): R-type move: rd=3
example : allTrue [
    decode (mkRT 0#32 0#32 3#32 0#32 0x12#32) == none,  -- removed in R6 (was `mflo`)
    decode (mkRT 0#32 0#32 3#32 0#32 0x10#32) == none  -- removed in R6 (was `mfhi`)
  ] := by decide +kernel

-- Removed in Release 6 (decodes to `none`): R-type move, write direction: rs=29 (same field shape as jr)
example : allTrue [
    decode (mkRT 29#32 0#32 0#32 0#32 0x11#32) == none,  -- removed in R6 (was `mthi`)
    decode (mkRT 29#32 0#32 0#32 0#32 0x13#32) == none  -- removed in R6 (was `mtlo`)
  ] := by decide +kernel

-- syscall: opcode 0, funct 0x0c, all other fields 0
example : allTrue [
    decode (mkRT 0#32 0#32 0#32 0#32 0x0c#32) == some (.syscall 0#32)
  ] := by decide +kernel

-- Release 6 bit-count: SPECIAL, rs=29, rt=0, rd=3, sa=1, funct 0x11 (CLO) / 0x10 (CLZ)
-- (MD00086 Vol II-A Rev 6.06, CLO p.134, CLZ p.135).
example : allTrue [
    decode (mkRT 29#32 0#32 3#32 1#32 0x11#32) == some (.clo 29#32 3#32),
    decode (mkRT 29#32 0#32 3#32 1#32 0x10#32) == some (.clz 29#32 3#32),
    decode 0x03a01851#32 == some (.clo 29#32 3#32),  -- clo $3,$29
    decode (mkRT 29#32 1#32 3#32 1#32 0x11#32) == none,  -- clo, rt ≠ 0
    -- the pre-Release 6 SPECIAL2 encodings (opcode 0x1c) do not decode: SPECIAL2 is removed.
    decode ((0x1c#32 <<< 26) ||| mkRT 29#32 3#32 3#32 0#32 0x21#32) == none,
    decode ((0x1c#32 <<< 26) ||| mkRT 29#32 3#32 3#32 0#32 0x20#32) == none,
    decode ((0x1c#32 <<< 26) ||| mkRT 29#32 17#32 3#32 0#32 0x21#32) == none
  ] := by decide +kernel

-- Removed in Release 6 (decodes to `none`): SPECIAL2 GPR multiply: rs=29, rt=8, rd=3 (plain rs/rt/rd shape, no duplication quirk)
example : allTrue [
    decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 3#32 0#32 0x02#32) == none  -- removed in R6 (was `mul`)
  ] := by decide +kernel

-- Removed in Release 6 (decodes to `none`): SPECIAL2 multiply-accumulate: rs=29, rt=8 (same rs/rt shape as mult/multu)
example : allTrue [
    decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x00#32) == none,  -- removed in R6 (was `madd`)
    decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x01#32) == none,  -- removed in R6 (was `maddu`)
    decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x04#32) == none,  -- removed in R6 (was `msub`)
    decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x05#32) == none  -- removed in R6 (was `msubu`)
  ] := by decide +kernel

-- SPECIAL3 BSHFL sign-extend/byte-swap: rd=3, rt=8, sub-field selects seb/seh/wsbh
example : allTrue [
    decode ((0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x10#32 0x20#32) == some (.seb 3#32 8#32),
    decode ((0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x18#32 0x20#32) == some (.seh 3#32 8#32),
    decode ((0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x02#32 0x20#32) == some (.wsbh 3#32 8#32)
  ] := by decide +kernel
-- a BSHFL sub-field that is no instruction (not seb/seh/wsbh/bitswap/align) → none
#guard decode ((0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x03#32 0x20#32) = none

-- rotr/rotrv (ROTR p.339, ROTRV p.340): rd=3, rt=8, sa=5 / rs=29 -- share srl/srlv's
-- opcode/funct but overload the rs/shamt field to select rotate.
example : allTrue [
    decode (mkRT 0x01#32 8#32 3#32 5#32 0x02#32) == some (.rotr 3#32 8#32 5#32),
    decode (mkRT 29#32 8#32 3#32 0x01#32 0x06#32) == some (.rotrv 3#32 8#32 29#32),
    -- rs=0 under funct 0x02 still decodes to plain srl (existing behavior unchanged)
    decode (mkRT 0#32 8#32 3#32 5#32 0x02#32) == some (.srl 3#32 8#32 5#32),
    decode (mkRT 29#32 8#32 3#32 0#32 0x06#32) == some (.srlv 3#32 8#32 29#32)
  ] := by decide +kernel

-- ext/ins (EXT p.183, INS p.192): rt=8, rs=29, pos=6, size=10
-- (so the raw `shamt` field is 6, and the raw `rd`-position field is
-- `size-1=9` for ext but `pos+size-1=15` for ins)
example : allTrue [
    decode ((0x1f#32 <<< 26) ||| mkRT 29#32 8#32 9#32 6#32 0x00#32) == some (.ext 8#32 29#32 6#32 10#32),
    decode ((0x1f#32 <<< 26) ||| mkRT 29#32 8#32 15#32 6#32 0x04#32) == some (.ins 8#32 29#32 6#32 10#32),
    -- break: opcode 0, funct 0x0d, all other fields 0
    decode (mkRT 0#32 0#32 0#32 0#32 0x0d#32) == some (.break 0#32)
  ] := by decide +kernel

-- sync: opcode 0, funct 0x0f, all other fields 0
example : allTrue [
    decode (mkRT 0#32 0#32 0#32 0#32 0x0f#32) == some (.sync 0#32),
    -- sync decodes the same way regardless of the (unmodeled) `stype` field,
    -- here carried in the raw `shamt`-position bits (e.g. `stype = 0x10`,
    -- a real MIPS32 "load ordering" hint value)
    decode (mkRT 0#32 0#32 0#32 0x10#32 0x0f#32) == some (.sync 0x10#32)
  ] := by decide +kernel

-- R-type trap-on-condition: rs=29, rt=8
example : allTrue [
    decode (mkRT 29#32 8#32 0#32 0#32 0x34#32) == some (.teq 29#32 8#32 0#32),
    decode (mkRT 29#32 8#32 0#32 0#32 0x36#32) == some (.tne 29#32 8#32 0#32),
    decode (mkRT 29#32 8#32 0#32 0#32 0x32#32) == some (.tlt 29#32 8#32 0#32),
    decode (mkRT 29#32 8#32 0#32 0#32 0x30#32) == some (.tge 29#32 8#32 0#32),
    decode (mkRT 29#32 8#32 0#32 0#32 0x33#32) == some (.tltu 29#32 8#32 0#32),
    decode (mkRT 29#32 8#32 0#32 0#32 0x31#32) == some (.tgeu 29#32 8#32 0#32)
  ] := by decide +kernel

-- I-type arith/logic: rs=29, rt=8, imm=0x1234
-- opcode 0x08 (pre-Release 6 `addi`) is POP10 in Release 6: with rs ≥ rt it is BOVC (BOVC p.107)
example : allTrue [
    decode (mkIT 0x08#32 29#32 8#32 0x1234#32) == some (.bovc 29#32 8#32 0x1234#32),
    decode (mkIT 0x09#32 29#32 8#32 0x1234#32) == some (.addiu 29#32 8#32 0x1234#32),
    decode (mkIT 0x0a#32 29#32 8#32 0x1234#32) == some (.slti 29#32 8#32 0x1234#32),
    decode (mkIT 0x0b#32 29#32 8#32 0x1234#32) == some (.sltiu 29#32 8#32 0x1234#32),
    decode (mkIT 0x0c#32 29#32 8#32 0x1234#32) == some (.andi 29#32 8#32 0x1234#32),
    decode (mkIT 0x0d#32 29#32 8#32 0x1234#32) == some (.ori 29#32 8#32 0x1234#32),
    decode (mkIT 0x0e#32 29#32 8#32 0x1234#32) == some (.xori 29#32 8#32 0x1234#32)
  ] := by decide +kernel

-- aui (opcode 0x0f): rs=29, rt=8, imm=0x1234; `lui $8, 0x1234` is `aui $8, $0, 0x1234`
-- (MD00086 Vol II-A Rev 6.06, AUI p.47)
example : allTrue [
    decode (mkIT 0x0f#32 0#32 8#32 0x1234#32) == some (.aui 0#32 8#32 0x1234#32),
    decode (mkIT 0x0f#32 29#32 8#32 0x1234#32) == some (.aui 29#32 8#32 0x1234#32),
    decode 0x3c081234#32 == some (.aui 0#32 8#32 0x1234#32),  -- lui $8, 0x1234
    encode (.aui 29#32 8#32 0x1234#32) == mkIT 0x0f#32 29#32 8#32 0x1234#32,
    decode (encode (.aui 29#32 8#32 0x8001#32)) == some (.aui 29#32 8#32 0x8001#32)
  ] := by decide +kernel

-- load/store: rs=29 (base), rt=8 (dest/src), imm=0x1234 (offset)
example : allTrue [
    decode (mkIT 0x23#32 29#32 8#32 0x1234#32) == some (.lw 29#32 8#32 0x1234#32),
    decode (mkIT 0x2b#32 29#32 8#32 0x1234#32) == some (.sw 29#32 8#32 0x1234#32),
    decode (mkIT 0x20#32 29#32 8#32 0x1234#32) == some (.lb 29#32 8#32 0x1234#32),
    decode (mkIT 0x24#32 29#32 8#32 0x1234#32) == some (.lbu 29#32 8#32 0x1234#32),
    decode (mkIT 0x21#32 29#32 8#32 0x1234#32) == some (.lh 29#32 8#32 0x1234#32),
    decode (mkIT 0x25#32 29#32 8#32 0x1234#32) == some (.lhu 29#32 8#32 0x1234#32),
    decode (mkIT 0x29#32 29#32 8#32 0x1234#32) == some (.sh 29#32 8#32 0x1234#32)
  ] := by decide +kernel

-- ll/sc (Release 6): SPECIAL3, base=29, rt=8, 9-bit offset 0x123 in bits 15..7, bit 6 = 0,
-- funct 0x36 (LL) / 0x26 (SC) (MD00086 Vol II-A Rev 6.06, LL p.223, SC p.347)
example : allTrue [
    decode 0x7fa891b6#32 == some (.ll 29#32 8#32 0x123#32),
    decode 0x7fa891a6#32 == some (.sc 29#32 8#32 0x123#32),
    decode 0x7c620436#32 == some (.ll 3#32 2#32 8#32),  -- ll $2, 8($3)
    decode 0x7c620476#32 == none,  -- ll, bit 6 = 1
    -- the pre-Release 6 encodings (opcodes 0x30/0x38) do not decode
    decode (mkIT 0x30#32 29#32 8#32 0x1234#32) == none,
    decode (mkIT 0x38#32 29#32 8#32 0x1234#32) == none
  ] := by decide +kernel

-- Removed in Release 6 (decodes to `none`): lwl/lwr/swl/swr: rs=29 (base), rt=8 (dest/src), imm=0x1234 (offset) --
-- identical field layout to lw/sw
example : allTrue [
    decode (mkIT 0x22#32 29#32 8#32 0x1234#32) == none,  -- removed in R6 (was `lwl`)
    decode (mkIT 0x26#32 29#32 8#32 0x1234#32) == none,  -- removed in R6 (was `lwr`)
    decode (mkIT 0x2a#32 29#32 8#32 0x1234#32) == none,  -- removed in R6 (was `swl`)
    decode (mkIT 0x2e#32 29#32 8#32 0x1234#32) == none  -- removed in R6 (was `swr`)
  ] := by decide +kernel

-- branch reg/reg: rs=29, rt=8, imm=0x1234
example : allTrue [
    decode (mkIT 0x04#32 29#32 8#32 0x1234#32) == some (.beq 29#32 8#32 0x1234#32),
    decode (mkIT 0x05#32 29#32 8#32 0x1234#32) == some (.bne 29#32 8#32 0x1234#32)
  ] := by decide +kernel

-- branch reg-only: rs=29, imm=0x1234 (rt fixed 0)
example : allTrue [
    decode (mkIT 0x06#32 29#32 0#32 0x1234#32) == some (.blez 29#32 0x1234#32),
    decode (mkIT 0x07#32 29#32 0#32 0x1234#32) == some (.bgtz 29#32 0x1234#32)
  ] := by decide +kernel

-- Removed in Release 6 (decodes to `none`): "branch likely" family: same field shapes as beq/bne/blez/bgtz, opcodes
-- 0x14..0x17 (Table A.2, p.451).
example : allTrue [
    decode (mkIT 0x14#32 29#32 8#32 0x1234#32) == none,  -- removed in R6 (was `beql`)
    decode (mkIT 0x15#32 29#32 8#32 0x1234#32) == none,  -- removed in R6 (was `bnel`)
    decode (mkIT 0x16#32 29#32 0#32 0x1234#32) == none,  -- removed in R6 (was `blezl`)
    decode (mkIT 0x17#32 29#32 0#32 0x1234#32) == none  -- removed in R6 (was `bgtzl`)
  ] := by decide +kernel

-- REGIMM zero-comparison branches: opcode 0x01, rs=29, imm=0x1234, rt field
-- selects bltz/bgez (bltzal/bgezal with rs ≠ 0: removed in Release 6, decode to `none`)
example : allTrue [
    decode (mkIT 0x01#32 29#32 0x00#32 0x1234#32) == some (.bltz 29#32 0x1234#32),
    decode (mkIT 0x01#32 29#32 0x01#32 0x1234#32) == some (.bgez 29#32 0x1234#32),
    decode (mkIT 0x01#32 29#32 0x10#32 0x1234#32) == none,  -- removed in R6 (was `bltzal`)
    decode (mkIT 0x01#32 29#32 0x11#32 0x1234#32) == none,  -- removed in R6 (was `bgezal`)
    -- Removed in Release 6 (decodes to `none`): REGIMM branch-likely zero-comparison family: same opcode 0x01, rt field
    -- 0x02/0x03/0x12/0x13 selects bltzl/bgezl/bltzall/bgezall.
    decode (mkIT 0x01#32 29#32 0x02#32 0x1234#32) == none,  -- removed in R6 (was `bltzl`)
    decode (mkIT 0x01#32 29#32 0x03#32 0x1234#32) == none,  -- removed in R6 (was `bgezl`)
    decode (mkIT 0x01#32 29#32 0x12#32 0x1234#32) == none,  -- removed in R6 (was `bltzall`)
    decode (mkIT 0x01#32 29#32 0x13#32 0x1234#32) == none,  -- removed in R6 (was `bgezall`)
    -- Removed in Release 6 (decodes to `none`): REGIMM trap-immediate family: same opcode 0x01, `rt` field selects
    -- teqi/tnei/tgei/tgeiu/tlti/tltiu (Table A.4, p.452).
    decode (mkIT 0x01#32 29#32 0x0c#32 0x1234#32) == none,  -- removed in R6 (was `teqi`)
    decode (mkIT 0x01#32 29#32 0x0e#32 0x1234#32) == none,  -- removed in R6 (was `tnei`)
    decode (mkIT 0x01#32 29#32 0x08#32 0x1234#32) == none,  -- removed in R6 (was `tgei`)
    decode (mkIT 0x01#32 29#32 0x09#32 0x1234#32) == none,  -- removed in R6 (was `tgeiu`)
    decode (mkIT 0x01#32 29#32 0x0a#32 0x1234#32) == none,  -- removed in R6 (was `tlti`)
    decode (mkIT 0x01#32 29#32 0x0b#32 0x1234#32) == none,  -- removed in R6 (was `tltiu`)
    -- synci: same opcode 0x01, `rt` field fixed 0x1f (SYNCI p.412), `rs, imm` shape
    -- identical to `blez`/`bgtz`.
    decode (mkIT 0x01#32 29#32 0x1f#32 0x1234#32) == some (.synci 29#32 0x1234#32)
  ] := by decide +kernel
-- a REGIMM word with an unrecognized rt field (0x1d is reserved in the
-- real MIPS32 REGIMM table -- not one of bltz/bgez/bltzal/bgezal/the trap
-- family/synci above) decodes to none
#guard decode (mkIT 0x01#32 29#32 0x1d#32 0x1234#32) = none

-- J-type: target = 0x3ffffff (all 26 bits)
example : allTrue [
    decode ((0x02#32 <<< 26) ||| mkJT 0x3ffffff#32) == some (.j 0x3ffffff#32),
    decode ((0x03#32 <<< 26) ||| mkJT 0x3ffffff#32) == some (.jal 0x3ffffff#32)
  ] := by decide +kernel

-- Coprocessor 1 (FPU): mtc1/mfc1 (fmt=MT/MF, rt=8, fs=3). Unlike plain
-- R-type, COP1 words need opcode 0x11 OR'd in explicitly over `mkRT`'s
-- (always-0) opcode field.
example : allTrue [
    decode ((0x11#32 <<< 26) ||| mkRT 0x00#32 8#32 3#32 0#32 0#32) == some (.mfc1 8#32 3#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x04#32 8#32 3#32 0#32 0#32) == some (.mtc1 8#32 3#32),
    -- lwc1/swc1: rs=29 (base), ft=5, imm=0x1234 (identical layout to lw/sw)
    decode (mkIT 0x31#32 29#32 5#32 0x1234#32) == some (.lwc1 29#32 5#32 0x1234#32),
    decode (mkIT 0x39#32 29#32 5#32 0x1234#32) == some (.swc1 29#32 5#32 0x1234#32),
    -- add.s/sub.s/mul.s/div.s: fmt=S, ft=6, fs=7, fd=8
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 8#32 0x00#32) == some (.addS 8#32 7#32 6#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 8#32 0x01#32) == some (.subS 8#32 7#32 6#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 8#32 0x02#32) == some (.mulS 8#32 7#32 6#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 8#32 0x03#32) == some (.divS 8#32 7#32 6#32),
    -- mov.s/cvt.w.s: fmt=S, fs=7, fd=8 (ft-position fixed 0)
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x06#32) == some (.movS 8#32 7#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x24#32) == some (.cvtWS 8#32 7#32),
    -- cvt.s.w: fmt=W, fs=7, fd=8
    decode ((0x11#32 <<< 26) ||| mkRT 0x14#32 0#32 7#32 8#32 0x20#32) == some (.cvtSW 8#32 7#32),
    -- Removed in Release 6 (decodes to `none`): c.eq.s/c.lt.s/c.le.s: fmt=S, fs=7, ft=6, fd-position (cc) fixed 0
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x32#32) == none,  -- removed in R6 (was `cCondS`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x3c#32) == none,  -- removed in R6 (was `cCondS`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x3e#32) == none,  -- removed in R6 (was `cCondS`)
    -- c.eq.s with a nonzero cc field → none (C.cond.fmt is removed in Release 6 in any case)
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 1#32 0x32#32) == none,
    -- sqrt.s/abs.s/neg.s: fmt=S, fs=7, fd=8 (ft-position fixed 0)
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x04#32) == some (.sqrtS 8#32 7#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x05#32) == some (.absS 8#32 7#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x07#32) == some (.negS 8#32 7#32),
    -- round.w.s/trunc.w.s/ceil.w.s/floor.w.s: fmt=S, fs=7, fd=8 (ft-position fixed 0)
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x0c#32) == some (.roundWS 8#32 7#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x0d#32) == some (.truncWS 8#32 7#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x0e#32) == some (.ceilWS 8#32 7#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x0f#32) == some (.floorWS 8#32 7#32),
    -- Removed in Release 6 (decodes to `none`): c.f.s/c.un.s/c.ueq.s/c.olt.s/c.ult.s/c.ole.s/c.ule.s: fmt=S, fs=7, ft=6, fd-position (cc) fixed 0
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x30#32) == none,  -- removed in R6 (was `cCondS`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x31#32) == none,  -- removed in R6 (was `cCondS`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x33#32) == none,  -- removed in R6 (was `cCondS`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x34#32) == none,  -- removed in R6 (was `cCondS`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x35#32) == none,  -- removed in R6 (was `cCondS`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x36#32) == none,  -- removed in R6 (was `cCondS`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x37#32) == none,  -- removed in R6 (was `cCondS`)
    -- c.un.s with a nonzero cc field → none (C.cond.fmt is removed in Release 6 in any case)
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 1#32 0x31#32) == none
  ] := by decide +kernel

-- ldc1/sdc1: rs=29 (base), ft=5, imm=0x1234 (identical layout to lwc1/swc1)
example : allTrue [
    decode (mkIT 0x35#32 29#32 5#32 0x1234#32) == some (.ldc1 29#32 5#32 0x1234#32),
    decode (mkIT 0x3d#32 29#32 5#32 0x1234#32) == some (.sdc1 29#32 5#32 0x1234#32),
    -- add.d/sub.d/mul.d/div.d: fmt=D, ft=6, fs=7, fd=8
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 8#32 0x00#32) == some (.addD 8#32 7#32 6#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 8#32 0x01#32) == some (.subD 8#32 7#32 6#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 8#32 0x02#32) == some (.mulD 8#32 7#32 6#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 8#32 0x03#32) == some (.divD 8#32 7#32 6#32),
    -- mov.d/sqrt.d/abs.d/neg.d/cvt.w.d: fmt=D, fs=7, fd=8 (ft-position fixed 0)
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x06#32) == some (.movD 8#32 7#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x04#32) == some (.sqrtD 8#32 7#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x05#32) == some (.absD 8#32 7#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x07#32) == some (.negD 8#32 7#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x24#32) == some (.cvtWD 8#32 7#32),
    -- cvt.d.s: fmt=S (source is single), fs=7, fd=8
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x21#32) == some (.cvtDS 8#32 7#32),
    -- cvt.s.d: fmt=D (source is double), fs=7, fd=8
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x20#32) == some (.cvtSD 8#32 7#32),
    -- cvt.d.w: fmt=W (source is a word), fs=7, fd=8
    decode ((0x11#32 <<< 26) ||| mkRT 0x14#32 0#32 7#32 8#32 0x21#32) == some (.cvtDW 8#32 7#32),
    -- Removed in Release 6 (decodes to `none`): c.eq.d/c.lt.d/c.le.d/c.f.d/c.un.d/c.ueq.d/c.olt.d/c.ult.d/c.ole.d/c.ule.d:
    -- fmt=D, fs=7, ft=6, fd-position (cc) fixed 0
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x32#32) == none,  -- removed in R6 (was `cCondD`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x3c#32) == none,  -- removed in R6 (was `cCondD`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x3e#32) == none,  -- removed in R6 (was `cCondD`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x30#32) == none,  -- removed in R6 (was `cCondD`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x31#32) == none,  -- removed in R6 (was `cCondD`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x33#32) == none,  -- removed in R6 (was `cCondD`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x34#32) == none,  -- removed in R6 (was `cCondD`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x35#32) == none,  -- removed in R6 (was `cCondD`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x36#32) == none,  -- removed in R6 (was `cCondD`)
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x37#32) == none,  -- removed in R6 (was `cCondD`)
    -- c.eq.d with a nonzero cc field → none (C.cond.fmt is removed in Release 6 in any case)
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 1#32 0x32#32) == none
  ] := by decide +kernel

-- cfc1/mfc1 share the same (rt, fs) field shape, distinguished by the
-- rs-position sub-opcode (CF=0x02 vs MF=0x00); ctc1/mtc1 likewise (CT=0x06 vs MT=0x04)
example : allTrue [
    decode ((0x11#32 <<< 26) ||| mkRT 0x02#32 8#32 3#32 0#32 0#32) == some (.cfc1 8#32 3#32),
    decode ((0x11#32 <<< 26) ||| mkRT 0x06#32 8#32 3#32 0#32 0#32) == some (.ctc1 8#32 3#32),
    -- Removed in Release 6 (decodes to `none`): bc1t/bc1f: fmt=BC1, tf=1/0, offset=0x1234
    decode (mkIT 0x11#32 0x08#32 1#32 0x1234#32) == none,  -- removed in R6 (was `bc1t`)
    decode (mkIT 0x11#32 0x08#32 0#32 0x1234#32) == none,  -- removed in R6 (was `bc1f`)
    -- Removed in Release 6 (decodes to `none`): BC1 with nd = 1 (rt-field bit 1) is the branch-likely form; bits 20..18 are cc
    decode (mkIT 0x11#32 0x08#32 2#32 0x1234#32) == none,  -- removed in R6 (was `bc1fl`)
    decode (mkIT 0x11#32 0x08#32 3#32 0x1234#32) == none,  -- removed in R6 (was `bc1tl`)
    decode (mkIT 0x11#32 0x08#32 0x1d#32 0x1234#32) == none  -- removed in R6 (was `bc1t`)
  ] := by decide +kernel

-- `encode ∘ decode` round-trips, spanning R / I / J / branch / syscall
example : allTrue [
    encode (.add 29#32 8#32 3#32) == mkRT 29#32 8#32 3#32 0#32 0x20#32,
    encode (.lw 29#32 8#32 0x1234#32) == mkIT 0x23#32 29#32 8#32 0x1234#32,
    encode (.beq 29#32 8#32 0x1234#32) == mkIT 0x04#32 29#32 8#32 0x1234#32,
    encode (.j 0x3ffffff#32) == (0x02#32 <<< 26) ||| mkJT 0x3ffffff#32,
    encode (.syscall 0#32) == mkRT 0#32 0#32 0#32 0#32 0x0c#32,
    encode (.sll 3#32 8#32 5#32) == mkRT 0#32 8#32 3#32 5#32 0x00#32,
    encode (.clo 29#32 3#32) == mkRT 29#32 0#32 3#32 1#32 0x11#32,
    encode (.clz 29#32 3#32) == mkRT 29#32 0#32 3#32 1#32 0x10#32,
    encode (.seb 3#32 8#32) == (0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x10#32 0x20#32,
    encode (.wsbh 3#32 8#32) == (0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x02#32 0x20#32,
    encode (.rotr 3#32 8#32 5#32) == mkRT 0x01#32 8#32 3#32 5#32 0x02#32,
    encode (.rotrv 3#32 8#32 29#32) == mkRT 29#32 8#32 3#32 0x01#32 0x06#32,
    encode (.ext 8#32 29#32 6#32 10#32) == (0x1f#32 <<< 26) ||| mkRT 29#32 8#32 9#32 6#32 0x00#32,
    encode (.ins 8#32 29#32 6#32 10#32) == (0x1f#32 <<< 26) ||| mkRT 29#32 8#32 15#32 6#32 0x04#32,
    encode (.sllv 3#32 8#32 29#32) == mkRT 29#32 8#32 3#32 0#32 0x04#32,
    encode (.jalr 29#32 3#32) == mkRT 29#32 0#32 3#32 0#32 0x09#32,
    encode (.jalrHb 29#32 3#32) == mkRT 29#32 0#32 3#32 0x10#32 0x09#32,
    -- full round trip for every new instruction (decode ∘ encode = id on the field values we store)
    decode (encode (.clo 29#32 3#32)) == some (.clo 29#32 3#32),
    decode (encode (.clz 29#32 3#32)) == some (.clz 29#32 3#32),
    decode (encode (.seb 3#32 8#32)) == some (.seb 3#32 8#32),
    decode (encode (.seh 3#32 8#32)) == some (.seh 3#32 8#32),
    decode (encode (.wsbh 3#32 8#32)) == some (.wsbh 3#32 8#32),
    decode (encode (.rotr 3#32 8#32 5#32)) == some (.rotr 3#32 8#32 5#32),
    decode (encode (.rotrv 3#32 8#32 29#32)) == some (.rotrv 3#32 8#32 29#32),
    decode (encode (.ext 8#32 29#32 6#32 10#32)) == some (.ext 8#32 29#32 6#32 10#32),
    decode (encode (.ins 8#32 29#32 6#32 10#32)) == some (.ins 8#32 29#32 6#32 10#32),
    -- ext/ins round-trip edge cases: pos=0 (size=32, the full word) and
    -- pos+size=32 (touches the top bit) -- both satisfy the real `pos+size<=32`
    -- constraint so the `rd`-position field packs/unpacks without truncation.
    decode (encode (.ext 8#32 29#32 0#32 32#32)) == some (.ext 8#32 29#32 0#32 32#32),
    decode (encode (.ins 8#32 29#32 20#32 12#32)) == some (.ins 8#32 29#32 20#32 12#32),
    decode (encode (.sllv 3#32 8#32 29#32)) == some (.sllv 3#32 8#32 29#32),
    decode (encode (.srlv 3#32 8#32 29#32)) == some (.srlv 3#32 8#32 29#32),
    decode (encode (.srav 3#32 8#32 29#32)) == some (.srav 3#32 8#32 29#32),
    decode (encode (.jalr 29#32 3#32)) == some (.jalr 29#32 3#32),
    decode (encode (.jalrHb 29#32 3#32)) == some (.jalrHb 29#32 3#32),
    encode (.break 0#32) == mkRT 0#32 0#32 0#32 0#32 0x0d#32,
    encode (.teq 29#32 8#32 0#32) == mkRT 29#32 8#32 0#32 0#32 0x34#32
  ] := by decide +kernel

-- `decode (encode ...)` round-trips for every new trap/break instruction
example : allTrue [
    decode (encode (.teq 29#32 8#32 0#32)) == some (.teq 29#32 8#32 0#32),
    decode (encode (.tne 29#32 8#32 0#32)) == some (.tne 29#32 8#32 0#32),
    decode (encode (.tlt 29#32 8#32 0#32)) == some (.tlt 29#32 8#32 0#32),
    decode (encode (.tge 29#32 8#32 0#32)) == some (.tge 29#32 8#32 0#32),
    decode (encode (.tltu 29#32 8#32 0#32)) == some (.tltu 29#32 8#32 0#32),
    decode (encode (.tgeu 29#32 8#32 0#32)) == some (.tgeu 29#32 8#32 0#32),
    decode (encode (.break 0#32)) == some (.break 0#32)
  ] := by decide +kernel

-- sync/synci: encode matches the hand-computed word, and decode (encode i) = some i
example : allTrue [
    encode (.sync 0#32) == mkRT 0#32 0#32 0#32 0#32 0x0f#32,
    encode (.synci 29#32 0x1234#32) == mkIT 0x01#32 29#32 0x1f#32 0x1234#32,
    decode (encode (.sync 0#32)) == some (.sync 0#32),
    decode (encode (.synci 29#32 0x1234#32)) == some (.synci 29#32 0x1234#32)
  ] := by decide +kernel

-- Coprocessor 1 (FPU): full `decode (encode i) = some i` round-trips
example : allTrue [
    decode (encode (.mfc1 8#32 3#32)) == some (.mfc1 8#32 3#32),
    decode (encode (.mtc1 8#32 3#32)) == some (.mtc1 8#32 3#32),
    decode (encode (.lwc1 29#32 5#32 0x1234#32)) == some (.lwc1 29#32 5#32 0x1234#32),
    decode (encode (.swc1 29#32 5#32 0x1234#32)) == some (.swc1 29#32 5#32 0x1234#32),
    decode (encode (.addS 8#32 7#32 6#32)) == some (.addS 8#32 7#32 6#32),
    decode (encode (.subS 8#32 7#32 6#32)) == some (.subS 8#32 7#32 6#32),
    decode (encode (.mulS 8#32 7#32 6#32)) == some (.mulS 8#32 7#32 6#32),
    decode (encode (.divS 8#32 7#32 6#32)) == some (.divS 8#32 7#32 6#32),
    decode (encode (.movS 8#32 7#32)) == some (.movS 8#32 7#32),
    decode (encode (.cvtSW 8#32 7#32)) == some (.cvtSW 8#32 7#32),
    decode (encode (.cvtWS 8#32 7#32)) == some (.cvtWS 8#32 7#32),
    decode (encode (.sqrtS 8#32 7#32)) == some (.sqrtS 8#32 7#32),
    decode (encode (.absS 8#32 7#32)) == some (.absS 8#32 7#32),
    decode (encode (.negS 8#32 7#32)) == some (.negS 8#32 7#32),
    decode (encode (.roundWS 8#32 7#32)) == some (.roundWS 8#32 7#32),
    decode (encode (.truncWS 8#32 7#32)) == some (.truncWS 8#32 7#32),
    decode (encode (.ceilWS 8#32 7#32)) == some (.ceilWS 8#32 7#32),
    decode (encode (.floorWS 8#32 7#32)) == some (.floorWS 8#32 7#32),
    decode (encode (.cfc1 8#32 3#32)) == some (.cfc1 8#32 3#32),
    decode (encode (.ctc1 8#32 3#32)) == some (.ctc1 8#32 3#32)
  ] := by decide +kernel

-- Coprocessor 1 (FPU), double-precision: full `decode (encode i) = some i` round-trips
example : allTrue [
    decode (encode (.ldc1 29#32 5#32 0x1234#32)) == some (.ldc1 29#32 5#32 0x1234#32),
    decode (encode (.sdc1 29#32 5#32 0x1234#32)) == some (.sdc1 29#32 5#32 0x1234#32),
    decode (encode (.addD 8#32 7#32 6#32)) == some (.addD 8#32 7#32 6#32),
    decode (encode (.subD 8#32 7#32 6#32)) == some (.subD 8#32 7#32 6#32),
    decode (encode (.mulD 8#32 7#32 6#32)) == some (.mulD 8#32 7#32 6#32),
    decode (encode (.divD 8#32 7#32 6#32)) == some (.divD 8#32 7#32 6#32),
    decode (encode (.movD 8#32 7#32)) == some (.movD 8#32 7#32),
    decode (encode (.cvtDS 8#32 7#32)) == some (.cvtDS 8#32 7#32),
    decode (encode (.cvtSD 8#32 7#32)) == some (.cvtSD 8#32 7#32),
    decode (encode (.cvtDW 8#32 7#32)) == some (.cvtDW 8#32 7#32),
    decode (encode (.cvtWD 8#32 7#32)) == some (.cvtWD 8#32 7#32),
    decode (encode (.sqrtD 8#32 7#32)) == some (.sqrtD 8#32 7#32),
    decode (encode (.absD 8#32 7#32)) == some (.absD 8#32 7#32),
    decode (encode (.negD 8#32 7#32)) == some (.negD 8#32 7#32)
  ] := by decide +kernel

-- REGIMM zero-comparison branches: full decode(encode i) = some i round-trips
example : allTrue [
    decode (encode (.bltz 29#32 0x1234#32)) == some (.bltz 29#32 0x1234#32),
    decode (encode (.bgez 29#32 0x1234#32)) == some (.bgez 29#32 0x1234#32),
    -- ll/sc: encode matches the hand-computed word, and decode (encode i) = some i
    encode (.ll 29#32 8#32 0x123#32) == 0x7fa891b6#32,
    encode (.sc 29#32 8#32 0x123#32) == 0x7fa891a6#32,
    encode (.ll 3#32 2#32 8#32) == 0x7c620436#32,
    decode (encode (.ll 29#32 8#32 0x1ff#32)) == some (.ll 29#32 8#32 0x1ff#32),
    decode (encode (.sc 29#32 8#32 0x100#32)) == some (.sc 29#32 8#32 0x100#32)
  ] := by decide +kernel

-- unknown opcodes → none
#guard decode (mkIT 0x3a#32 0#32 0#32 0#32) = some (.balc 0#32)  -- opcode 0x3a: Release 6 BALC (BALC p.52)
#guard decode (mkIT 0x3b#32 0#32 0#32 0#32) = some (.addiupc 0#32 0#32)  -- opcode 0x3b: PCREL ADDIUPC (p.37)
-- opcode 0x11 (COP1) is implemented for the fmt/funct combinations below;
-- an unrecognized fmt (not MF/MT/BC1/S/W) still decodes to `none`.
#guard decode (mkIT 0x11#32 0x1f#32 0#32 0#32) = none
-- opcodes 0x16/0x17 with `rt = 0` (pre-Release 6 blezl/bgtzl) and 0x12/0x13 (COP2, COP1X) do not
-- decode (Release 6 reuses 0x16/0x17 with `rt ≠ 0` for the compact branches, Table A.26 p.464).
#guard decode (mkIT 0x16#32 29#32 0#32 0#32) = none
#guard decode (mkIT 0x17#32 29#32 0#32 0#32) = none
#guard decode (mkIT 0x12#32 0#32 0#32 0#32) = none
-- Removed in Release 6 (decodes to `none`): opcode 0x13 (COP1X): funct 0x05 `luxc1` / 0x0d `suxc1` and
-- the paired-single functs
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

-- funct 0x35 sits between teq (0x34) and tne (0x36); Release 6 assigns it to SELEQZ (MD00086 Vol
-- II-A Rev 6.06, SELEQZ SELNEZ, p.369; R6-4: this test expected `none` before). With `sa ≠ 0` it does
-- not decode (an UNPREDICTABLE nonzero unnamed field).
#guard decode (mkRT 0#32 0#32 0#32 0#32 0x35#32) = some (.seleqz 0#32 0#32 0#32)
#guard decode (mkRT 0#32 0#32 0#32 1#32 0x35#32) = none
#guard decode (encode (.addS 8#32 7#32 6#32)) = some (.addS 8#32 7#32 6#32)
#guard decode (encode (.addD 8#32 7#32 6#32)) = some (.addD 8#32 7#32 6#32)
#guard decode (encode (.ldc1 29#32 5#32 0x1234#32)) = some (.ldc1 29#32 5#32 0x1234#32)

-- Coprocessor 0 (CP0) register move / execution control: mfc0/mtc0/eret/wait
-- (Tables A.11-A.13, p.455). rt=8 (GPR), rd=13 (Cause).
example : allTrue [
    decode ((0x10#32 <<< 26) ||| mkRT 0x00#32 8#32 13#32 0#32 0#32) == some (.mfc0 8#32 13#32 0#32),
    decode ((0x10#32 <<< 26) ||| mkRT 0x04#32 8#32 13#32 0#32 0#32) == some (.mtc0 8#32 13#32 0#32),
    decode ((0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x18#32) == some .eret,
    decode ((0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x20#32) == some (.wait 0#32)
  ] := by decide +kernel

-- encode produces the exact hand-computed words above.
example : allTrue [
    encode (.mfc0 8#32 13#32 0#32) == (0x10#32 <<< 26) ||| mkRT 0x00#32 8#32 13#32 0#32 0#32,
    encode (.mtc0 8#32 13#32 0#32) == (0x10#32 <<< 26) ||| mkRT 0x04#32 8#32 13#32 0#32 0#32,
    encode .eret == (0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x18#32,
    encode (.wait 0#32) == (0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x20#32
  ] := by decide +kernel

-- full decode ∘ encode round trips for Status/Cause/EPC (BadVAddr/ErrorEPC are below).
example : allTrue [
    decode (encode (.mfc0 8#32 12#32 0#32)) == some (.mfc0 8#32 12#32 0#32),
    decode (encode (.mfc0 8#32 13#32 0#32)) == some (.mfc0 8#32 13#32 0#32),
    decode (encode (.mfc0 8#32 14#32 0#32)) == some (.mfc0 8#32 14#32 0#32),
    decode (encode (.mtc0 8#32 12#32 0#32)) == some (.mtc0 8#32 12#32 0#32),
    decode (encode (.mtc0 8#32 13#32 0#32)) == some (.mtc0 8#32 13#32 0#32),
    decode (encode (.mtc0 8#32 14#32 0#32)) == some (.mtc0 8#32 14#32 0#32),
    decode (encode .eret) == some .eret,
    decode (encode (.wait 0#32)) == some (.wait 0#32)
  ] := by decide +kernel

-- an unrecognized COP0 `rs`-field (not MF/MT/CO) decodes to `none`.
#guard decode (mkIT 0x10#32 0x08#32 0#32 0#32) = none
-- a CO-sub-format word with an unrecognized `funct` (not eret's 0x18 or
-- wait's 0x20) decodes to `none`.
#guard decode ((0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x01#32) = none

-- ## Strict decoding (reserved fields must be zero) and `sb`

-- `sb`: opcode 0x28.
example : allTrue [
    decode (mkIT 0x28#32 29#32 8#32 0x1234#32) == some (.sb 29#32 8#32 0x1234#32),
    decode (encode (.sb 29#32 8#32 0xffff#32)) == some (.sb 29#32 8#32 0xffff#32),
    decode 0xa1090003#32 == some (.sb 8#32 9#32 3#32)  -- sb $t1, 3($t0)
  ] := by decide +kernel

-- Nonzero must-be-zero fields do not decode.
example : allTrue [
    decode (mkRT 29#32 8#32 3#32 1#32 0x20#32) == none,  -- add, shamt ≠ 0
    decode (mkRT 29#32 8#32 3#32 0#32 0x18#32) == none,  -- mult, rd ≠ 0
    decode (mkRT 1#32 0#32 3#32 0#32 0x10#32) == none,  -- mfhi, rs ≠ 0
    decode (mkRT 0#32 1#32 3#32 0#32 0x10#32) == none,  -- mfhi, rt ≠ 0
    decode (mkIT 0x0f#32 1#32 8#32 0x1234#32) == some (.aui 1#32 8#32 0x1234#32),  -- aui, rs ≠ 0
    -- Release 6: BLEZ/BGTZ with rt ≠ 0 are POP06/POP07 and BLEZL/BGTZL's opcodes with rt ≠ 0 are POP26/
    -- POP27 (Table A.26, p.464); rs ≠ rt, both nonzero: BGEUC, BLTUC, BGEC, BLTC.
    decode (mkIT 0x06#32 29#32 1#32 0x1234#32) == some (.bgeuc 29#32 1#32 0x1234#32),
    decode (mkIT 0x07#32 29#32 1#32 0x1234#32) == some (.bltuc 29#32 1#32 0x1234#32),
    decode (mkIT 0x16#32 29#32 1#32 0x1234#32) == some (.bgec 29#32 1#32 0x1234#32),
    decode (mkIT 0x17#32 29#32 1#32 0x1234#32) == some (.bltc 29#32 1#32 0x1234#32),
    decode (mkRT 29#32 1#32 0#32 0#32 0x08#32) == none,  -- jr, rt ≠ 0
    decode (mkRT 29#32 0#32 1#32 0#32 0x08#32) == none,  -- jr, rd ≠ 0
    decode ((0x1f#32 <<< 26) ||| mkRT 1#32 8#32 3#32 0x10#32 0x20#32) == none,  -- seb, rs ≠ 0
    decode ((0x1f#32 <<< 26) ||| mkRT 1#32 8#32 3#32 0x18#32 0x20#32) == none,  -- seh, rs ≠ 0
    decode ((0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 1#32 0x18#32) == some .eretnc,  -- bit 6 set: ERETNC
    decode ((0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 2#32 0x18#32) == none,  -- eret, CO bits ≠ 0
    decode ((0x10#32 <<< 26) ||| mkRT 0x11#32 0#32 0#32 0#32 0x18#32) == none,  -- eret, CO bits ≠ 0
    -- `srl`/`rotr` are selected by bit 21 alone, with bits 25..22 zero; likewise
    -- `srlv`/`rotrv` by bit 6 with bits 10..7 zero.
    decode (mkRT 2#32 8#32 3#32 5#32 0x02#32) == none,
    decode (mkRT 3#32 8#32 3#32 5#32 0x02#32) == none,
    decode (mkRT 29#32 8#32 3#32 2#32 0x06#32) == none,
    decode (mkRT 29#32 8#32 3#32 3#32 0x06#32) == none,
    -- `mfc0`/`mtc0`: every `(rd, sel)` decodes in Release 6 (an unimplemented register, e.g. `mfc0
    -- $t0,$12,3` = SRSMap, reads 0 and ignores writes, MFC0 p.266, MTC0 p.290); nonzero bits 10..3 do not.
    decode 0x40086003#32 == some (.mfc0 8#32 12#32 3#32),  -- mfc0 $t0,$12,3
    decode 0x40886003#32 == some (.mtc0 8#32 12#32 3#32),  -- mtc0 $t0,$12,3
    -- IntCtl (12,1) and SRSCtl (12,2) are modeled since wave 6 (F13, F16).
    decode 0x40086001#32 == some (.mfc0 8#32 12#32 1#32),  -- mfc0 $t0,$12,1
    decode 0x40886002#32 == some (.mtc0 8#32 12#32 2#32),  -- mtc0 $t0,$12,2
    -- `rdpgpr $t0, $t1` / `wrpgpr $t0, $t1` (MD00086 Vol II-A Rev 6.06, RDPGPR p.335, WRPGPR p.444).
    decode 0x41494000#32 == some (.rdpgpr 8#32 9#32),
    decode 0x41c94000#32 == some (.wrpgpr 8#32 9#32),
    encode (.rdpgpr 8#32 9#32) == 0x41494000#32,
    encode (.wrpgpr 8#32 9#32) == 0x41c94000#32,
    decode 0x41494001#32 == none,  -- bits 10..0 ≠ 0
    decode 0x41c94040#32 == none,  -- bits 10..0 ≠ 0
    decode 0x40086008#32 == none,  -- bit 3 set
    decode ((0x10#32 <<< 26) ||| mkRT 0#32 8#32 1#32 0#32 0#32) == some (.mfc0 8#32 1#32 0#32),  -- Random (1): reads 0
    decode ((0x10#32 <<< 26) ||| mkRT 0#32 8#32 10#32 0#32 0#32) == some (.mfc0 8#32 10#32 0#32),  -- EntryHi (10): reads 0
    -- Count (9,0), Compare (11,0) and HWREna (7,0) are modeled since wave 5 (F12, F15).
    decode ((0x10#32 <<< 26) ||| mkRT 0#32 8#32 9#32 0#32 0#32) == some (.mfc0 8#32 9#32 0#32),  -- Count
    decode (encode (.mtc0 8#32 11#32 0#32)) == some (.mtc0 8#32 11#32 0#32),  -- Compare
    decode (encode (.mtc0 8#32 7#32 0#32)) == some (.mtc0 8#32 7#32 0#32),  -- HWREna
    decode (encode (.mfc0 8#32 7#32 0#32)) == some (.mfc0 8#32 7#32 0#32),  -- HWREna
    -- `rdhwr` (SPECIAL3 funct 0x3b): `rdhwr $3, $29` is 0x7c03e83b (MD00086 Vol II-A Rev 6.06, RDHWR,
    -- p.332); Release 6 adds `sel` in bits 8..6; `rs` and bits 10..9 must be zero.
    encode (.rdhwr 3#32 29#32 0#32) == 0x7c03e83b#32,
    decode 0x7c03e83b#32 == some (.rdhwr 3#32 29#32 0#32),
    decode (encode (.rdhwr 8#32 2#32 0#32)) == some (.rdhwr 8#32 2#32 0#32),
    decode (encode (.rdhwr 8#32 2#32 7#32)) == some (.rdhwr 8#32 2#32 7#32),
    decode 0x7c03e87b#32 == some (.rdhwr 3#32 29#32 1#32),  -- sel = 1
    decode 0x7c03ea3b#32 == none,  -- bit 9 = 1
    decode 0x7c23e83b#32 == none,  -- rs = 1
    decode (encode (.mfc0 8#32 8#32 0#32)) == some (.mfc0 8#32 8#32 0#32),  -- BadVAddr
    decode (encode (.mfc0 8#32 30#32 0#32)) == some (.mfc0 8#32 30#32 0#32),  -- ErrorEPC
    -- COP1 moves: bits 10..0 must be zero; unary ops: `ft` must be zero.
    decode ((0x11#32 <<< 26) ||| mkRT 0x00#32 8#32 3#32 0#32 1#32) == none,
    decode ((0x11#32 <<< 26) ||| mkRT 0x04#32 8#32 3#32 1#32 0#32) == none,
    decode ((0x11#32 <<< 26) ||| mkRT 0x02#32 8#32 3#32 0#32 1#32) == none,
    decode ((0x11#32 <<< 26) ||| mkRT 0x06#32 8#32 3#32 0#32 1#32) == none,
    decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 1#32 7#32 8#32 0x06#32) == none,  -- mov.s, ft ≠ 0
    decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 1#32 7#32 8#32 0x04#32) == none,  -- sqrt.d, ft ≠ 0
    -- UNPREDICTABLE `ext`/`ins` field combinations do not decode.
    decode ((0x1f#32 <<< 26) ||| mkRT 29#32 8#32 31#32 1#32 0x00#32) == none,  -- ext lsb+msbd = 32
    decode ((0x1f#32 <<< 26) ||| mkRT 29#32 8#32 3#32 6#32 0x04#32) == none  -- ins msb < lsb
  ] := by decide +kernel

-- Software `code` fields carried in the constructors, and the jr/jalr hint values (see `decode`'s docstring).
example : allTrue [
    decode 0x42000020#32 == some (.wait 0#32),  -- wait, code 0
    decode 0x43ffffe0#32 == some (.wait 0x7ffff#32),  -- wait, code all ones
    decode 0x40000020#32 == none,  -- CO bit clear
    decode (mkRT 0#32 0#32 0#32 0x1f#32 0x0f#32) == some (.sync 0x1f#32),  -- sync stype
    decode (mkRT 0x1f#32 0x1f#32 0x1f#32 0x1f#32 0x0c#32) == some (.syscall 0xfffff#32),  -- syscall code
    decode (mkRT 0x1f#32 0x1f#32 0x1f#32 0x1f#32 0x0d#32) == some (.break 0xfffff#32),  -- break code
    decode (mkRT 29#32 8#32 0x1f#32 0x1f#32 0x34#32) == some (.teq 29#32 8#32 0x3ff#32),  -- trap code
    decode (mkRT 29#32 0#32 0#32 0x10#32 0x08#32) == none,  -- removed in R6 (was `jrHb`)
    decode (mkRT 29#32 0#32 31#32 0x10#32 0x09#32) == some (.jalrHb 29#32 31#32),  -- jalr.hb
    decode (mkRT 29#32 0#32 0#32 0x11#32 0x08#32) == none,  -- jr, hint 17
    decode (mkRT 29#32 0#32 31#32 0x01#32 0x09#32) == none,  -- jalr, hint 1
    -- `nop` / `ssnop` / `ehb` are `sll $0,$0,{0,1,3}`.
    decode 0x00000000#32 == some (.sll 0#32 0#32 0#32),
    decode 0x00000040#32 == some (.sll 0#32 0#32 1#32),
    decode 0x000000c0#32 == some (.sll 0#32 0#32 3#32)
  ] := by decide +kernel

-- ## Tests: FCSR-era additions (cc fields, signaling compares, new instructions)

-- `C.cond.fmt` is removed in Release 6 (replaced by CMP.condn.fmt, R6-6): its words decode to `none`
example : allTrue [
    decode 0x46062832#32 == none,  -- removed in R6 (was `cCondS`)
    decode 0x46262f3a#32 == none,  -- removed in R6 (was `cCondD`)
    -- bits 7..6 of a compare must be zero
    decode 0x46062872#32 == none,
    decode 0x460628b2#32 == none
  ] := by decide +kernel

-- words hand-assembled from the field layouts on the manual pages (the conditional moves and the
-- COP1X instructions are removed in Release 6)
example : allTrue [
    decode 0x0085100a#32 == none,  -- removed in R6 (was `movz`)
    decode 0x00801001#32 == none,  -- removed in R6 (was `movf`)
    decode 0x009d1001#32 == none,  -- removed in R6 (was `movt`)
    decode 0x46002091#32 == none,  -- removed in R6 (was `movfS`)
    decode 0x463d2091#32 == none,  -- removed in R6 (was `movtD`)
    decode 0x46052093#32 == none,  -- removed in R6 (was `movnS`)
    decode 0x46252092#32 == none,  -- removed in R6 (was `movzD`)
    decode 0x44682000#32 == some (.mfhc1 8#32 4#32),  -- mfhc1 $8,$f4
    decode 0x44e82000#32 == some (.mthc1 8#32 4#32),  -- mthc1 $8,$f4
    decode 0x4c850080#32 == none,  -- removed in R6 (was `lwxc1`)
    decode 0x4c850081#32 == none,  -- removed in R6 (was `ldxc1`)
    decode 0x4c851008#32 == none,  -- removed in R6 (was `swxc1`)
    decode 0x4c851009#32 == none,  -- removed in R6 (was `sdxc1`)
    decode 0x4c85080f#32 == none,  -- removed in R6 (was `prefx`)
    decode 0x4c8628a0#32 == none,  -- removed in R6 (was `maddS`)
    decode 0x4c8628a9#32 == none,  -- removed in R6 (was `msubD`)
    decode 0x4c8628b0#32 == none,  -- removed in R6 (was `nmaddS`)
    decode 0x4c8628b9#32 == none,  -- removed in R6 (was `nmsubD`)
    decode 0x46002095#32 == some (.recipS 2#32 4#32),  -- recip.s $f2,$f4
    decode 0x46202096#32 == some (.rsqrtD 2#32 4#32),  -- rsqrt.d $f2,$f4
    decode 0x4620208c#32 == some (.roundWD 2#32 4#32),  -- round.w.d
    decode 0x4620208d#32 == some (.truncWD 2#32 4#32),
    decode 0x4620208e#32 == some (.ceilWD 2#32 4#32),
    decode 0x4620208f#32 == some (.floorWD 2#32 4#32),
    decode 0x7c810835#32 == some (.pref 4#32 1#32 16#32),  -- pref 1,16($4)
    -- Longword conversions (words from llvm-mc-21 -mcpu=mips32r6), decode and round trip
    decode 0x460020a5#32 == some (.cvtLS 2#32 4#32),  -- cvt.l.s $f2,$f4
    encode (.cvtLS 2#32 4#32) == 0x460020a5#32,
    decode (encode (.cvtLS 31#32 17#32)) == some (.cvtLS 31#32 17#32),
    decode 0x462020a5#32 == some (.cvtLD 2#32 4#32),  -- cvt.l.d $f2,$f4
    encode (.cvtLD 2#32 4#32) == 0x462020a5#32,
    decode (encode (.cvtLD 31#32 17#32)) == some (.cvtLD 31#32 17#32),
    decode 0x46002088#32 == some (.roundLS 2#32 4#32),  -- round.l.s $f2,$f4
    encode (.roundLS 2#32 4#32) == 0x46002088#32,
    decode (encode (.roundLS 31#32 17#32)) == some (.roundLS 31#32 17#32),
    decode 0x46202088#32 == some (.roundLD 2#32 4#32),  -- round.l.d $f2,$f4
    encode (.roundLD 2#32 4#32) == 0x46202088#32,
    decode (encode (.roundLD 31#32 17#32)) == some (.roundLD 31#32 17#32),
    decode 0x46002089#32 == some (.truncLS 2#32 4#32),  -- trunc.l.s $f2,$f4
    encode (.truncLS 2#32 4#32) == 0x46002089#32,
    decode (encode (.truncLS 31#32 17#32)) == some (.truncLS 31#32 17#32),
    decode 0x46202089#32 == some (.truncLD 2#32 4#32),  -- trunc.l.d $f2,$f4
    encode (.truncLD 2#32 4#32) == 0x46202089#32,
    decode (encode (.truncLD 31#32 17#32)) == some (.truncLD 31#32 17#32),
    decode 0x4600208a#32 == some (.ceilLS 2#32 4#32),  -- ceil.l.s $f2,$f4
    encode (.ceilLS 2#32 4#32) == 0x4600208a#32,
    decode (encode (.ceilLS 31#32 17#32)) == some (.ceilLS 31#32 17#32),
    decode 0x4620208a#32 == some (.ceilLD 2#32 4#32),  -- ceil.l.d $f2,$f4
    encode (.ceilLD 2#32 4#32) == 0x4620208a#32,
    decode (encode (.ceilLD 31#32 17#32)) == some (.ceilLD 31#32 17#32),
    decode 0x4600208b#32 == some (.floorLS 2#32 4#32),  -- floor.l.s $f2,$f4
    encode (.floorLS 2#32 4#32) == 0x4600208b#32,
    decode (encode (.floorLS 31#32 17#32)) == some (.floorLS 31#32 17#32),
    decode 0x4620208b#32 == some (.floorLD 2#32 4#32),  -- floor.l.d $f2,$f4
    encode (.floorLD 2#32 4#32) == 0x4620208b#32,
    decode (encode (.floorLD 31#32 17#32)) == some (.floorLD 31#32 17#32),
    decode 0x46a020a0#32 == some (.cvtSL 2#32 4#32),  -- cvt.s.l $f2,$f4
    encode (.cvtSL 2#32 4#32) == 0x46a020a0#32,
    decode (encode (.cvtSL 31#32 17#32)) == some (.cvtSL 31#32 17#32),
    decode 0x46a020a1#32 == some (.cvtDL 2#32 4#32),  -- cvt.d.l $f2,$f4
    encode (.cvtDL 2#32 4#32) == 0x46a020a1#32,
    decode (encode (.cvtDL 31#32 17#32)) == some (.cvtDL 31#32 17#32),
    -- the L format is not defined for the arithmetic operations or for CVT.W/CVT.L: reserved
    -- R6-6B: fmt L function 0 is CMP.AF.D (Table A.17, p.457), no longer a reserved `add.l`
    decode 0x46a02080#32 == some (.cmpD 0#32 2#32 4#32 0#32),  -- cmp.af.d $f2,$f4,$f0
    decode 0x46a020a4#32 == none,  -- cvt.w.l
    decode 0x46a020a5#32 == none,  -- cvt.l.l
    -- The Release 6 FP instructions (words: llvm-mc -mcpu=mips32r6; the negated CMP condns from the
    -- CMP.condn.fmt diagram, p.136, and Table A.17, p.457)
    decode 0x46831040#32 == some (.cmpS 0#32 1#32 2#32 3#32),  -- cmp.af.s $f1, $f2, $f3
    encode (.cmpS 0#32 1#32 2#32 3#32) == 0x46831040#32,
    decode (encode (.cmpS 0#32 31#32 17#32 9#32)) == some (.cmpS 0#32 31#32 17#32 9#32),
    decode 0x46a31040#32 == some (.cmpD 0#32 1#32 2#32 3#32),  -- cmp.af.d $f1, $f2, $f3
    encode (.cmpD 0#32 1#32 2#32 3#32) == 0x46a31040#32,
    decode (encode (.cmpD 0#32 31#32 17#32 9#32)) == some (.cmpD 0#32 31#32 17#32 9#32),
    decode 0x46831041#32 == some (.cmpS 1#32 1#32 2#32 3#32),  -- cmp.un.s $f1, $f2, $f3
    encode (.cmpS 1#32 1#32 2#32 3#32) == 0x46831041#32,
    decode (encode (.cmpS 1#32 31#32 17#32 9#32)) == some (.cmpS 1#32 31#32 17#32 9#32),
    decode 0x46a31041#32 == some (.cmpD 1#32 1#32 2#32 3#32),  -- cmp.un.d $f1, $f2, $f3
    encode (.cmpD 1#32 1#32 2#32 3#32) == 0x46a31041#32,
    decode (encode (.cmpD 1#32 31#32 17#32 9#32)) == some (.cmpD 1#32 31#32 17#32 9#32),
    decode 0x46831042#32 == some (.cmpS 2#32 1#32 2#32 3#32),  -- cmp.eq.s $f1, $f2, $f3
    encode (.cmpS 2#32 1#32 2#32 3#32) == 0x46831042#32,
    decode (encode (.cmpS 2#32 31#32 17#32 9#32)) == some (.cmpS 2#32 31#32 17#32 9#32),
    decode 0x46a31042#32 == some (.cmpD 2#32 1#32 2#32 3#32),  -- cmp.eq.d $f1, $f2, $f3
    encode (.cmpD 2#32 1#32 2#32 3#32) == 0x46a31042#32,
    decode (encode (.cmpD 2#32 31#32 17#32 9#32)) == some (.cmpD 2#32 31#32 17#32 9#32),
    decode 0x46831043#32 == some (.cmpS 3#32 1#32 2#32 3#32),  -- cmp.ueq.s $f1, $f2, $f3
    encode (.cmpS 3#32 1#32 2#32 3#32) == 0x46831043#32,
    decode (encode (.cmpS 3#32 31#32 17#32 9#32)) == some (.cmpS 3#32 31#32 17#32 9#32),
    decode 0x46a31043#32 == some (.cmpD 3#32 1#32 2#32 3#32),  -- cmp.ueq.d $f1, $f2, $f3
    encode (.cmpD 3#32 1#32 2#32 3#32) == 0x46a31043#32,
    decode (encode (.cmpD 3#32 31#32 17#32 9#32)) == some (.cmpD 3#32 31#32 17#32 9#32),
    decode 0x46831044#32 == some (.cmpS 4#32 1#32 2#32 3#32),  -- cmp.lt.s $f1, $f2, $f3
    encode (.cmpS 4#32 1#32 2#32 3#32) == 0x46831044#32,
    decode (encode (.cmpS 4#32 31#32 17#32 9#32)) == some (.cmpS 4#32 31#32 17#32 9#32),
    decode 0x46a31044#32 == some (.cmpD 4#32 1#32 2#32 3#32),  -- cmp.lt.d $f1, $f2, $f3
    encode (.cmpD 4#32 1#32 2#32 3#32) == 0x46a31044#32,
    decode (encode (.cmpD 4#32 31#32 17#32 9#32)) == some (.cmpD 4#32 31#32 17#32 9#32),
    decode 0x46831045#32 == some (.cmpS 5#32 1#32 2#32 3#32),  -- cmp.ult.s $f1, $f2, $f3
    encode (.cmpS 5#32 1#32 2#32 3#32) == 0x46831045#32,
    decode (encode (.cmpS 5#32 31#32 17#32 9#32)) == some (.cmpS 5#32 31#32 17#32 9#32),
    decode 0x46a31045#32 == some (.cmpD 5#32 1#32 2#32 3#32),  -- cmp.ult.d $f1, $f2, $f3
    encode (.cmpD 5#32 1#32 2#32 3#32) == 0x46a31045#32,
    decode (encode (.cmpD 5#32 31#32 17#32 9#32)) == some (.cmpD 5#32 31#32 17#32 9#32),
    decode 0x46831046#32 == some (.cmpS 6#32 1#32 2#32 3#32),  -- cmp.le.s $f1, $f2, $f3
    encode (.cmpS 6#32 1#32 2#32 3#32) == 0x46831046#32,
    decode (encode (.cmpS 6#32 31#32 17#32 9#32)) == some (.cmpS 6#32 31#32 17#32 9#32),
    decode 0x46a31046#32 == some (.cmpD 6#32 1#32 2#32 3#32),  -- cmp.le.d $f1, $f2, $f3
    encode (.cmpD 6#32 1#32 2#32 3#32) == 0x46a31046#32,
    decode (encode (.cmpD 6#32 31#32 17#32 9#32)) == some (.cmpD 6#32 31#32 17#32 9#32),
    decode 0x46831047#32 == some (.cmpS 7#32 1#32 2#32 3#32),  -- cmp.ule.s $f1, $f2, $f3
    encode (.cmpS 7#32 1#32 2#32 3#32) == 0x46831047#32,
    decode (encode (.cmpS 7#32 31#32 17#32 9#32)) == some (.cmpS 7#32 31#32 17#32 9#32),
    decode 0x46a31047#32 == some (.cmpD 7#32 1#32 2#32 3#32),  -- cmp.ule.d $f1, $f2, $f3
    encode (.cmpD 7#32 1#32 2#32 3#32) == 0x46a31047#32,
    decode (encode (.cmpD 7#32 31#32 17#32 9#32)) == some (.cmpD 7#32 31#32 17#32 9#32),
    decode 0x46831048#32 == some (.cmpS 8#32 1#32 2#32 3#32),  -- cmp.saf.s $f1, $f2, $f3
    encode (.cmpS 8#32 1#32 2#32 3#32) == 0x46831048#32,
    decode (encode (.cmpS 8#32 31#32 17#32 9#32)) == some (.cmpS 8#32 31#32 17#32 9#32),
    decode 0x46a31048#32 == some (.cmpD 8#32 1#32 2#32 3#32),  -- cmp.saf.d $f1, $f2, $f3
    encode (.cmpD 8#32 1#32 2#32 3#32) == 0x46a31048#32,
    decode (encode (.cmpD 8#32 31#32 17#32 9#32)) == some (.cmpD 8#32 31#32 17#32 9#32),
    decode 0x46831049#32 == some (.cmpS 9#32 1#32 2#32 3#32),  -- cmp.sun.s $f1, $f2, $f3
    encode (.cmpS 9#32 1#32 2#32 3#32) == 0x46831049#32,
    decode (encode (.cmpS 9#32 31#32 17#32 9#32)) == some (.cmpS 9#32 31#32 17#32 9#32),
    decode 0x46a31049#32 == some (.cmpD 9#32 1#32 2#32 3#32),  -- cmp.sun.d $f1, $f2, $f3
    encode (.cmpD 9#32 1#32 2#32 3#32) == 0x46a31049#32,
    decode (encode (.cmpD 9#32 31#32 17#32 9#32)) == some (.cmpD 9#32 31#32 17#32 9#32),
    decode 0x4683104a#32 == some (.cmpS 10#32 1#32 2#32 3#32),  -- cmp.seq.s $f1, $f2, $f3
    encode (.cmpS 10#32 1#32 2#32 3#32) == 0x4683104a#32,
    decode (encode (.cmpS 10#32 31#32 17#32 9#32)) == some (.cmpS 10#32 31#32 17#32 9#32),
    decode 0x46a3104a#32 == some (.cmpD 10#32 1#32 2#32 3#32),  -- cmp.seq.d $f1, $f2, $f3
    encode (.cmpD 10#32 1#32 2#32 3#32) == 0x46a3104a#32,
    decode (encode (.cmpD 10#32 31#32 17#32 9#32)) == some (.cmpD 10#32 31#32 17#32 9#32),
    decode 0x4683104b#32 == some (.cmpS 11#32 1#32 2#32 3#32),  -- cmp.sueq.s $f1, $f2, $f3
    encode (.cmpS 11#32 1#32 2#32 3#32) == 0x4683104b#32,
    decode (encode (.cmpS 11#32 31#32 17#32 9#32)) == some (.cmpS 11#32 31#32 17#32 9#32),
    decode 0x46a3104b#32 == some (.cmpD 11#32 1#32 2#32 3#32),  -- cmp.sueq.d $f1, $f2, $f3
    encode (.cmpD 11#32 1#32 2#32 3#32) == 0x46a3104b#32,
    decode (encode (.cmpD 11#32 31#32 17#32 9#32)) == some (.cmpD 11#32 31#32 17#32 9#32),
    decode 0x4683104c#32 == some (.cmpS 12#32 1#32 2#32 3#32),  -- cmp.slt.s $f1, $f2, $f3
    encode (.cmpS 12#32 1#32 2#32 3#32) == 0x4683104c#32,
    decode (encode (.cmpS 12#32 31#32 17#32 9#32)) == some (.cmpS 12#32 31#32 17#32 9#32),
    decode 0x46a3104c#32 == some (.cmpD 12#32 1#32 2#32 3#32),  -- cmp.slt.d $f1, $f2, $f3
    encode (.cmpD 12#32 1#32 2#32 3#32) == 0x46a3104c#32,
    decode (encode (.cmpD 12#32 31#32 17#32 9#32)) == some (.cmpD 12#32 31#32 17#32 9#32),
    decode 0x4683104d#32 == some (.cmpS 13#32 1#32 2#32 3#32),  -- cmp.sult.s $f1, $f2, $f3
    encode (.cmpS 13#32 1#32 2#32 3#32) == 0x4683104d#32,
    decode (encode (.cmpS 13#32 31#32 17#32 9#32)) == some (.cmpS 13#32 31#32 17#32 9#32),
    decode 0x46a3104d#32 == some (.cmpD 13#32 1#32 2#32 3#32),  -- cmp.sult.d $f1, $f2, $f3
    encode (.cmpD 13#32 1#32 2#32 3#32) == 0x46a3104d#32,
    decode (encode (.cmpD 13#32 31#32 17#32 9#32)) == some (.cmpD 13#32 31#32 17#32 9#32),
    decode 0x4683104e#32 == some (.cmpS 14#32 1#32 2#32 3#32),  -- cmp.sle.s $f1, $f2, $f3
    encode (.cmpS 14#32 1#32 2#32 3#32) == 0x4683104e#32,
    decode (encode (.cmpS 14#32 31#32 17#32 9#32)) == some (.cmpS 14#32 31#32 17#32 9#32),
    decode 0x46a3104e#32 == some (.cmpD 14#32 1#32 2#32 3#32),  -- cmp.sle.d $f1, $f2, $f3
    encode (.cmpD 14#32 1#32 2#32 3#32) == 0x46a3104e#32,
    decode (encode (.cmpD 14#32 31#32 17#32 9#32)) == some (.cmpD 14#32 31#32 17#32 9#32),
    decode 0x4683104f#32 == some (.cmpS 15#32 1#32 2#32 3#32),  -- cmp.sule.s $f1, $f2, $f3
    encode (.cmpS 15#32 1#32 2#32 3#32) == 0x4683104f#32,
    decode (encode (.cmpS 15#32 31#32 17#32 9#32)) == some (.cmpS 15#32 31#32 17#32 9#32),
    decode 0x46a3104f#32 == some (.cmpD 15#32 1#32 2#32 3#32),  -- cmp.sule.d $f1, $f2, $f3
    encode (.cmpD 15#32 1#32 2#32 3#32) == 0x46a3104f#32,
    decode (encode (.cmpD 15#32 31#32 17#32 9#32)) == some (.cmpD 15#32 31#32 17#32 9#32),
    decode 0x46831051#32 == some (.cmpS 17#32 1#32 2#32 3#32),  -- cmp.or.s $f1, $f2, $f3
    encode (.cmpS 17#32 1#32 2#32 3#32) == 0x46831051#32,
    decode (encode (.cmpS 17#32 31#32 17#32 9#32)) == some (.cmpS 17#32 31#32 17#32 9#32),
    decode 0x46a31051#32 == some (.cmpD 17#32 1#32 2#32 3#32),  -- cmp.or.d $f1, $f2, $f3
    encode (.cmpD 17#32 1#32 2#32 3#32) == 0x46a31051#32,
    decode (encode (.cmpD 17#32 31#32 17#32 9#32)) == some (.cmpD 17#32 31#32 17#32 9#32),
    decode 0x46831052#32 == some (.cmpS 18#32 1#32 2#32 3#32),  -- cmp.une.s $f1, $f2, $f3
    encode (.cmpS 18#32 1#32 2#32 3#32) == 0x46831052#32,
    decode (encode (.cmpS 18#32 31#32 17#32 9#32)) == some (.cmpS 18#32 31#32 17#32 9#32),
    decode 0x46a31052#32 == some (.cmpD 18#32 1#32 2#32 3#32),  -- cmp.une.d $f1, $f2, $f3
    encode (.cmpD 18#32 1#32 2#32 3#32) == 0x46a31052#32,
    decode (encode (.cmpD 18#32 31#32 17#32 9#32)) == some (.cmpD 18#32 31#32 17#32 9#32),
    decode 0x46831053#32 == some (.cmpS 19#32 1#32 2#32 3#32),  -- cmp.ne.s $f1, $f2, $f3
    encode (.cmpS 19#32 1#32 2#32 3#32) == 0x46831053#32,
    decode (encode (.cmpS 19#32 31#32 17#32 9#32)) == some (.cmpS 19#32 31#32 17#32 9#32),
    decode 0x46a31053#32 == some (.cmpD 19#32 1#32 2#32 3#32),  -- cmp.ne.d $f1, $f2, $f3
    encode (.cmpD 19#32 1#32 2#32 3#32) == 0x46a31053#32,
    decode (encode (.cmpD 19#32 31#32 17#32 9#32)) == some (.cmpD 19#32 31#32 17#32 9#32),
    decode 0x46831059#32 == some (.cmpS 25#32 1#32 2#32 3#32),  -- cmp.sor.s $f1, $f2, $f3
    encode (.cmpS 25#32 1#32 2#32 3#32) == 0x46831059#32,
    decode (encode (.cmpS 25#32 31#32 17#32 9#32)) == some (.cmpS 25#32 31#32 17#32 9#32),
    decode 0x46a31059#32 == some (.cmpD 25#32 1#32 2#32 3#32),  -- cmp.sor.d $f1, $f2, $f3
    encode (.cmpD 25#32 1#32 2#32 3#32) == 0x46a31059#32,
    decode (encode (.cmpD 25#32 31#32 17#32 9#32)) == some (.cmpD 25#32 31#32 17#32 9#32),
    decode 0x4683105a#32 == some (.cmpS 26#32 1#32 2#32 3#32),  -- cmp.sune.s $f1, $f2, $f3
    encode (.cmpS 26#32 1#32 2#32 3#32) == 0x4683105a#32,
    decode (encode (.cmpS 26#32 31#32 17#32 9#32)) == some (.cmpS 26#32 31#32 17#32 9#32),
    decode 0x46a3105a#32 == some (.cmpD 26#32 1#32 2#32 3#32),  -- cmp.sune.d $f1, $f2, $f3
    encode (.cmpD 26#32 1#32 2#32 3#32) == 0x46a3105a#32,
    decode (encode (.cmpD 26#32 31#32 17#32 9#32)) == some (.cmpD 26#32 31#32 17#32 9#32),
    decode 0x4683105b#32 == some (.cmpS 27#32 1#32 2#32 3#32),  -- cmp.sne.s $f1, $f2, $f3
    encode (.cmpS 27#32 1#32 2#32 3#32) == 0x4683105b#32,
    decode (encode (.cmpS 27#32 31#32 17#32 9#32)) == some (.cmpS 27#32 31#32 17#32 9#32),
    decode 0x46a3105b#32 == some (.cmpD 27#32 1#32 2#32 3#32),  -- cmp.sne.d $f1, $f2, $f3
    encode (.cmpD 27#32 1#32 2#32 3#32) == 0x46a3105b#32,
    decode (encode (.cmpD 27#32 31#32 17#32 9#32)) == some (.cmpD 27#32 31#32 17#32 9#32),
    decode 0x46031050#32 == some (.selS 1#32 2#32 3#32),  -- sel.s $f1, $f2, $f3
    encode (.selS 1#32 2#32 3#32) == 0x46031050#32,
    decode (encode (.selS 31#32 17#32 9#32)) == some (.selS 31#32 17#32 9#32),
    decode 0x46231050#32 == some (.selD 1#32 2#32 3#32),  -- sel.d $f1, $f2, $f3
    encode (.selD 1#32 2#32 3#32) == 0x46231050#32,
    decode (encode (.selD 31#32 17#32 9#32)) == some (.selD 31#32 17#32 9#32),
    decode 0x46031054#32 == some (.seleqzS 1#32 2#32 3#32),  -- seleqz.s $f1, $f2, $f3
    encode (.seleqzS 1#32 2#32 3#32) == 0x46031054#32,
    decode (encode (.seleqzS 31#32 17#32 9#32)) == some (.seleqzS 31#32 17#32 9#32),
    decode 0x46231054#32 == some (.seleqzD 1#32 2#32 3#32),  -- seleqz.d $f1, $f2, $f3
    encode (.seleqzD 1#32 2#32 3#32) == 0x46231054#32,
    decode (encode (.seleqzD 31#32 17#32 9#32)) == some (.seleqzD 31#32 17#32 9#32),
    decode 0x46031057#32 == some (.selnezS 1#32 2#32 3#32),  -- selnez.s $f1, $f2, $f3
    encode (.selnezS 1#32 2#32 3#32) == 0x46031057#32,
    decode (encode (.selnezS 31#32 17#32 9#32)) == some (.selnezS 31#32 17#32 9#32),
    decode 0x46231057#32 == some (.selnezD 1#32 2#32 3#32),  -- selnez.d $f1, $f2, $f3
    encode (.selnezD 1#32 2#32 3#32) == 0x46231057#32,
    decode (encode (.selnezD 31#32 17#32 9#32)) == some (.selnezD 31#32 17#32 9#32),
    decode 0x46031058#32 == some (.maddfS 1#32 2#32 3#32),  -- maddf.s $f1, $f2, $f3
    encode (.maddfS 1#32 2#32 3#32) == 0x46031058#32,
    decode (encode (.maddfS 31#32 17#32 9#32)) == some (.maddfS 31#32 17#32 9#32),
    decode 0x46231058#32 == some (.maddfD 1#32 2#32 3#32),  -- maddf.d $f1, $f2, $f3
    encode (.maddfD 1#32 2#32 3#32) == 0x46231058#32,
    decode (encode (.maddfD 31#32 17#32 9#32)) == some (.maddfD 31#32 17#32 9#32),
    decode 0x46031059#32 == some (.msubfS 1#32 2#32 3#32),  -- msubf.s $f1, $f2, $f3
    encode (.msubfS 1#32 2#32 3#32) == 0x46031059#32,
    decode (encode (.msubfS 31#32 17#32 9#32)) == some (.msubfS 31#32 17#32 9#32),
    decode 0x46231059#32 == some (.msubfD 1#32 2#32 3#32),  -- msubf.d $f1, $f2, $f3
    encode (.msubfD 1#32 2#32 3#32) == 0x46231059#32,
    decode (encode (.msubfD 31#32 17#32 9#32)) == some (.msubfD 31#32 17#32 9#32),
    decode 0x4603105e#32 == some (.maxS 1#32 2#32 3#32),  -- max.s $f1, $f2, $f3
    encode (.maxS 1#32 2#32 3#32) == 0x4603105e#32,
    decode (encode (.maxS 31#32 17#32 9#32)) == some (.maxS 31#32 17#32 9#32),
    decode 0x4623105e#32 == some (.maxD 1#32 2#32 3#32),  -- max.d $f1, $f2, $f3
    encode (.maxD 1#32 2#32 3#32) == 0x4623105e#32,
    decode (encode (.maxD 31#32 17#32 9#32)) == some (.maxD 31#32 17#32 9#32),
    decode 0x4603105c#32 == some (.minS 1#32 2#32 3#32),  -- min.s $f1, $f2, $f3
    encode (.minS 1#32 2#32 3#32) == 0x4603105c#32,
    decode (encode (.minS 31#32 17#32 9#32)) == some (.minS 31#32 17#32 9#32),
    decode 0x4623105c#32 == some (.minD 1#32 2#32 3#32),  -- min.d $f1, $f2, $f3
    encode (.minD 1#32 2#32 3#32) == 0x4623105c#32,
    decode (encode (.minD 31#32 17#32 9#32)) == some (.minD 31#32 17#32 9#32),
    decode 0x4603105f#32 == some (.maxaS 1#32 2#32 3#32),  -- maxa.s $f1, $f2, $f3
    encode (.maxaS 1#32 2#32 3#32) == 0x4603105f#32,
    decode (encode (.maxaS 31#32 17#32 9#32)) == some (.maxaS 31#32 17#32 9#32),
    decode 0x4623105f#32 == some (.maxaD 1#32 2#32 3#32),  -- maxa.d $f1, $f2, $f3
    encode (.maxaD 1#32 2#32 3#32) == 0x4623105f#32,
    decode (encode (.maxaD 31#32 17#32 9#32)) == some (.maxaD 31#32 17#32 9#32),
    decode 0x4603105d#32 == some (.minaS 1#32 2#32 3#32),  -- mina.s $f1, $f2, $f3
    encode (.minaS 1#32 2#32 3#32) == 0x4603105d#32,
    decode (encode (.minaS 31#32 17#32 9#32)) == some (.minaS 31#32 17#32 9#32),
    decode 0x4623105d#32 == some (.minaD 1#32 2#32 3#32),  -- mina.d $f1, $f2, $f3
    encode (.minaD 1#32 2#32 3#32) == 0x4623105d#32,
    decode (encode (.minaD 31#32 17#32 9#32)) == some (.minaD 31#32 17#32 9#32),
    decode 0x4600105b#32 == some (.classS 1#32 2#32),  -- class.s $f1, $f2
    encode (.classS 1#32 2#32) == 0x4600105b#32,
    decode (encode (.classS 31#32 17#32)) == some (.classS 31#32 17#32),
    decode 0x4620105b#32 == some (.classD 1#32 2#32),  -- class.d $f1, $f2
    encode (.classD 1#32 2#32) == 0x4620105b#32,
    decode (encode (.classD 31#32 17#32)) == some (.classD 31#32 17#32),
    decode 0x4600105a#32 == some (.rintS 1#32 2#32),  -- rint.s $f1, $f2
    encode (.rintS 1#32 2#32) == 0x4600105a#32,
    decode (encode (.rintS 31#32 17#32)) == some (.rintS 31#32 17#32),
    decode 0x4620105a#32 == some (.rintD 1#32 2#32),  -- rint.d $f1, $f2
    encode (.rintD 1#32 2#32) == 0x4620105a#32,
    decode (encode (.rintD 31#32 17#32)) == some (.rintD 31#32 17#32),
    decode 0x45230002#32 == some (.bc1eqz 3#32 2#32),  -- bc1eqz $f3, 8
    encode (.bc1eqz 3#32 2#32) == 0x45230002#32,
    decode 0x45bfffff#32 == some (.bc1nez 31#32 0xffff#32),  -- bc1nez $f31, -4
    encode (.bc1nez 31#32 0xffff#32) == 0x45bfffff#32,
    decode (encode (.bc1eqz 17#32 0x8000#32)) == some (.bc1eqz 17#32 0x8000#32),
    -- reserved CMP condn values (16, 20..24, 28..31) do not decode; bit 5 set is no CMP
    decode 0x46831050#32 == none,
    decode 0x46831054#32 == none,
    decode 0x46831055#32 == none,
    decode 0x46831056#32 == none,
    decode 0x46831057#32 == none,
    decode 0x46831058#32 == none,
    decode 0x4683105c#32 == none,
    decode 0x4683105d#32 == none,
    decode 0x4683105e#32 == none,
    decode 0x4683105f#32 == none,
    decode 0x46a31050#32 == none,
    decode 0x46a31058#32 == none,
    decode 0x46a3105f#32 == none,
    decode 0x46831062#32 == none,  -- fmt W function 100010
    -- RINT/CLASS with ft ≠ 0 do not decode
    decode 0x4603105a#32 == none,
    decode 0x4623105b#32 == none,
    encode (.pref 4#32 1#32 16#32) == 0x7c810835#32,
    decode 0xcc810010#32 == none,  -- pre-R6 PREF (0x33)
    decode 0x41606000#32 == some (.di 0#32),  -- di
    decode 0x41686020#32 == some (.ei 8#32),  -- ei $8
    decode 0x41686800#32 == none,  -- MFMC0, rd ≠ 12
    -- dvp / evp (DVP p.172, EVP p.181; words from llvm-mc -mcpu=mips32r6)
    decode 0x41680024#32 == some (.dvp 8#32),  -- dvp $8
    decode 0x41600004#32 == some (.evp 0#32),  -- evp
    decode (encode (.dvp 31#32)) == some (.dvp 31#32),
    decode (encode (.evp 17#32)) == some (.evp 17#32),
    decode 0x41680824#32 == none,  -- dvp, rd ≠ 0
    decode 0x41680064#32 == none,  -- dvp, bits 10..6 ≠ 0
    decode 0x4168002c#32 == none,  -- dvp, bits 4..3 ≠ 0
    -- Coverage audit (Wave R6-7): encodings of pages outside the profile do not decode (Reserved
    -- Instruction, or Coprocessor Unusable by encoding space; words from llvm-mc-21 / the page diagrams).
    decode 0x42000008#32 == none,  -- tlbp     (Fixed Mapping MMU, TLBP p.427)
    decode 0x42000001#32 == none,  -- tlbr     (TLBR p.428)
    decode 0x42000002#32 == none,  -- tlbwi    (TLBWI p.430)
    decode 0x42000006#32 == none,  -- tlbwr    (TLBWR p.432)
    decode 0x42000003#32 == none,  -- tlbinv   (TLBINV p.423)
    decode 0x42000004#32 == none,  -- tlbinvf  (TLBINVF p.426)
    decode 0x4200001f#32 == none,  -- deret    (EJTAG absent, DERET p.163)
    decode 0x0000000e#32 == none,  -- sdbbp    (EJTAG absent, SDBBP p.361)
    decode 0x40486000#32 == none,  -- mfhc0    (Config5.MVH = 0, MFHC0 p.270)
    decode 0x40c86000#32 == none,  -- mthc0    (Config5.MVH = 0, MTHC0 p.294)
    decode 0x7d484876#32 == none,  -- llwp     (Config5.XNP = 1, LLWP p.228)
    decode 0x7d484866#32 == none,  -- scwp     (Config5.XNP = 1, SCWP p.355)
    decode 0x7d28002f#32 == none,  -- lwe      (EVA absent, LWE p.239)
    decode 0x7d01001b#32 == none,  -- cachee   (EVA absent, CACHEE p.121)
    decode 0x7d28008f#32 == none,  -- crc32w   (CRC absent, p.143)
    decode 0x7d00003d#32 == none,  -- ginvi    (GINV absent, GINVI p.187)
    decode 0x7d0000bd#32 == none,  -- ginvt    (GINVT p.189)
    decode 0x4a000001#32 == none,  -- cop2     (no coprocessor 2, COP2 p.141)
    decode 0x49220002#32 == none,  -- bc2eqz   (BC2EQZ p.64)
    decode 0x0109001e#32 == none,  -- ddiv     (MIPS64, DDIV p.161)
    decode 0x74100000#32 == none,  -- jalx     (removed, JALX p.201)
    decode 0x40087801#32 == some (.mfc0 8#32 15#32 1#32),  -- mfc0 $8,$15,1 (EBase)
    decode 0x40888001#32 == some (.mtc0 8#32 16#32 1#32),  -- mtc0 $8,$16,1 (Config1)
    decode 0x40087800#32 == some (.mfc0 8#32 15#32 0#32),  -- PRId
    decode 0x40088002#32 == some (.mfc0 8#32 16#32 2#32),  -- mfc0 $8,$16,2 (Config2)
    decode 0x40888003#32 == some (.mtc0 8#32 16#32 3#32),  -- mtc0 $8,$16,3 (Config3)
    decode 0x40088004#32 == some (.mfc0 8#32 16#32 4#32),  -- Config4 (Release 6)
    decode 0x40087002#32 == some (.mfc0 8#32 14#32 2#32),  -- (14,2): reads 0
    decode 0x0000000c#32 == some (.syscall 0#32),
    decode 0x0001234d#32 == some (.break 0x48d#32),  -- code 0x48d = 1165
    decode 0x00a41df4#32 == some (.teq 5#32 4#32 0x77#32),  -- teq $5,$4,0x77
    -- round trips of the new shapes (every field at a non-trivial value)
    decode (encode (.syscall 0xabcde#32)) == some (.syscall 0xabcde#32),
    decode (encode (.break 0xfffff#32)) == some (.break 0xfffff#32),
    decode (encode (.tgeu 29#32 8#32 0x2aa#32)) == some (.tgeu 29#32 8#32 0x2aa#32),
    decode (encode (.sync 0x1f#32)) == some (.sync 0x1f#32),
    decode (encode (.wait 0x55555#32)) == some (.wait 0x55555#32),
    decode (encode (.pref 29#32 30#32 0x101#32)) == some (.pref 29#32 30#32 0x101#32),
    decode (encode (.di 9#32)) == some (.di 9#32),
    decode (encode (.ei 9#32)) == some (.ei 9#32),
    decode (encode (.mfc0 9#32 16#32 1#32)) == some (.mfc0 9#32 16#32 1#32),
    decode (encode (.mfhc1 8#32 4#32)) == some (.mfhc1 8#32 4#32),
    decode (encode (.mthc1 8#32 4#32)) == some (.mthc1 8#32 4#32),
    decode (encode (.recipD 2#32 4#32)) == some (.recipD 2#32 4#32),
    decode (encode (.rsqrtS 2#32 4#32)) == some (.rsqrtS 2#32 4#32),
    decode (encode (.floorWD 2#32 4#32)) == some (.floorWD 2#32 4#32),
    -- L-format conversions (fmt = L = 0x15, and cvt.l/round.l… functs) are modeled since R6-5
    decode 0x46a02020#32 == some (.cvtSL 0#32 4#32),  -- cvt.s.l $f0,$f4
    decode 0x46002025#32 == some (.cvtLS 0#32 4#32),  -- cvt.l.s $f0,$f4
    decode 0x46002008#32 == some (.roundLS 0#32 4#32),  -- round.l.s $f0,$f4
    -- paired-single (fmt = PS = 0x16) is not modeled
    decode 0x46c62000#32 == none  -- add.ps
  ] := by decide +kernel

/-! ## Release 6 encodings

The retained, renamed and new constructors with Release 6 words (MD00086 Vol II-A Rev 6.06), a
`decode (encode i) = some i` round trip for every constructor not covered above, and one guard per
removed opcode group not covered above (removed encodings decode to `none`). -/

-- `jr $5` is `jalr $0, $5` = 0x00a00009 (JR p.207: "JR is defined to be JALR with the destination
-- register specifier rd set to 0"); `jr.hb $5` is `jalr.hb $0, $5`.
example : allTrue [
    decode 0x00a00009#32 == some (.jalr 5#32 0#32),
    encode (.jalr 5#32 0#32) == 0x00a00009#32,
    decode 0x00a00409#32 == some (.jalrHb 5#32 0#32),
    -- the pre-Release 6 JR encoding (funct 0x08) is removed
    decode 0x00a00008#32 == none,
    decode 0x00a00408#32 == none,
    -- PAUSE = `sll $0, $0, 5` = 0x00000140 (PAUSE p.317); it is not an `sll`
    decode 0x00000140#32 == some .pause,
    encode .pause == 0x00000140#32,
    decode (mkRT 0#32 0#32 0#32 5#32 0x00#32) == some .pause,
    decode (mkRT 0#32 0#32 0#32 3#32 0x00#32) == some (.sll 0#32 0#32 3#32),  -- ehb
    decode (mkRT 0#32 1#32 0#32 5#32 0x00#32) == some (.sll 0#32 1#32 5#32),
    -- NAL = REGIMM rs = 0, rt = 0x10 (NAL p.306); BAL = REGIMM rs = 0, rt = 0x11 (BAL p.50)
    decode 0x04101234#32 == some (.nal 0x1234#32),
    decode 0x04111234#32 == some (.bal 0x1234#32),
    encode (.nal 0x1234#32) == 0x04101234#32,
    encode (.bal 0x1234#32) == 0x04111234#32,
    -- BLTZAL/BGEZAL with rs ≠ 0 are removed
    decode (mkIT 0x01#32 8#32 0x10#32 0x1234#32) == none,
    decode (mkIT 0x01#32 8#32 0x11#32 0x1234#32) == none
  ] := by decide +kernel

-- round trips (every constructor has one in this file)
example : allTrue [
    decode (encode .pause) == some .pause,
    decode (encode (.nal 0xffff#32)) == some (.nal 0xffff#32),
    decode (encode (.bal 0x8000#32)) == some (.bal 0x8000#32),
    decode (encode (.add 29#32 8#32 3#32)) == some (.add 29#32 8#32 3#32),
    decode (encode (.addu 29#32 8#32 3#32)) == some (.addu 29#32 8#32 3#32),
    decode (encode (.sub 29#32 8#32 3#32)) == some (.sub 29#32 8#32 3#32),
    decode (encode (.subu 29#32 8#32 3#32)) == some (.subu 29#32 8#32 3#32),
    decode (encode (.and 29#32 8#32 3#32)) == some (.and 29#32 8#32 3#32),
    decode (encode (.or 29#32 8#32 3#32)) == some (.or 29#32 8#32 3#32),
    decode (encode (.xor 29#32 8#32 3#32)) == some (.xor 29#32 8#32 3#32),
    decode (encode (.nor 29#32 8#32 3#32)) == some (.nor 29#32 8#32 3#32),
    decode (encode (.slt 29#32 8#32 3#32)) == some (.slt 29#32 8#32 3#32),
    decode (encode (.sltu 29#32 8#32 3#32)) == some (.sltu 29#32 8#32 3#32),
    decode (encode (.sll 3#32 8#32 5#32)) == some (.sll 3#32 8#32 5#32),
    decode (encode (.srl 3#32 8#32 5#32)) == some (.srl 3#32 8#32 5#32),
    decode (encode (.sra 3#32 8#32 5#32)) == some (.sra 3#32 8#32 5#32),
    decode (encode (.addiu 29#32 8#32 0x8001#32)) == some (.addiu 29#32 8#32 0x8001#32),
    decode (encode (.slti 29#32 8#32 0x8001#32)) == some (.slti 29#32 8#32 0x8001#32),
    decode (encode (.sltiu 29#32 8#32 0x8001#32)) == some (.sltiu 29#32 8#32 0x8001#32),
    decode (encode (.andi 29#32 8#32 0x8001#32)) == some (.andi 29#32 8#32 0x8001#32),
    decode (encode (.ori 29#32 8#32 0x8001#32)) == some (.ori 29#32 8#32 0x8001#32),
    decode (encode (.xori 29#32 8#32 0x8001#32)) == some (.xori 29#32 8#32 0x8001#32),
    decode (encode (.lw 29#32 8#32 0x8001#32)) == some (.lw 29#32 8#32 0x8001#32),
    decode (encode (.sw 29#32 8#32 0x8001#32)) == some (.sw 29#32 8#32 0x8001#32),
    decode (encode (.lb 29#32 8#32 0x8001#32)) == some (.lb 29#32 8#32 0x8001#32),
    decode (encode (.lbu 29#32 8#32 0x8001#32)) == some (.lbu 29#32 8#32 0x8001#32),
    decode (encode (.lh 29#32 8#32 0x8001#32)) == some (.lh 29#32 8#32 0x8001#32),
    decode (encode (.lhu 29#32 8#32 0x8001#32)) == some (.lhu 29#32 8#32 0x8001#32),
    decode (encode (.sh 29#32 8#32 0x8001#32)) == some (.sh 29#32 8#32 0x8001#32),
    decode (encode (.beq 29#32 8#32 0x8001#32)) == some (.beq 29#32 8#32 0x8001#32),
    decode (encode (.bne 29#32 8#32 0x8001#32)) == some (.bne 29#32 8#32 0x8001#32),
    decode (encode (.blez 29#32 0x8001#32)) == some (.blez 29#32 0x8001#32),
    decode (encode (.bgtz 29#32 0x8001#32)) == some (.bgtz 29#32 0x8001#32),
    decode (encode (.j 0x2aaaaaa#32)) == some (.j 0x2aaaaaa#32),
    decode (encode (.jal 0x2aaaaaa#32)) == some (.jal 0x2aaaaaa#32),
    decode (encode (.rdpgpr 8#32 9#32)) == some (.rdpgpr 8#32 9#32),
    decode (encode (.wrpgpr 8#32 9#32)) == some (.wrpgpr 8#32 9#32),
    decode (encode (.recipS 2#32 4#32)) == some (.recipS 2#32 4#32),
    decode (encode (.rsqrtD 2#32 4#32)) == some (.rsqrtD 2#32 4#32),
    decode (encode (.roundWD 2#32 4#32)) == some (.roundWD 2#32 4#32),
    decode (encode (.truncWD 2#32 4#32)) == some (.truncWD 2#32 4#32),
    decode (encode (.ceilWD 2#32 4#32)) == some (.ceilWD 2#32 4#32)
  ] := by decide +kernel

-- removed opcode groups not covered above: SPECIAL2 (0x1c) MUL, COP1X (0x13) MADD.S, MOVCI
-- (SPECIAL funct 0x01), BC1 with cc ≠ 0
example : allTrue [
    decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 3#32 0#32 0x02#32) == none,
    decode 0x4c8628a0#32 == none,
    decode (mkRT 29#32 4#32 3#32 0#32 0x01#32) == none,
    decode (mkIT 0x11#32 0x08#32 0x1c#32 0x1234#32) == none
  ] := by decide +kernel

-- `eretnc` (MD00086 Vol II-A Rev 6.06, ERETNC, p.179: COP0, CO = 1, bit 6 = 1, funct ERET),
-- `sigrie code` (SIGRIE p.375: REGIMM rt = 0x17, rs = 0), `cache op, offset(base)` (CACHE p.114:
-- SPECIAL3 funct 0x25, 9-bit offset, bit 6 = 0). Encodings checked with
-- `llvm-mc -triple=mipsel -mcpu=mips32r6`: eretnc = 0x42000058, `sigrie 5` = 0x04170005,
-- `cache 20, -8($9)` = 0x7d34fc25, `cache 1, 255($4)` = 0x7c817fa5.
example : allTrue [
    encode .eretnc == 0x42000058#32,
    decode 0x42000058#32 == some .eretnc,
    encode (.sigrie 5#32) == 0x04170005#32,
    decode 0x04170005#32 == some (.sigrie 5#32),
    decode (encode (.sigrie 0xffff#32)) == some (.sigrie 0xffff#32),
    decode 0x04370005#32 == none,  -- sigrie, rs ≠ 0
    encode (.cache 9#32 20#32 0x1f8#32) == 0x7d34fc25#32,  -- cache 20, -8($9)
    decode 0x7d34fc25#32 == some (.cache 9#32 20#32 0x1f8#32),
    encode (.cache 4#32 1#32 0xff#32) == 0x7c817fa5#32,  -- cache 1, 255($4)
    decode 0x7c817fa5#32 == some (.cache 4#32 1#32 0xff#32),
    decode 0x7c817fe5#32 == none,  -- cache, bit 6 set
    decode (encode (.cache 31#32 31#32 0x1ff#32)) == some (.cache 31#32 31#32 0x1ff#32),
    -- mfc0/mtc0 of the Release 6 registers round-trip
    decode (encode (.mfc0 8#32 4#32 2#32)) == some (.mfc0 8#32 4#32 2#32),  -- UserLocal
    decode (encode (.mtc0 8#32 31#32 7#32)) == some (.mtc0 8#32 31#32 7#32),  -- KScratch6
    decode (encode (.mfc0 8#32 8#32 2#32)) == some (.mfc0 8#32 8#32 2#32),  -- BadInstrP
    -- SDBBP, DERET and the TLB instructions are not implemented: their words do not decode
    decode 0x0000000e#32 == none,  -- sdbbp
    decode 0x4200001f#32 == none,  -- deret
    decode 0x42000002#32 == none,  -- tlbwi
    decode 0x42000003#32 == none,  -- tlbinv
    -- Release 6 integer instructions: round trips, the words llvm-mc gives (Tests/AsmTests.lean
    -- `r6IntWords`), and the neighbouring encodings that do not decode.
    decode (encode (.mul 29#32 8#32 3#32)) == some (.mul 29#32 8#32 3#32),
    decode (encode (.muh 29#32 8#32 3#32)) == some (.muh 29#32 8#32 3#32),
    decode (encode (.mulu 29#32 8#32 3#32)) == some (.mulu 29#32 8#32 3#32),
    decode (encode (.muhu 29#32 8#32 3#32)) == some (.muhu 29#32 8#32 3#32),
    decode (encode (.div 29#32 8#32 3#32)) == some (.div 29#32 8#32 3#32),
    decode (encode (.mod 29#32 8#32 3#32)) == some (.mod 29#32 8#32 3#32),
    decode (encode (.divu 29#32 8#32 3#32)) == some (.divu 29#32 8#32 3#32),
    decode (encode (.modu 29#32 8#32 3#32)) == some (.modu 29#32 8#32 3#32),
    decode (encode (.seleqz 29#32 8#32 3#32)) == some (.seleqz 29#32 8#32 3#32),
    decode (encode (.selnez 29#32 8#32 3#32)) == some (.selnez 29#32 8#32 3#32),
    decode (encode (.lsa 29#32 8#32 3#32 2#32)) == some (.lsa 29#32 8#32 3#32 2#32),
    decode (encode (.align 29#32 8#32 3#32 3#32)) == some (.align 29#32 8#32 3#32 3#32),
    decode (encode (.bitswap 8#32 3#32)) == some (.bitswap 8#32 3#32),
    decode (encode (.addiupc 8#32 0x7ffff#32)) == some (.addiupc 8#32 0x7ffff#32),
    decode (encode (.lwpc 8#32 0x40000#32)) == some (.lwpc 8#32 0x40000#32),
    decode (encode (.auipc 8#32 0x8001#32)) == some (.auipc 8#32 0x8001#32),
    decode (encode (.aluipc 8#32 0xffff#32)) == some (.aluipc 8#32 0xffff#32),
    -- llvm-mc words: mul $t0,$t1,$t2; lsa $t0,$t1,$t2,3; align $t0,$t1,$t2,2; bitswap $t0,$t1; addiupc $t0,-8
    decode 0x012a4098#32 == some (.mul 9#32 10#32 8#32),
    decode 0x012a4085#32 == some (.lsa 9#32 10#32 8#32 2#32),
    decode 0x7d2a42a0#32 == some (.align 9#32 10#32 8#32 2#32),
    decode 0x7c094020#32 == some (.bitswap 8#32 9#32),
    decode 0xed07fffe#32 == some (.addiupc 8#32 0x7fffe#32),
    -- MUL/DIV with `sa` other than 00010/00011 (`sa` = 0 is the removed HI/LO form, Table A.23, p.462)
    decode (mkRT 9#32 10#32 8#32 0#32 0x18#32) == none,
    decode (mkRT 9#32 10#32 8#32 1#32 0x1a#32) == none,
    decode (mkRT 9#32 10#32 8#32 4#32 0x1b#32) == none,
    -- LSA with bits 10..8 nonzero, SELNEZ with `sa` nonzero, BITSWAP with `rs` nonzero: unnamed fields
    decode (mkRT 9#32 10#32 8#32 4#32 0x05#32) == none,
    decode (mkRT 9#32 10#32 8#32 1#32 0x37#32) == none,
    decode ((0x1f#32 <<< 26) ||| mkRT 1#32 9#32 8#32 0#32 0x20#32) == none,
    -- PCREL: LWUPC (bits 20..19 = 10, MIPS64), LDPC (11 0xx) and the reserved 11 10x do not decode
    decode (mkIT 0x3b#32 8#32 0x10#32 0#32) == none,
    decode (mkIT 0x3b#32 8#32 0x18#32 0#32) == none,
    decode (mkIT 0x3b#32 8#32 0x1c#32 0#32) == none,
    -- Release 6 compact branches and jumps: round trip (MD00086 Vol II-A Rev 6.06 Table A.26, p.464).
    decode (encode (.bc 0x2abcdef#32)) == some (.bc 0x2abcdef#32),
    decode (encode (.balc 0x3ffffff#32)) == some (.balc 0x3ffffff#32),
    decode (encode (.beqc 3#32 5#32 0x8001#32)) == some (.beqc 3#32 5#32 0x8001#32),
    decode (encode (.bnec 1#32 31#32 0x7fff#32)) == some (.bnec 1#32 31#32 0x7fff#32),
    decode (encode (.bltc 5#32 3#32 0xffff#32)) == some (.bltc 5#32 3#32 0xffff#32),
    decode (encode (.bgec 3#32 5#32 0#32)) == some (.bgec 3#32 5#32 0#32),
    decode (encode (.bltuc 31#32 1#32 0x1234#32)) == some (.bltuc 31#32 1#32 0x1234#32),
    decode (encode (.bgeuc 2#32 7#32 0x8000#32)) == some (.bgeuc 2#32 7#32 0x8000#32),
    decode (encode (.blezc 3#32 0x10#32)) == some (.blezc 3#32 0x10#32),
    decode (encode (.bgezc 31#32 0xfff0#32)) == some (.bgezc 31#32 0xfff0#32),
    decode (encode (.bgtzc 1#32 0x1#32)) == some (.bgtzc 1#32 0x1#32),
    decode (encode (.bltzc 9#32 0x8000#32)) == some (.bltzc 9#32 0x8000#32),
    decode (encode (.beqzc 3#32 0x1fffff#32)) == some (.beqzc 3#32 0x1fffff#32),
    decode (encode (.bnezc 31#32 0x100000#32)) == some (.bnezc 31#32 0x100000#32),
    decode (encode (.blezalc 4#32 0x4#32)) == some (.blezalc 4#32 0x4#32),
    decode (encode (.bgezalc 4#32 0x4#32)) == some (.bgezalc 4#32 0x4#32),
    decode (encode (.bgtzalc 31#32 0xffff#32)) == some (.bgtzalc 31#32 0xffff#32),
    decode (encode (.bltzalc 1#32 0#32)) == some (.bltzalc 1#32 0#32),
    decode (encode (.beqzalc 5#32 0x8#32)) == some (.beqzalc 5#32 0x8#32),
    decode (encode (.bnezalc 5#32 0x8#32)) == some (.bnezalc 5#32 0x8#32),
    decode (encode (.bovc 5#32 3#32 0x20#32)) == some (.bovc 5#32 3#32 0x20#32),
    decode (encode (.bovc 0#32 0#32 0#32)) == some (.bovc 0#32 0#32 0#32),
    decode (encode (.bnvc 7#32 7#32 0xfffe#32)) == some (.bnvc 7#32 7#32 0xfffe#32),
    decode (encode (.jic 3#32 0x8000#32)) == some (.jic 3#32 0x8000#32),
    decode (encode (.jialc 0#32 0x7fff#32)) == some (.jialc 0#32 0x7fff#32),
    -- The shared opcodes are split by the rs/rt relation (Table A.26, p.464):
    decode (mkIT 0x06#32 0#32 0#32 4#32) == some (.blez 0#32 4#32),  -- rt = 0: BLEZ
    decode (mkIT 0x06#32 0#32 3#32 4#32) == some (.blezalc 3#32 4#32),  -- rs = 0
    decode (mkIT 0x06#32 3#32 3#32 4#32) == some (.bgezalc 3#32 4#32),  -- rs = rt
    decode (mkIT 0x08#32 0#32 0#32 4#32) == some (.bovc 0#32 0#32 4#32),  -- rs = rt = 0
    decode (mkIT 0x08#32 0#32 3#32 4#32) == some (.beqzalc 3#32 4#32),  -- rs = 0 < rt
    decode (mkIT 0x18#32 3#32 3#32 4#32) == some (.bnvc 3#32 3#32 4#32),  -- rs = rt
    decode (mkIT 0x36#32 0#32 3#32 4#32) == some (.jic 3#32 4#32),  -- rs = 0: JIC
    decode (mkIT 0x3e#32 3#32 0#32 4#32) == some (.bnezc 3#32 4#32)  -- rs ≠ 0: BNEZC
  ] := by decide +kernel
