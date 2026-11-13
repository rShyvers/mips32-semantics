import Semantics.Instruction

/-!
# Tests for `Semantics/Instruction.lean` (decode / encode)

Moved verbatim out of `Semantics/Instruction.lean` (reviewability restructuring): the definition file now holds definitions only.
Hand-computed words decode to the expected constructor, `encode` produces the expected word,
and round trips hold on concrete instances. The general round-trip theorem is
`decode_encode` in `Semantics/Specs/DecodeSpec.lean`.
-/


-- Each v1 instruction: hand-computed word (from INSTRUCTION-REF encodings,
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
example : decode (mkRT 29#32 8#32 3#32 0#32 0x0b#32) = some (.movn 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x0a#32) = some (.movz 29#32 8#32 3#32) := by decide

-- R-type shift: rd=3, rt=8, shamt=5 (rs unused/0)
example : decode (mkRT 0#32 8#32 3#32 5#32 0x00#32) = some (.sll 3#32 8#32 5#32) := by decide
example : decode (mkRT 0#32 8#32 3#32 5#32 0x02#32) = some (.srl 3#32 8#32 5#32) := by decide
example : decode (mkRT 0#32 8#32 3#32 5#32 0x03#32) = some (.sra 3#32 8#32 5#32) := by decide

-- R-type variable shift: rd=3, rt=8, rs=29 (shamt field unused/0)
example : decode (mkRT 29#32 8#32 3#32 0#32 0x04#32) = some (.sllv 3#32 8#32 29#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x06#32) = some (.srlv 3#32 8#32 29#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x07#32) = some (.srav 3#32 8#32 29#32) := by decide

-- R-type mult/div: rs=29, rt=8
example : decode (mkRT 29#32 8#32 0#32 0#32 0x18#32) = some (.mult 29#32 8#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x19#32) = some (.multu 29#32 8#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x1a#32) = some (.div 29#32 8#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x1b#32) = some (.divu 29#32 8#32) := by decide

-- R-type move: rd=3
example : decode (mkRT 0#32 0#32 3#32 0#32 0x12#32) = some (.mflo 3#32) := by decide
example : decode (mkRT 0#32 0#32 3#32 0#32 0x10#32) = some (.mfhi 3#32) := by decide

-- R-type move, write direction: rs=29 (same field shape as jr)
example : decode (mkRT 29#32 0#32 0#32 0#32 0x11#32) = some (.mthi 29#32) := by decide
example : decode (mkRT 29#32 0#32 0#32 0#32 0x13#32) = some (.mtlo 29#32) := by decide

-- syscall: opcode 0, funct 0x0c, all other fields 0
example : decode (mkRT 0#32 0#32 0#32 0#32 0x0c#32) = some (.syscall 0#32) := by decide

-- SPECIAL2 bit-count: rs=29, rd=3 (rt field duplicates rd=3, per the real encoding)
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 3#32 3#32 0#32 0x21#32) = some (.clo 29#32 3#32) := by decide
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 3#32 3#32 0#32 0x20#32) = some (.clz 29#32 3#32) := by decide
-- strict decode: an `rt` field that does not duplicate `rd` is UNPREDICTABLE
-- per MD00086 and does not decode.
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 17#32 3#32 0#32 0x21#32) = none := by decide

-- SPECIAL2 GPR multiply: rs=29, rt=8, rd=3 (plain rs/rt/rd shape, no duplication quirk)
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 3#32 0#32 0x02#32) = some (.mul 29#32 8#32 3#32) := by decide

-- SPECIAL2 multiply-accumulate: rs=29, rt=8 (same rs/rt shape as mult/multu)
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x00#32) = some (.madd 29#32 8#32) := by decide
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x01#32) = some (.maddu 29#32 8#32) := by decide
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x04#32) = some (.msub 29#32 8#32) := by decide
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x05#32) = some (.msubu 29#32 8#32) := by decide

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

-- R-type trap-on-condition: rs=29, rt=8 (same shape as mult/div)
example : decode (mkRT 29#32 8#32 0#32 0#32 0x34#32) = some (.teq 29#32 8#32 0#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x36#32) = some (.tne 29#32 8#32 0#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x32#32) = some (.tlt 29#32 8#32 0#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x30#32) = some (.tge 29#32 8#32 0#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x33#32) = some (.tltu 29#32 8#32 0#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x31#32) = some (.tgeu 29#32 8#32 0#32) := by decide

-- I-type arith/logic: rs=29, rt=8, imm=0x1234
example : decode (mkIT 0x08#32 29#32 8#32 0x1234#32) = some (.addi 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x09#32 29#32 8#32 0x1234#32) = some (.addiu 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0a#32 29#32 8#32 0x1234#32) = some (.slti 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0b#32 29#32 8#32 0x1234#32) = some (.sltiu 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0c#32 29#32 8#32 0x1234#32) = some (.andi 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0d#32 29#32 8#32 0x1234#32) = some (.ori 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0e#32 29#32 8#32 0x1234#32) = some (.xori 29#32 8#32 0x1234#32) := by decide

-- lui: rt=8, imm=0x1234 (rs fixed 0)
example : decode (mkIT 0x0f#32 0#32 8#32 0x1234#32) = some (.lui 8#32 0x1234#32) := by decide

-- load/store: rs=29 (base), rt=8 (dest/src), imm=0x1234 (offset)
example : decode (mkIT 0x23#32 29#32 8#32 0x1234#32) = some (.lw 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x2b#32 29#32 8#32 0x1234#32) = some (.sw 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x20#32 29#32 8#32 0x1234#32) = some (.lb 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x24#32 29#32 8#32 0x1234#32) = some (.lbu 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x21#32 29#32 8#32 0x1234#32) = some (.lh 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x25#32 29#32 8#32 0x1234#32) = some (.lhu 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x29#32 29#32 8#32 0x1234#32) = some (.sh 29#32 8#32 0x1234#32) := by decide

-- ll/sc: rs=29 (base), rt=8 (dest/src), imm=0x1234 (offset) -- identical
-- field layout to lw/sw
example : decode (mkIT 0x30#32 29#32 8#32 0x1234#32) = some (.ll 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x38#32 29#32 8#32 0x1234#32) = some (.sc 29#32 8#32 0x1234#32) := by decide

-- lwl/lwr/swl/swr: rs=29 (base), rt=8 (dest/src), imm=0x1234 (offset) --
-- identical field layout to lw/sw
example : decode (mkIT 0x22#32 29#32 8#32 0x1234#32) = some (.lwl 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x26#32 29#32 8#32 0x1234#32) = some (.lwr 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x2a#32 29#32 8#32 0x1234#32) = some (.swl 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x2e#32 29#32 8#32 0x1234#32) = some (.swr 29#32 8#32 0x1234#32) := by decide

-- branch reg/reg: rs=29, rt=8, imm=0x1234
example : decode (mkIT 0x04#32 29#32 8#32 0x1234#32) = some (.beq 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x05#32 29#32 8#32 0x1234#32) = some (.bne 29#32 8#32 0x1234#32) := by decide

-- branch reg-only: rs=29, imm=0x1234 (rt fixed 0)
example : decode (mkIT 0x06#32 29#32 0#32 0x1234#32) = some (.blez 29#32 0x1234#32) := by decide
example : decode (mkIT 0x07#32 29#32 0#32 0x1234#32) = some (.bgtz 29#32 0x1234#32) := by decide

-- "branch likely" family: same field shapes as beq/bne/blez/bgtz, opcodes
-- 0x14..0x17 (MIPS-COVERAGE-GAPS.md \u00a73.3).
example : decode (mkIT 0x14#32 29#32 8#32 0x1234#32) = some (.beql 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x15#32 29#32 8#32 0x1234#32) = some (.bnel 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x16#32 29#32 0#32 0x1234#32) = some (.blezl 29#32 0x1234#32) := by decide
example : decode (mkIT 0x17#32 29#32 0#32 0x1234#32) = some (.bgtzl 29#32 0x1234#32) := by decide

-- REGIMM zero-comparison branches: opcode 0x01, rs=29, imm=0x1234, rt field
-- selects bltz/bgez/bltzal/bgezal
example : decode (mkIT 0x01#32 29#32 0x00#32 0x1234#32) = some (.bltz 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x01#32 0x1234#32) = some (.bgez 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x10#32 0x1234#32) = some (.bltzal 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x11#32 0x1234#32) = some (.bgezal 29#32 0x1234#32) := by decide
-- REGIMM branch-likely zero-comparison family: same opcode 0x01, rt field
-- 0x02/0x03/0x12/0x13 selects bltzl/bgezl/bltzall/bgezall.
example : decode (mkIT 0x01#32 29#32 0x02#32 0x1234#32) = some (.bltzl 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x03#32 0x1234#32) = some (.bgezl 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x12#32 0x1234#32) = some (.bltzall 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x13#32 0x1234#32) = some (.bgezall 29#32 0x1234#32) := by decide
-- REGIMM trap-immediate family: same opcode 0x01, `rt` field selects
-- teqi/tnei/tgei/tgeiu/tlti/tltiu (real MIPS32 ISA, MD00086 Rev 2.50 §3.2,
-- Table 3-2 -- see docs/spec/MIPS-COVERAGE-GAPS.md §3.8).
example : decode (mkIT 0x01#32 29#32 0x0c#32 0x1234#32) = some (.teqi 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x0e#32 0x1234#32) = some (.tnei 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x08#32 0x1234#32) = some (.tgei 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x09#32 0x1234#32) = some (.tgeiu 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x0a#32 0x1234#32) = some (.tlti 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x0b#32 0x1234#32) = some (.tltiu 29#32 0x1234#32) := by decide
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
example : decode (mkIT 0x31#32 29#32 5#32 0x1234#32) = some (.lwc1 29#32 5#32 0x1234#32) := by
  decide
example : decode (mkIT 0x39#32 29#32 5#32 0x1234#32) = some (.swc1 29#32 5#32 0x1234#32) := by
  decide
-- add.s/sub.s/mul.s/div.s: fmt=S, ft=6, fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 8#32 0x00#32) = some (.addS 8#32 7#32 6#32) := by
  decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 8#32 0x01#32) = some (.subS 8#32 7#32 6#32) := by
  decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 8#32 0x02#32) = some (.mulS 8#32 7#32 6#32) := by
  decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 8#32 0x03#32) = some (.divS 8#32 7#32 6#32) := by
  decide
-- mov.s/cvt.w.s: fmt=S, fs=7, fd=8 (ft-position fixed 0)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x06#32) = some (.movS 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x24#32) = some (.cvtWS 8#32 7#32) := by
  decide
-- cvt.s.w: fmt=W, fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x14#32 0#32 7#32 8#32 0x20#32) = some (.cvtSW 8#32 7#32) := by
  decide
-- c.eq.s/c.lt.s/c.le.s: fmt=S, fs=7, ft=6, fd-position (cc) fixed 0
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x32#32) = some (.cCondS 2#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x3c#32) = some (.cCondS 12#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x3e#32) = some (.cCondS 14#32 0#32 7#32 6#32) := by decide
-- c.eq.s with a nonzero cc field (unsupported, only cc=0 modeled) → none
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
-- c.f.s/c.un.s/c.ueq.s/c.olt.s/c.ult.s/c.ole.s/c.ule.s: fmt=S, fs=7, ft=6, fd-position (cc) fixed 0
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x30#32) = some (.cCondS 0#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x31#32) = some (.cCondS 1#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x33#32) = some (.cCondS 3#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x34#32) = some (.cCondS 4#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x35#32) = some (.cCondS 5#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x36#32) = some (.cCondS 6#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x37#32) = some (.cCondS 7#32 0#32 7#32 6#32) := by decide
-- c.un.s with a nonzero cc field (unsupported, only cc=0 modeled) → none
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 1#32 0x31#32) = none := by decide

-- ldc1/sdc1: rs=29 (base), ft=5, imm=0x1234 (identical layout to lwc1/swc1)
example : decode (mkIT 0x35#32 29#32 5#32 0x1234#32) = some (.ldc1 29#32 5#32 0x1234#32) := by
  decide
example : decode (mkIT 0x3d#32 29#32 5#32 0x1234#32) = some (.sdc1 29#32 5#32 0x1234#32) := by
  decide
-- add.d/sub.d/mul.d/div.d: fmt=D, ft=6, fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 8#32 0x00#32) = some (.addD 8#32 7#32 6#32) := by
  decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 8#32 0x01#32) = some (.subD 8#32 7#32 6#32) := by
  decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 8#32 0x02#32) = some (.mulD 8#32 7#32 6#32) := by
  decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 8#32 0x03#32) = some (.divD 8#32 7#32 6#32) := by
  decide
-- mov.d/sqrt.d/abs.d/neg.d/cvt.w.d: fmt=D, fs=7, fd=8 (ft-position fixed 0)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x06#32) = some (.movD 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x04#32) = some (.sqrtD 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x05#32) = some (.absD 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x07#32) = some (.negD 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x24#32) = some (.cvtWD 8#32 7#32) := by
  decide
-- cvt.d.s: fmt=S (source is single), fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x21#32) = some (.cvtDS 8#32 7#32) := by
  decide
-- cvt.s.d: fmt=D (source is double), fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x20#32) = some (.cvtSD 8#32 7#32) := by
  decide
-- cvt.d.w: fmt=W (source is a word), fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x14#32 0#32 7#32 8#32 0x21#32) = some (.cvtDW 8#32 7#32) := by
  decide
-- c.eq.d/c.lt.d/c.le.d/c.f.d/c.un.d/c.ueq.d/c.olt.d/c.ult.d/c.ole.d/c.ule.d:
-- fmt=D, fs=7, ft=6, fd-position (cc) fixed 0
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x32#32) = some (.cCondD 2#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x3c#32) = some (.cCondD 12#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x3e#32) = some (.cCondD 14#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x30#32) = some (.cCondD 0#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x31#32) = some (.cCondD 1#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x33#32) = some (.cCondD 3#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x34#32) = some (.cCondD 4#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x35#32) = some (.cCondD 5#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x36#32) = some (.cCondD 6#32 0#32 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x37#32) = some (.cCondD 7#32 0#32 7#32 6#32) := by decide
-- c.eq.d with a nonzero cc field (unsupported, only cc=0 modeled) → none
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 1#32 0x32#32) = none := by decide

-- cfc1/mfc1 share the same (rt, fs) field shape, distinguished by the
-- rs-position sub-opcode (CF=0x02 vs MF=0x00); ctc1/mtc1 likewise (CT=0x06 vs MT=0x04)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x02#32 8#32 3#32 0#32 0#32) = some (.cfc1 8#32 3#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x06#32 8#32 3#32 0#32 0#32) = some (.ctc1 8#32 3#32) := by decide
-- bc1t/bc1f: fmt=BC1, tf=1/0, offset=0x1234
example : decode (mkIT 0x11#32 0x08#32 1#32 0x1234#32) = some (.bc1t 0#32 0x1234#32) := by decide
example : decode (mkIT 0x11#32 0x08#32 0#32 0x1234#32) = some (.bc1f 0#32 0x1234#32) := by decide
-- BC1 with nd = 1 (rt-field bit 1) is the branch-likely form; bits 20..18 are cc
example : decode (mkIT 0x11#32 0x08#32 2#32 0x1234#32) = some (.bc1fl 0#32 0x1234#32) := by decide
example : decode (mkIT 0x11#32 0x08#32 3#32 0x1234#32) = some (.bc1tl 0#32 0x1234#32) := by decide
example : decode (mkIT 0x11#32 0x08#32 0x1d#32 0x1234#32) = some (.bc1t 7#32 0x1234#32) := by decide
example : decode (mkCCI 0x11#32 0x08#32 5#32 1#32 0#32 0xfffe#32) = some (.bc1fl 5#32 0xfffe#32) := by
  decide

-- `encode ∘ decode` round-trips, spanning R / I / J / branch / syscall
example : encode (.add 29#32 8#32 3#32) = mkRT 29#32 8#32 3#32 0#32 0x20#32 := by decide
example : encode (.lw 29#32 8#32 0x1234#32) = mkIT 0x23#32 29#32 8#32 0x1234#32 := by decide
example : encode (.beq 29#32 8#32 0x1234#32) = mkIT 0x04#32 29#32 8#32 0x1234#32 := by decide
example : encode (.j 0x3ffffff#32) = (0x02#32 <<< 26) ||| mkJT 0x3ffffff#32 := by decide
example : encode (.syscall 0#32) = mkRT 0#32 0#32 0#32 0#32 0x0c#32 := by decide
example : encode (.sll 3#32 8#32 5#32) = mkRT 0#32 8#32 3#32 5#32 0x00#32 := by decide
example : encode (.movn 29#32 8#32 3#32) = mkRT 29#32 8#32 3#32 0#32 0x0b#32 := by decide
example : encode (.clo 29#32 3#32) = (0x1c#32 <<< 26) ||| mkRT 29#32 3#32 3#32 0#32 0x21#32 := by decide
example : encode (.seb 3#32 8#32) = (0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x10#32 0x20#32 := by decide
example : encode (.wsbh 3#32 8#32) = (0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x02#32 0x20#32 := by decide
example : encode (.rotr 3#32 8#32 5#32) = mkRT 0x01#32 8#32 3#32 5#32 0x02#32 := by decide
example : encode (.rotrv 3#32 8#32 29#32) = mkRT 29#32 8#32 3#32 0x01#32 0x06#32 := by decide
example : encode (.ext 8#32 29#32 6#32 10#32) = (0x1f#32 <<< 26) ||| mkRT 29#32 8#32 9#32 6#32 0x00#32 := by decide
example : encode (.ins 8#32 29#32 6#32 10#32) = (0x1f#32 <<< 26) ||| mkRT 29#32 8#32 15#32 6#32 0x04#32 := by decide
example : encode (.sllv 3#32 8#32 29#32) = mkRT 29#32 8#32 3#32 0#32 0x04#32 := by decide
example : encode (.mul 29#32 8#32 3#32) = (0x1c#32 <<< 26) ||| mkRT 29#32 8#32 3#32 0#32 0x02#32 := by decide
example : encode (.madd 29#32 8#32) = (0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x00#32 := by decide
example : encode (.maddu 29#32 8#32) = (0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x01#32 := by decide
example : encode (.msub 29#32 8#32) = (0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x04#32 := by decide
example : encode (.msubu 29#32 8#32) = (0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x05#32 := by decide
example : encode (.mthi 29#32) = mkRT 29#32 0#32 0#32 0#32 0x11#32 := by decide
example : encode (.mtlo 29#32) = mkRT 29#32 0#32 0#32 0#32 0x13#32 := by decide
example : encode (.jr 29#32) = mkRT 29#32 0#32 0#32 0#32 0x08#32 := by decide
example : encode (.jalr 29#32 3#32) = mkRT 29#32 0#32 3#32 0#32 0x09#32 := by decide
-- full round trip for every new instruction (decode ∘ encode = id on the field values we store)
example : decode (encode (.movn 29#32 8#32 3#32)) = some (.movn 29#32 8#32 3#32) := by decide
example : decode (encode (.movz 29#32 8#32 3#32)) = some (.movz 29#32 8#32 3#32) := by decide
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
example : decode (encode (.mul 29#32 8#32 3#32)) = some (.mul 29#32 8#32 3#32) := by decide
example : decode (encode (.madd 29#32 8#32)) = some (.madd 29#32 8#32) := by decide
example : decode (encode (.maddu 29#32 8#32)) = some (.maddu 29#32 8#32) := by decide
example : decode (encode (.msub 29#32 8#32)) = some (.msub 29#32 8#32) := by decide
example : decode (encode (.msubu 29#32 8#32)) = some (.msubu 29#32 8#32) := by decide
example : decode (encode (.mthi 29#32)) = some (.mthi 29#32) := by decide
example : decode (encode (.mtlo 29#32)) = some (.mtlo 29#32) := by decide
example : decode (encode (.jr 29#32)) = some (.jr 29#32) := by decide
example : decode (encode (.jalr 29#32 3#32)) = some (.jalr 29#32 3#32) := by decide
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
example : decode (encode (.lwc1 29#32 5#32 0x1234#32)) = some (.lwc1 29#32 5#32 0x1234#32) := by
  decide
example : decode (encode (.swc1 29#32 5#32 0x1234#32)) = some (.swc1 29#32 5#32 0x1234#32) := by
  decide
example : decode (encode (.addS 8#32 7#32 6#32)) = some (.addS 8#32 7#32 6#32) := by decide
example : decode (encode (.subS 8#32 7#32 6#32)) = some (.subS 8#32 7#32 6#32) := by decide
example : decode (encode (.mulS 8#32 7#32 6#32)) = some (.mulS 8#32 7#32 6#32) := by decide
example : decode (encode (.divS 8#32 7#32 6#32)) = some (.divS 8#32 7#32 6#32) := by decide
example : decode (encode (.movS 8#32 7#32)) = some (.movS 8#32 7#32) := by decide
example : decode (encode (.cvtSW 8#32 7#32)) = some (.cvtSW 8#32 7#32) := by decide
example : decode (encode (.cvtWS 8#32 7#32)) = some (.cvtWS 8#32 7#32) := by decide
example : decode (encode (.cCondS 2#32 0#32 7#32 6#32)) = some (.cCondS 2#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondS 12#32 0#32 7#32 6#32)) = some (.cCondS 12#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondS 14#32 0#32 7#32 6#32)) = some (.cCondS 14#32 0#32 7#32 6#32) := by decide
example : decode (encode (.sqrtS 8#32 7#32)) = some (.sqrtS 8#32 7#32) := by decide
example : decode (encode (.absS 8#32 7#32)) = some (.absS 8#32 7#32) := by decide
example : decode (encode (.negS 8#32 7#32)) = some (.negS 8#32 7#32) := by decide
example : decode (encode (.roundWS 8#32 7#32)) = some (.roundWS 8#32 7#32) := by decide
example : decode (encode (.truncWS 8#32 7#32)) = some (.truncWS 8#32 7#32) := by decide
example : decode (encode (.ceilWS 8#32 7#32)) = some (.ceilWS 8#32 7#32) := by decide
example : decode (encode (.floorWS 8#32 7#32)) = some (.floorWS 8#32 7#32) := by decide
example : decode (encode (.cCondS 0#32 0#32 7#32 6#32)) = some (.cCondS 0#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondS 1#32 0#32 7#32 6#32)) = some (.cCondS 1#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondS 3#32 0#32 7#32 6#32)) = some (.cCondS 3#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondS 4#32 0#32 7#32 6#32)) = some (.cCondS 4#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondS 5#32 0#32 7#32 6#32)) = some (.cCondS 5#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondS 6#32 0#32 7#32 6#32)) = some (.cCondS 6#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondS 7#32 0#32 7#32 6#32)) = some (.cCondS 7#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cfc1 8#32 3#32)) = some (.cfc1 8#32 3#32) := by decide
example : decode (encode (.ctc1 8#32 3#32)) = some (.ctc1 8#32 3#32) := by decide
example : decode (encode (.bc1t 0#32 0x1234#32)) = some (.bc1t 0#32 0x1234#32) := by decide
example : decode (encode (.bc1f 0#32 0x1234#32)) = some (.bc1f 0#32 0x1234#32) := by decide

-- Coprocessor 1 (FPU), double-precision: full `decode (encode i) = some i` round-trips
example : decode (encode (.ldc1 29#32 5#32 0x1234#32)) = some (.ldc1 29#32 5#32 0x1234#32) := by
  decide
example : decode (encode (.sdc1 29#32 5#32 0x1234#32)) = some (.sdc1 29#32 5#32 0x1234#32) := by
  decide
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
example : decode (encode (.cCondD 2#32 0#32 7#32 6#32)) = some (.cCondD 2#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondD 12#32 0#32 7#32 6#32)) = some (.cCondD 12#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondD 14#32 0#32 7#32 6#32)) = some (.cCondD 14#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondD 0#32 0#32 7#32 6#32)) = some (.cCondD 0#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondD 1#32 0#32 7#32 6#32)) = some (.cCondD 1#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondD 3#32 0#32 7#32 6#32)) = some (.cCondD 3#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondD 4#32 0#32 7#32 6#32)) = some (.cCondD 4#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondD 5#32 0#32 7#32 6#32)) = some (.cCondD 5#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondD 6#32 0#32 7#32 6#32)) = some (.cCondD 6#32 0#32 7#32 6#32) := by decide
example : decode (encode (.cCondD 7#32 0#32 7#32 6#32)) = some (.cCondD 7#32 0#32 7#32 6#32) := by decide

-- REGIMM zero-comparison branches: full decode(encode i) = some i round-trips
example : decode (encode (.bltz 29#32 0x1234#32)) = some (.bltz 29#32 0x1234#32) := by decide
example : decode (encode (.bgez 29#32 0x1234#32)) = some (.bgez 29#32 0x1234#32) := by decide
example : decode (encode (.bltzal 29#32 0x1234#32)) = some (.bltzal 29#32 0x1234#32) := by decide
example : decode (encode (.bgezal 29#32 0x1234#32)) = some (.bgezal 29#32 0x1234#32) := by decide
-- "Branch likely" family: encode matches the hand-computed opcode, and
-- full decode(encode i) = some i round-trips (MIPS-COVERAGE-GAPS.md \u00a73.3).
example : encode (.beql 29#32 8#32 0x1234#32) = mkIT 0x14#32 29#32 8#32 0x1234#32 := by decide
example : encode (.bnel 29#32 8#32 0x1234#32) = mkIT 0x15#32 29#32 8#32 0x1234#32 := by decide
example : encode (.blezl 29#32 0x1234#32) = mkIT 0x16#32 29#32 0#32 0x1234#32 := by decide
example : encode (.bgtzl 29#32 0x1234#32) = mkIT 0x17#32 29#32 0#32 0x1234#32 := by decide
example : encode (.bltzl 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x02#32 0x1234#32 := by decide
example : encode (.bgezl 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x03#32 0x1234#32 := by decide
example : encode (.bltzall 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x12#32 0x1234#32 := by decide
example : encode (.bgezall 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x13#32 0x1234#32 := by decide
example : decode (encode (.beql 29#32 8#32 0x1234#32)) = some (.beql 29#32 8#32 0x1234#32) := by decide
example : decode (encode (.bnel 29#32 8#32 0x1234#32)) = some (.bnel 29#32 8#32 0x1234#32) := by decide
example : decode (encode (.blezl 29#32 0x1234#32)) = some (.blezl 29#32 0x1234#32) := by decide
example : decode (encode (.bgtzl 29#32 0x1234#32)) = some (.bgtzl 29#32 0x1234#32) := by decide
example : decode (encode (.bltzl 29#32 0x1234#32)) = some (.bltzl 29#32 0x1234#32) := by decide
example : decode (encode (.bgezl 29#32 0x1234#32)) = some (.bgezl 29#32 0x1234#32) := by decide
example : decode (encode (.bltzall 29#32 0x1234#32)) = some (.bltzall 29#32 0x1234#32) := by decide
example : decode (encode (.bgezall 29#32 0x1234#32)) = some (.bgezall 29#32 0x1234#32) := by decide
-- REGIMM trap-immediate family: encode matches the hand-computed opcode,
-- and full decode(encode i) = some i round-trips.
example : encode (.teqi 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x0c#32 0x1234#32 := by decide
example : encode (.tnei 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x0e#32 0x1234#32 := by decide
example : encode (.tgei 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x08#32 0x1234#32 := by decide
example : encode (.tgeiu 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x09#32 0x1234#32 := by decide
example : encode (.tlti 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x0a#32 0x1234#32 := by decide
example : encode (.tltiu 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x0b#32 0x1234#32 := by decide
example : decode (encode (.teqi 29#32 0x1234#32)) = some (.teqi 29#32 0x1234#32) := by decide
example : decode (encode (.tnei 29#32 0x1234#32)) = some (.tnei 29#32 0x1234#32) := by decide
example : decode (encode (.tgei 29#32 0x1234#32)) = some (.tgei 29#32 0x1234#32) := by decide
example : decode (encode (.tgeiu 29#32 0x1234#32)) = some (.tgeiu 29#32 0x1234#32) := by decide
example : decode (encode (.tlti 29#32 0x1234#32)) = some (.tlti 29#32 0x1234#32) := by decide
example : decode (encode (.tltiu 29#32 0x1234#32)) = some (.tltiu 29#32 0x1234#32) := by decide
-- ll/sc: encode matches the hand-computed opcode, and decode (encode i) = some i
example : encode (.ll 29#32 8#32 0x1234#32) = mkIT 0x30#32 29#32 8#32 0x1234#32 := by decide
example : encode (.sc 29#32 8#32 0x1234#32) = mkIT 0x38#32 29#32 8#32 0x1234#32 := by decide
example : decode (encode (.ll 29#32 8#32 0x1234#32)) = some (.ll 29#32 8#32 0x1234#32) := by decide
example : decode (encode (.sc 29#32 8#32 0x1234#32)) = some (.sc 29#32 8#32 0x1234#32) := by decide
-- lwl/lwr/swl/swr: encode matches the hand-computed opcode, and
-- decode (encode i) = some i
example : encode (.lwl 29#32 8#32 0x1234#32) = mkIT 0x22#32 29#32 8#32 0x1234#32 := by decide
example : encode (.lwr 29#32 8#32 0x1234#32) = mkIT 0x26#32 29#32 8#32 0x1234#32 := by decide
example : encode (.swl 29#32 8#32 0x1234#32) = mkIT 0x2a#32 29#32 8#32 0x1234#32 := by decide
example : encode (.swr 29#32 8#32 0x1234#32) = mkIT 0x2e#32 29#32 8#32 0x1234#32 := by decide
example : decode (encode (.lwl 29#32 8#32 0x1234#32)) = some (.lwl 29#32 8#32 0x1234#32) := by decide
example : decode (encode (.lwr 29#32 8#32 0x1234#32)) = some (.lwr 29#32 8#32 0x1234#32) := by decide
example : decode (encode (.swl 29#32 8#32 0x1234#32)) = some (.swl 29#32 8#32 0x1234#32) := by decide
example : decode (encode (.swr 29#32 8#32 0x1234#32)) = some (.swr 29#32 8#32 0x1234#32) := by decide

-- unknown opcodes → none
#guard decode (mkIT 0x3a#32 0#32 0#32 0#32) = none  -- opcode 0x3a, unassigned/not in v1+ scope
-- opcode 0x11 (COP1) is implemented for the fmt/funct combinations below;
-- an unrecognized fmt (not MF/MT/BC1/S/W) still decodes to `none`.
#guard decode (mkIT 0x11#32 0x1f#32 0#32 0#32) = none
-- opcodes 0x16/0x17 are now assigned to the branch-likely family
-- (blezl/bgtzl, this track's addition); 0x12/0x13 (COP2, out of scope)
-- remain unassigned instead.
#guard decode (mkIT 0x12#32 0#32 0#32 0#32) = none
-- opcode 0x13 (COP1X): funct 0x05 `luxc1` / 0x0d `suxc1` (UNPREDICTABLE with
-- FR = 0) and the paired-single functs are not modeled
#guard decode (mkIT 0x13#32 0#32 0#32 0x05#32) = none
#guard decode (mkIT 0x13#32 0#32 0#32 0x0d#32) = none
#guard decode (mkIT 0x13#32 0#32 0#32 0x26#32) = none
-- opcode 0x1c (SPECIAL2) funct 0x00/0x01/0x02/0x04/0x05/0x20/0x21 are now
-- assigned (madd/maddu/mul/msub/msubu/clz/clo); funct 0x3f remains unassigned.
#guard decode (mkIT 0x1c#32 0#32 0#32 0x3f#32) = none
#guard decode (mkIT 0x1d#32 0#32 0#32 0#32) = none

-- unknown functs under opcode 0 → none
-- funct 0x01 is `MOVCI` (movf/movt); bit 17 or bits 10..6 nonzero → none
#guard decode (mkRT 0#32 0#32 0#32 0#32 0x01#32) = some (.movf 0#32 0#32 0#32)
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
example : decode ((0x10#32 <<< 26) ||| mkRT 0x00#32 8#32 13#32 0#32 0#32)
  = some (.mfc0 8#32 13#32 0#32) := by decide
example : decode ((0x10#32 <<< 26) ||| mkRT 0x04#32 8#32 13#32 0#32 0#32)
  = some (.mtc0 8#32 13#32 0#32) := by decide
example : decode ((0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x18#32)
  = some .eret := by decide
example : decode ((0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x20#32)
  = some (.wait 0#32) := by decide

-- encode produces the exact hand-computed words above.
example : encode (.mfc0 8#32 13#32 0#32) = (0x10#32 <<< 26) ||| mkRT 0x00#32 8#32 13#32 0#32 0#32 := by
  decide
example : encode (.mtc0 8#32 13#32 0#32) = (0x10#32 <<< 26) ||| mkRT 0x04#32 8#32 13#32 0#32 0#32 := by
  decide
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
example : decode (mkIT 0x0f#32 1#32 8#32 0x1234#32) = none := by decide       -- lui, rs ≠ 0
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
-- p.332); `rs` and bits 10..6 must be zero before Release 6.
example : encode (.rdhwr 3#32 29#32) = 0x7c03e83b#32 := by decide
example : decode 0x7c03e83b#32 = some (.rdhwr 3#32 29#32) := by decide
example : decode (encode (.rdhwr 8#32 2#32)) = some (.rdhwr 8#32 2#32) := by decide
example : decode 0x7c03e87b#32 = none := by decide   -- bits 10..6 = 1 (Release 6 `sel`)
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

-- Deliberately tolerated don't-care fields (see `decode`'s docstring).
example : decode 0x42000020#32 = some (.wait 0#32) := by decide                                          -- wait, code 0
example : decode 0x43ffffe0#32 = some (.wait 0x7ffff#32) := by decide                                          -- wait, code all ones
example : decode 0x40000020#32 = none := by decide                                                -- CO bit clear
example : decode (mkRT 0#32 0#32 0#32 0x1f#32 0x0f#32) = some (.sync 0x1f#32) := by decide                 -- sync stype
example : decode (mkRT 0x1f#32 0x1f#32 0x1f#32 0x1f#32 0x0c#32) = some (.syscall 0xfffff#32) := by decide     -- syscall code
example : decode (mkRT 0x1f#32 0x1f#32 0x1f#32 0x1f#32 0x0d#32) = some (.break 0xfffff#32) := by decide       -- break code
example : decode (mkRT 29#32 8#32 0x1f#32 0x1f#32 0x34#32) = some (.teq 29#32 8#32 0x3ff#32) := by decide -- trap code
example : decode (mkRT 29#32 0#32 0#32 0x10#32 0x08#32) = some (.jr 29#32) := by decide          -- jr.hb
example : decode (mkRT 29#32 0#32 31#32 0x10#32 0x09#32) = some (.jalr 29#32 31#32) := by decide -- jalr.hb
-- `nop` / `ssnop` / `ehb` are `sll $0,$0,{0,1,3}`.
example : decode 0x00000000#32 = some (.sll 0#32 0#32 0#32) := by decide
example : decode 0x00000040#32 = some (.sll 0#32 0#32 1#32) := by decide
example : decode 0x000000c0#32 = some (.sll 0#32 0#32 3#32) := by decide

-- ## Tests: FCSR-era additions (cc fields, signaling compares, new instructions)

-- `C.cond.fmt`: all sixteen `cond` values and all eight `cc` values
example : decode 0x46062832#32 = some (.cCondS 2#32 0#32 5#32 6#32) := by decide   -- c.eq.s $f5,$f6
example : decode 0x46262f3a#32 = some (.cCondD 10#32 7#32 5#32 6#32) := by decide  -- c.seq.d $fcc7,$f5,$f6
example : encode (.cCondS 15#32 3#32 5#32 6#32) = 0x46062b3f#32 := by decide       -- c.ngt.s $fcc3,$f5,$f6
example : (List.range 16).all (fun c => (List.range 8).all fun cc =>
    decode (encode (.cCondS (BitVec.ofNat 32 c) (BitVec.ofNat 32 cc) 5#32 6#32))
      == some (.cCondS (BitVec.ofNat 32 c) (BitVec.ofNat 32 cc) 5#32 6#32) &&
    decode (encode (.cCondD (BitVec.ofNat 32 c) (BitVec.ofNat 32 cc) 30#32 2#32))
      == some (.cCondD (BitVec.ofNat 32 c) (BitVec.ofNat 32 cc) 30#32 2#32)) = true := by decide
-- bits 7..6 of a compare must be zero
example : decode 0x46062872#32 = none := by decide
example : decode 0x460628b2#32 = none := by decide

-- words hand-assembled from the field layouts on the manual pages
example : decode 0x0085100a#32 = some (.movz 4#32 5#32 2#32) := by decide
example : decode 0x00801001#32 = some (.movf 4#32 0#32 2#32) := by decide          -- movf $2,$4,$fcc0
example : decode 0x009d1001#32 = some (.movt 4#32 7#32 2#32) := by decide          -- movt $2,$4,$fcc7
example : decode 0x46002091#32 = some (.movfS 2#32 4#32 0#32) := by decide         -- movf.s $f2,$f4,$fcc0
example : decode 0x463d2091#32 = some (.movtD 2#32 4#32 7#32) := by decide         -- movt.d $f2,$f4,$fcc7
example : decode 0x46052093#32 = some (.movnS 2#32 4#32 5#32) := by decide         -- movn.s $f2,$f4,$5
example : decode 0x46252092#32 = some (.movzD 2#32 4#32 5#32) := by decide         -- movz.d $f2,$f4,$5
example : decode 0x44682000#32 = some (.mfhc1 8#32 4#32) := by decide              -- mfhc1 $8,$f4
example : decode 0x44e82000#32 = some (.mthc1 8#32 4#32) := by decide              -- mthc1 $8,$f4
example : decode 0x4c850080#32 = some (.lwxc1 2#32 5#32 4#32) := by decide         -- lwxc1 $f2,$5($4)
example : decode 0x4c850081#32 = some (.ldxc1 2#32 5#32 4#32) := by decide         -- ldxc1 $f2,$5($4)
example : decode 0x4c851008#32 = some (.swxc1 2#32 5#32 4#32) := by decide         -- swxc1 $f2,$5($4)
example : decode 0x4c851009#32 = some (.sdxc1 2#32 5#32 4#32) := by decide         -- sdxc1 $f2,$5($4)
example : decode 0x4c85080f#32 = some (.prefx 1#32 5#32 4#32) := by decide         -- prefx 1,$5($4)
example : decode 0x4c8628a0#32 = some (.maddS 2#32 4#32 5#32 6#32) := by decide    -- madd.s $f2,$f4,$f5,$f6
example : decode 0x4c8628a9#32 = some (.msubD 2#32 4#32 5#32 6#32) := by decide    -- msub.d
example : decode 0x4c8628b0#32 = some (.nmaddS 2#32 4#32 5#32 6#32) := by decide   -- nmadd.s
example : decode 0x4c8628b9#32 = some (.nmsubD 2#32 4#32 5#32 6#32) := by decide   -- nmsub.d
example : decode 0x46002095#32 = some (.recipS 2#32 4#32) := by decide             -- recip.s $f2,$f4
example : decode 0x46202096#32 = some (.rsqrtD 2#32 4#32) := by decide             -- rsqrt.d $f2,$f4
example : decode 0x4620208c#32 = some (.roundWD 2#32 4#32) := by decide            -- round.w.d
example : decode 0x4620208d#32 = some (.truncWD 2#32 4#32) := by decide
example : decode 0x4620208e#32 = some (.ceilWD 2#32 4#32) := by decide
example : decode 0x4620208f#32 = some (.floorWD 2#32 4#32) := by decide
example : decode 0xcc810010#32 = some (.pref 4#32 1#32 16#32) := by decide         -- pref 1,16($4)
example : decode 0x41606000#32 = some (.di 0#32) := by decide                      -- di
example : decode 0x41686020#32 = some (.ei 8#32) := by decide                      -- ei $8
example : decode 0x41686800#32 = none := by decide                                 -- MFMC0, rd ≠ 12
example : decode 0x40087801#32 = some (.mfc0 8#32 15#32 1#32) := by decide         -- mfc0 $8,$15,1 (EBase)
example : decode 0x40888001#32 = some (.mtc0 8#32 16#32 1#32) := by decide         -- mtc0 $8,$16,1 (Config1)
example : decode 0x40087800#32 = some (.mfc0 8#32 15#32 0#32) := by decide         -- PRId
example : decode 0x40088002#32 = none := by decide                                 -- Config2: not modeled
example : decode 0x0000000c#32 = some (.syscall 0#32) := by decide
example : decode 0x0001234d#32 = some (.break 0x48d#32) := by decide               -- code 0x48d = 1165
example : decode 0x00a41df4#32 = some (.teq 5#32 4#32 0x77#32) := by decide        -- teq $5,$4,0x77
-- round trips of the new shapes (every field at a non-trivial value)
example : decode (encode (.syscall 0xabcde#32)) = some (.syscall 0xabcde#32) := by decide
example : decode (encode (.break 0xfffff#32)) = some (.break 0xfffff#32) := by decide
example : decode (encode (.tgeu 29#32 8#32 0x2aa#32)) = some (.tgeu 29#32 8#32 0x2aa#32) := by decide
example : decode (encode (.sync 0x1f#32)) = some (.sync 0x1f#32) := by decide
example : decode (encode (.wait 0x55555#32)) = some (.wait 0x55555#32) := by decide
example : decode (encode (.pref 29#32 30#32 0x8001#32)) = some (.pref 29#32 30#32 0x8001#32) := by decide
example : decode (encode (.di 9#32)) = some (.di 9#32) := by decide
example : decode (encode (.ei 9#32)) = some (.ei 9#32) := by decide
example : decode (encode (.mfc0 9#32 16#32 1#32)) = some (.mfc0 9#32 16#32 1#32) := by decide
example : decode (encode (.movf 29#32 5#32 3#32)) = some (.movf 29#32 5#32 3#32) := by decide
example : decode (encode (.movt 29#32 5#32 3#32)) = some (.movt 29#32 5#32 3#32) := by decide
example : decode (encode (.movfS 2#32 4#32 6#32)) = some (.movfS 2#32 4#32 6#32) := by decide
example : decode (encode (.movtS 2#32 4#32 6#32)) = some (.movtS 2#32 4#32 6#32) := by decide
example : decode (encode (.movfD 2#32 4#32 6#32)) = some (.movfD 2#32 4#32 6#32) := by decide
example : decode (encode (.movtD 2#32 4#32 6#32)) = some (.movtD 2#32 4#32 6#32) := by decide
example : decode (encode (.movnD 2#32 4#32 31#32)) = some (.movnD 2#32 4#32 31#32) := by decide
example : decode (encode (.movzS 2#32 4#32 31#32)) = some (.movzS 2#32 4#32 31#32) := by decide
example : decode (encode (.bc1f 7#32 0x8000#32)) = some (.bc1f 7#32 0x8000#32) := by decide
example : decode (encode (.bc1t 7#32 0x8000#32)) = some (.bc1t 7#32 0x8000#32) := by decide
example : decode (encode (.bc1fl 7#32 0x8000#32)) = some (.bc1fl 7#32 0x8000#32) := by decide
example : decode (encode (.bc1tl 7#32 0x8000#32)) = some (.bc1tl 7#32 0x8000#32) := by decide
example : decode (encode (.maddD 2#32 4#32 6#32 8#32)) = some (.maddD 2#32 4#32 6#32 8#32) := by decide
example : decode (encode (.nmsubS 31#32 30#32 29#32 28#32)) = some (.nmsubS 31#32 30#32 29#32 28#32) := by
  decide
example : decode (encode (.lwxc1 2#32 5#32 4#32)) = some (.lwxc1 2#32 5#32 4#32) := by decide
example : decode (encode (.sdxc1 2#32 5#32 4#32)) = some (.sdxc1 2#32 5#32 4#32) := by decide
example : decode (encode (.prefx 31#32 5#32 4#32)) = some (.prefx 31#32 5#32 4#32) := by decide
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
