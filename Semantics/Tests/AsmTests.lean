import Semantics.Asm

/-!
# Tests for `Semantics/Asm.lean` (the assembler)

Moved verbatim out of `Semantics/Asm.lean` (reviewability restructuring): the definition file now holds definitions only.
-/


-- Note: these golden tests use `#guard` exclusively, not `by decide`/`by rfl`.
-- `Std.HashMap`'s `getD`/`contains` do not kernel-reduce (`by decide` gets
-- stuck on the underlying imperative array operations — confirmed against
-- a minimal `Std.HashMap Nat Nat` repro), so `by decide`/`by rfl` are not
-- usable for any `Program`-valued assertion in this Lean/Std version.
-- `#guard` (compiled evaluation) is explicitly sanctioned by DESIGN.md §5
-- and works correctly here; all checks below use it.

-- A `.text` program mixing `add`/`addi`/`beq`/`jal` with labels.
-- loop:  addi $t0, $zero, 1
--        add  $t1, $t0, $t0
--        beq  $t1, $zero, loop
--        jal  loop
def prog1Src : String :=
"loop: addi $t0, $zero, 1\n" ++
"      add $t1, $t0, $t0\n" ++
"      beq $t1, $zero, loop\n" ++
"      jal loop\n"

def prog1 : Program :=
  match assemble prog1Src with
  | .ok p => p
  | .error _ => ∅

-- addr 0x400000: addi $t0,$zero,1 -> opcode 0x09? no addi is 0x08.
#guard prog1.getD textBase 0 = mkIT (8#32) (0#32) (8#32) (1#32)

#guard prog1.getD (textBase + 4#32) 0 = mkRT (8#32) (8#32) (9#32) (0#32) (0x20#32)

-- beq $t1,$zero,loop: instrAddr = textBase+8, nextPc = textBase+12,
-- target = textBase (loop), offset = (textBase - (textBase+12))/4 = -3
#guard prog1.getD (textBase + 8#32) 0 = mkIT (4#32) (9#32) (0#32) (ofInt32 (-3))

-- jal loop: target = textBase, targetWordAddr = textBase/4
#guard prog1.getD (textBase + 12#32) 0 = (natToW32 0x03 <<< 26) ||| mkJT (textBase >>> 2)

-- `li` needing the lui+ori split: 0x12345 = 74565, hi16 = 1, lo16 = 0x2345.
def liSplitSrc : String := "li $t0, 0x12345\n"
def liSplitProg : Program :=
  match assemble liSplitSrc with
  | .ok p => p
  | .error _ => ∅

#guard liSplitProg.getD textBase 0 = mkIT (0x0f#32) (0#32) (1#32) (1#32)
#guard liSplitProg.getD (textBase + 4#32) 0 = mkIT (0x0d#32) (1#32) (8#32) (0x2345#32)

-- A negative `li`: -1 is within [-32768,-1], single `addiu` with imm = 0xffff.
def liNegSrc : String := "li $t0, -1\n"
def liNegProg : Program :=
  match assemble liNegSrc with
  | .ok p => p
  | .error _ => ∅

#guard liNegProg.getD textBase 0 = mkIT (0x09#32) (0#32) (8#32) (0xffff#32)
#guard liNegProg.size = 1

-- `.data` with `.word`/`.asciiz`/`.space`, big-endian byte layout at dataBase.
def dataSrc : String :=
".data\n" ++
"x: .word 0x01020304\n" ++
"y: .asciiz \"Hi\"\n" ++
"z: .space 4\n" ++
"w: .word 7\n"

def dataProg : Program :=
  match assemble dataSrc with
  | .ok p => p
  | .error _ => ∅

-- x at dataBase, full word stored as-is.
#guard dataProg.getD dataBase 0 = 0x01020304#32

-- y at dataBase+4: bytes 'H'(0x48) 'i'(0x69) 0x00 0x00 (padding byte unset -> 0)
#guard dataProg.getD (dataBase + 4#32) 0 = 0x48690000#32

-- z: .space 4 reserves dataBase+7 .. dataBase+10, no entries written (0 default);
-- w: .word 7 lands at dataBase+11 rounded up to 4-alignment = dataBase+12.
#guard dataProg.getD (dataBase + 12#32) 0 = 7#32
#guard dataProg.contains (dataBase + 8#32) = false

-- `move`/`nop` expansions.
def moveNopSrc : String := "move $t0, $t1\nnop\n"
def moveNopProg : Program :=
  match assemble moveNopSrc with
  | .ok p => p
  | .error _ => ∅

#guard moveNopProg.getD textBase 0 = mkRT (0#32) (9#32) (8#32) (0#32) (0x21#32)
#guard moveNopProg.getD (textBase + 4#32) 0 = 0#32

-- `syscall`: zero operands, all fields zero except funct = 0x0c (0x0000000C),
-- per MARS's own runtime table (`InstructionSet.java` lines 1188-1191,
-- "000000 ccccc ccccc ccccc ccccc 001100"); also matches `Instruction.lean`'s
-- `encode (.syscall 0#32)`.
def syscallSrc : String := "addi $t0, $zero, 1\nsyscall\n"
def syscallProg : Program :=
  match assemble syscallSrc with
  | .ok p => p
  | .error _ => ∅

#guard syscallProg.getD (textBase + 4#32) 0 = 0x0000000C#32
#guard decode (syscallProg.getD (textBase + 4#32) 0) = some (.syscall 0#32)

-- `movn`/`movz`: table-driven like `add`, 'rd, rs, rt' operand order.
def movSrc : String := "movn $t0, $t1, $t2\nmovz $t0, $t1, $t2\n"
def movProg : Program :=
  match assemble movSrc with
  | .ok p => p
  | .error _ => ∅

#guard movProg.getD textBase 0 = mkRT (9#32) (10#32) (8#32) (0#32) (0x0b#32)
#guard movProg.getD (textBase + 4#32) 0 = mkRT (9#32) (10#32) (8#32) (0#32) (0x0a#32)
#guard decode (movProg.getD textBase 0) = some (.movn 9#32 10#32 8#32)
#guard decode (movProg.getD (textBase + 4#32) 0) = some (.movz 9#32 10#32 8#32)

-- `sllv`/`srlv`/`srav $rd, $rt, $rs`: table-driven like `shift`, but the
-- third operand is a register (the shift amount), opcode 0.
def shiftvSrc : String := "sllv $t0, $t1, $t2\nsrlv $t0, $t1, $t2\nsrav $t0, $t1, $t2\n"
def shiftvProg : Program :=
  match assemble shiftvSrc with
  | .ok p => p
  | .error _ => ∅

#guard shiftvProg.getD textBase 0 = mkRT (10#32) (9#32) (8#32) (0#32) (0x04#32)
#guard shiftvProg.getD (textBase + 4#32) 0 = mkRT (10#32) (9#32) (8#32) (0#32) (0x06#32)
#guard shiftvProg.getD (textBase + 8#32) 0 = mkRT (10#32) (9#32) (8#32) (0#32) (0x07#32)
#guard decode (shiftvProg.getD textBase 0) = some (.sllv 8#32 9#32 10#32)
#guard decode (shiftvProg.getD (textBase + 4#32) 0) = some (.srlv 8#32 9#32 10#32)
#guard decode (shiftvProg.getD (textBase + 8#32) 0) = some (.srav 8#32 9#32 10#32)

-- `clo $rd, $rs` / `clz $rd, $rs`: SPECIAL2 opcode 0x1c, rt field duplicates rd.
def cloClzSrc : String := "clo $t0, $t1\nclz $t0, $t1\n"
def cloClzProg : Program :=
  match assemble cloClzSrc with
  | .ok p => p
  | .error _ => ∅

#guard cloClzProg.getD textBase 0 = (natToW32 0x1c <<< 26) ||| mkRT (9#32) (8#32) (8#32) (0#32) (0x21#32)
#guard cloClzProg.getD (textBase + 4#32) 0 = (natToW32 0x1c <<< 26) ||| mkRT (9#32) (8#32) (8#32) (0#32) (0x20#32)
#guard decode (cloClzProg.getD textBase 0) = some (.clo 9#32 8#32)
#guard decode (cloClzProg.getD (textBase + 4#32) 0) = some (.clz 9#32 8#32)

-- `mul $rd, $rs, $rt`: SPECIAL2 opcode 0x1c, plain rs/rt/rd shape (no
-- duplicated-field quirk, unlike clo/clz).
def mulSrc : String := "mul $t0, $t1, $t2\n"
def mulProg : Program :=
  match assemble mulSrc with
  | .ok p => p
  | .error _ => ∅

#guard mulProg.getD textBase 0 = (natToW32 0x1c <<< 26) ||| mkRT (9#32) (10#32) (8#32) (0#32) (0x02#32)
#guard decode (mulProg.getD textBase 0) = some (.mul 9#32 10#32 8#32)

-- `madd`/`maddu`/`msub`/`msubu $rs, $rt`: SPECIAL2 opcode 0x1c, `rs, rt`
-- shape (no `rd` field), cross-checked against `Instruction.encode`.
def multAccumSrc : String := "madd $t0, $t1\nmaddu $t0, $t1\nmsub $t0, $t1\nmsubu $t0, $t1\n"
def multAccumProg : Program :=
  match assemble multAccumSrc with
  | .ok p => p
  | .error _ => ∅

#guard multAccumProg.getD textBase 0 = encode (.madd 8#32 9#32)
#guard multAccumProg.getD (textBase + 4#32) 0 = encode (.maddu 8#32 9#32)
#guard multAccumProg.getD (textBase + 8#32) 0 = encode (.msub 8#32 9#32)
#guard multAccumProg.getD (textBase + 12#32) 0 = encode (.msubu 8#32 9#32)
#guard decode (multAccumProg.getD textBase 0) = some (.madd 8#32 9#32)
#guard decode (multAccumProg.getD (textBase + 4#32) 0) = some (.maddu 8#32 9#32)
#guard decode (multAccumProg.getD (textBase + 8#32) 0) = some (.msub 8#32 9#32)
#guard decode (multAccumProg.getD (textBase + 12#32) 0) = some (.msubu 8#32 9#32)
#guard (assemble "madd $t0, $t1, $t2\n").isOk = false
#guard (assemble "madd $t0\n").isOk = false

-- `seb $rd, $rt` / `seh $rd, $rt`: SPECIAL3 opcode 0x1f, funct 0x20, the
-- shamt-position sub-field (0x10/0x18) selects seb vs seh.
def sebSehSrc : String := "seb $t0, $t1\nseh $t0, $t1\n"
def sebSehProg : Program :=
  match assemble sebSehSrc with
  | .ok p => p
  | .error _ => ∅

#guard sebSehProg.getD textBase 0 = (natToW32 0x1f <<< 26) ||| mkRT (0#32) (9#32) (8#32) (0x10#32) (0x20#32)
#guard sebSehProg.getD (textBase + 4#32) 0 = (natToW32 0x1f <<< 26) ||| mkRT (0#32) (9#32) (8#32) (0x18#32) (0x20#32)
#guard decode (sebSehProg.getD textBase 0) = some (.seb 8#32 9#32)
#guard decode (sebSehProg.getD (textBase + 4#32) 0) = some (.seh 8#32 9#32)

-- `wsbh $rd, $rt`: SPECIAL3 opcode 0x1f, funct 0x20, same BSHFL family as
-- seb/seh, sub-field 0x02.
def wsbhSrc : String := "wsbh $t0, $t1\n"
def wsbhProg : Program :=
  match assemble wsbhSrc with
  | .ok p => p
  | .error _ => ∅

#guard wsbhProg.getD textBase 0 = (natToW32 0x1f <<< 26) ||| mkRT (0#32) (9#32) (8#32) (0x02#32) (0x20#32)
#guard decode (wsbhProg.getD textBase 0) = some (.wsbh 8#32 9#32)

-- `rotr $rd, $rt, $sa` / `rotrv $rd, $rt, $rs` (MIPS32r2): same opcode/funct
-- as srl/srlv, but overload the rs/shamt field to 0x01 to select rotate.
def rotrSrc : String := "rotr $t0, $t1, 5\nrotrv $t0, $t1, $t2\n"
def rotrProg : Program :=
  match assemble rotrSrc with
  | .ok p => p
  | .error _ => ∅

#guard rotrProg.getD textBase 0 = mkRT (1#32) (9#32) (8#32) (5#32) (0x02#32)
#guard rotrProg.getD (textBase + 4#32) 0 = mkRT (10#32) (9#32) (8#32) (1#32) (0x06#32)
#guard decode (rotrProg.getD textBase 0) = some (.rotr 8#32 9#32 5#32)
#guard decode (rotrProg.getD (textBase + 4#32) 0) = some (.rotrv 8#32 9#32 10#32)
-- rotr shamt out of range is rejected, same as shift's shamt check
#guard (assemble "rotr $t0, $t1, 32\n").isOk = false

-- `ext $rt, $rs, pos, size` / `ins $rt, $rs, pos, size` (MIPS32r2 bitfield
-- extract/insert): SPECIAL3 opcode 0x1f, funct 0x00/0x04. `pos`/`size` are
-- compile-time constants (pos=6, size=10 here), packed per the
-- `Instruction.lean`'s `.ext`/`.ins` docstrings (`rd`-position field is
-- `size-1=9` for ext, `pos+size-1=15` for ins).
def extInsSrc : String := "ext $t0, $t1, 6, 10\nins $t0, $t1, 6, 10\n"
def extInsProg : Program :=
  match assemble extInsSrc with
  | .ok p => p
  | .error _ => ∅

#guard extInsProg.getD textBase 0 = (natToW32 0x1f <<< 26) ||| mkRT (9#32) (8#32) (9#32) (6#32) (0x00#32)
#guard extInsProg.getD (textBase + 4#32) 0 = (natToW32 0x1f <<< 26) ||| mkRT (9#32) (8#32) (15#32) (6#32) (0x04#32)
#guard decode (extInsProg.getD textBase 0) = some (.ext 8#32 9#32 6#32 10#32)
#guard decode (extInsProg.getD (textBase + 4#32) 0) = some (.ins 8#32 9#32 6#32 10#32)
-- out-of-range pos/size, and pos+size > 32, are all rejected
#guard (assemble "ext $t0, $t1, 32, 1\n").isOk = false   -- pos out of range
#guard (assemble "ext $t0, $t1, 0, 33\n").isOk = false    -- size out of range
#guard (assemble "ext $t0, $t1, 30, 10\n").isOk = false   -- pos + size > 32
#guard (assemble "ins $t0, $t1, 30, 10\n").isOk = false   -- pos + size > 32

-- `jr $rs` / `jalr $rd, $rs`: real MIPS32 register-indirect jump/call,
-- opcode 0, funct 0x08/0x09. Also covers the `jalr $rs` one-operand sugar
-- (rd defaults to $ra = 31).
def jrJalrSrc : String := "jr $ra\njalr $t0, $t1\njalr $t2\n"
def jrJalrProg : Program :=
  match assemble jrJalrSrc with
  | .ok p => p
  | .error _ => ∅

#guard jrJalrProg.getD textBase 0 = mkRT (31#32) (0#32) (0#32) (0#32) (0x08#32)
#guard jrJalrProg.getD (textBase + 4#32) 0 = mkRT (9#32) (0#32) (8#32) (0#32) (0x09#32)
#guard jrJalrProg.getD (textBase + 8#32) 0 = mkRT (10#32) (0#32) (31#32) (0#32) (0x09#32)
#guard decode (jrJalrProg.getD textBase 0) = some (.jr 31#32)
#guard decode (jrJalrProg.getD (textBase + 4#32) 0) = some (.jalr 9#32 8#32)
#guard decode (jrJalrProg.getD (textBase + 8#32) 0) = some (.jalr 10#32 31#32)
-- operand-count errors: zero/three operands are rejected for both mnemonics.
#guard (assemble "jr\n").isOk = false
#guard (assemble "jr $t0, $t1\n").isOk = false
#guard (assemble "jalr\n").isOk = false
#guard (assemble "jalr $t0, $t1, $t2\n").isOk = false

-- `mthi`/`mtlo $rs`: opcode 0, funct 0x11/0x13, single-operand `rs` shape
-- (same as `jr`), cross-checked against `Instruction.encode`.
def mthiMtloSrc : String := "mthi $t0\nmtlo $t0\n"
def mthiMtloProg : Program :=
  match assemble mthiMtloSrc with
  | .ok p => p
  | .error _ => ∅

#guard mthiMtloProg.getD textBase 0 = encode (.mthi 8#32)
#guard mthiMtloProg.getD (textBase + 4#32) 0 = encode (.mtlo 8#32)
#guard decode (mthiMtloProg.getD textBase 0) = some (.mthi 8#32)
#guard decode (mthiMtloProg.getD (textBase + 4#32) 0) = some (.mtlo 8#32)
#guard (assemble "mthi\n").isOk = false
#guard (assemble "mthi $t0, $t1\n").isOk = false

-- `break`: zero operands, all fields zero except funct = 0x0d (0x0000000D);
-- real MIPS32 encoding (the funct value immediately after `syscall`'s
-- 0x0c) -- see `Instruction.lean`'s `encode (.break 0#32)`.
def breakSrc : String := "break\n"
def breakProg : Program :=
  match assemble breakSrc with
  | .ok p => p
  | .error _ => ∅

#guard breakProg.getD textBase 0 = 0x0000000D#32
#guard decode (breakProg.getD textBase 0) = some (.break 0#32)
#guard (assemble "break $t0\n").isOk = false

-- trap-on-condition family: `rs, rt` operands, same shape as `mult`/`div`.
def trapSrc : String := "teq $t0, $t1\ntne $t0, $t1\ntlt $t0, $t1\ntge $t0, $t1\ntltu $t0, $t1\ntgeu $t0, $t1\n"
def trapProg : Program :=
  match assemble trapSrc with
  | .ok p => p
  | .error _ => ∅

#guard trapProg.getD textBase 0 = mkRT (8#32) (9#32) (0#32) (0#32) (0x34#32)
#guard decode (trapProg.getD textBase 0) = some (.teq 8#32 9#32 0#32)
#guard trapProg.getD (textBase + 4#32) 0 = mkRT (8#32) (9#32) (0#32) (0#32) (0x36#32)
#guard decode (trapProg.getD (textBase + 4#32) 0) = some (.tne 8#32 9#32 0#32)
#guard trapProg.getD (textBase + 8#32) 0 = mkRT (8#32) (9#32) (0#32) (0#32) (0x32#32)
#guard decode (trapProg.getD (textBase + 8#32) 0) = some (.tlt 8#32 9#32 0#32)
#guard trapProg.getD (textBase + 12#32) 0 = mkRT (8#32) (9#32) (0#32) (0#32) (0x30#32)
#guard decode (trapProg.getD (textBase + 12#32) 0) = some (.tge 8#32 9#32 0#32)
#guard trapProg.getD (textBase + 16#32) 0 = mkRT (8#32) (9#32) (0#32) (0#32) (0x33#32)
#guard decode (trapProg.getD (textBase + 16#32) 0) = some (.tltu 8#32 9#32 0#32)
#guard trapProg.getD (textBase + 20#32) 0 = mkRT (8#32) (9#32) (0#32) (0#32) (0x31#32)
#guard decode (trapProg.getD (textBase + 20#32) 0) = some (.tgeu 8#32 9#32 0#32)
#guard (assemble "teq $t0\n").isOk = false

-- REGIMM zero-comparison branches: `bltz`/`bgez`/`bltzal`/`bgezal` all
-- share opcode 0x01 (distinguished only by the `rt` field — see
-- `Instruction.lean`/`docs/spec/INSTRUCTION-REF.md`); operand shape is
-- `rs, target`, same as `blez`/`bgtz`.
def regimmSrc : String :=
"loop: bltz $t0, loop\n" ++
"bgez $t0, loop\n" ++
"bltzal $t0, loop\n" ++
"bgezal $t0, loop\n"
def regimmProg : Program :=
  match assemble regimmSrc with
  | .ok p => p
  | .error _ => ∅

-- `loop: bltz $t0, loop`: instrAddr = textBase = target; nextPc = +4;
-- offset = (target - nextPc)/4 = -1.
#guard regimmProg.getD textBase 0 = mkIT (0x01#32) (8#32) (0x00#32) (ofInt32 (-1))
#guard decode (regimmProg.getD textBase 0) = some (.bltz 8#32 0xffff#32)
-- `bgez $t0, loop`: instrAddr = textBase+4, nextPc = textBase+8,
-- target = textBase (loop); offset = (0 - 8)/4 = -2.
#guard regimmProg.getD (textBase + 4#32) 0 = mkIT (0x01#32) (8#32) (0x01#32) (ofInt32 (-2))
#guard decode (regimmProg.getD (textBase + 4#32) 0) = some (.bgez 8#32 0xfffe#32)
-- `bltzal $t0, loop`: instrAddr = textBase+8, nextPc = textBase+12;
-- offset = (0 - 12)/4 = -3.
#guard regimmProg.getD (textBase + 8#32) 0 = mkIT (0x01#32) (8#32) (0x10#32) (ofInt32 (-3))
#guard decode (regimmProg.getD (textBase + 8#32) 0) = some (.bltzal 8#32 0xfffd#32)
-- `bgezal $t0, loop`: instrAddr = textBase+12, nextPc = textBase+16;
-- offset = (0 - 16)/4 = -4.
#guard regimmProg.getD (textBase + 12#32) 0 = mkIT (0x01#32) (8#32) (0x11#32) (ofInt32 (-4))
#guard decode (regimmProg.getD (textBase + 12#32) 0) = some (.bgezal 8#32 0xfffc#32)
#guard (assemble "bltz $t0\n").isOk = false

-- "Branch likely" family (real MIPS32; deprecated in MIPS32, removed in
-- Release 6 -- docs/spec/MIPS-COVERAGE-GAPS.md \u00a73.3): `beql`/`bnel` share
-- `beq`/`bne`'s `rs, rt, target` shape; `blezl`/`bgtzl`/`bltzl`/`bgezl`/
-- `bltzall`/`bgezall` share `blez`/`bgtz`/`bltz`/`bgez`/`bltzal`/`bgezal`'s
-- `rs, target` shape -- same table-driven `bTable` encoding as every other
-- branch in this file.
def beqlBnelSrc : String := "beql $t0, $t1, loop\nbnel $t0, $t1, loop\nloop: nop\n"
def beqlBnelProg : Program :=
  match assemble beqlBnelSrc with
  | .ok p => p
  | .error _ => ∅

-- `beql $t0, $t1, loop`: instrAddr = textBase, nextPc = textBase+4,
-- target = textBase+8 (loop); offset = (8 - 4)/4 = 1.
#guard beqlBnelProg.getD textBase 0 = mkIT (0x14#32) (8#32) (9#32) (ofInt32 1)
#guard decode (beqlBnelProg.getD textBase 0) = some (.beql 8#32 9#32 1#32)
-- `bnel $t0, $t1, loop`: instrAddr = textBase+4, nextPc = textBase+8,
-- target = textBase+8 (loop); offset = (8 - 8)/4 = 0.
#guard beqlBnelProg.getD (textBase + 4#32) 0 = mkIT (0x15#32) (8#32) (9#32) (ofInt32 0)
#guard decode (beqlBnelProg.getD (textBase + 4#32) 0) = some (.bnel 8#32 9#32 0#32)
#guard (assemble "beql $t0, $t1\n").isOk = false

def blezlBgtzlSrc : String := "loop: blezl $t0, loop\nbgtzl $t0, loop\n"
def blezlBgtzlProg : Program :=
  match assemble blezlBgtzlSrc with
  | .ok p => p
  | .error _ => ∅

-- `loop: blezl $t0, loop`: instrAddr = textBase = target; nextPc = +4;
-- offset = (target - nextPc)/4 = -1.
#guard blezlBgtzlProg.getD textBase 0 = mkIT (0x16#32) (8#32) (0#32) (ofInt32 (-1))
#guard decode (blezlBgtzlProg.getD textBase 0) = some (.blezl 8#32 0xffff#32)
-- `bgtzl $t0, loop`: instrAddr = textBase+4, nextPc = textBase+8,
-- target = textBase (loop); offset = (0 - 8)/4 = -2.
#guard blezlBgtzlProg.getD (textBase + 4#32) 0 = mkIT (0x17#32) (8#32) (0#32) (ofInt32 (-2))
#guard decode (blezlBgtzlProg.getD (textBase + 4#32) 0) = some (.bgtzl 8#32 0xfffe#32)
#guard (assemble "blezl $t0, $t1, loop\n").isOk = false

-- REGIMM branch-likely zero-comparison family: `bltzl`/`bgezl`/`bltzall`/
-- `bgezall` all share opcode 0x01 (distinguished by the `rt` field, same
-- as `bltz`/`bgez`/`bltzal`/`bgezal` above); operand shape is `rs, target`.
def regimmLikelySrc : String :=
"loop: bltzl $t0, loop\n" ++
"bgezl $t0, loop\n" ++
"bltzall $t0, loop\n" ++
"bgezall $t0, loop\n"
def regimmLikelyProg : Program :=
  match assemble regimmLikelySrc with
  | .ok p => p
  | .error _ => ∅

-- `loop: bltzl $t0, loop`: instrAddr = textBase = target; nextPc = +4;
-- offset = (target - nextPc)/4 = -1.
#guard regimmLikelyProg.getD textBase 0 = mkIT (0x01#32) (8#32) (0x02#32) (ofInt32 (-1))
#guard decode (regimmLikelyProg.getD textBase 0) = some (.bltzl 8#32 0xffff#32)
-- `bgezl $t0, loop`: instrAddr = textBase+4, nextPc = textBase+8,
-- target = textBase (loop); offset = (0 - 8)/4 = -2.
#guard regimmLikelyProg.getD (textBase + 4#32) 0 = mkIT (0x01#32) (8#32) (0x03#32) (ofInt32 (-2))
#guard decode (regimmLikelyProg.getD (textBase + 4#32) 0) = some (.bgezl 8#32 0xfffe#32)
-- `bltzall $t0, loop`: instrAddr = textBase+8, nextPc = textBase+12;
-- offset = (0 - 12)/4 = -3.
#guard regimmLikelyProg.getD (textBase + 8#32) 0 = mkIT (0x01#32) (8#32) (0x12#32) (ofInt32 (-3))
#guard decode (regimmLikelyProg.getD (textBase + 8#32) 0) = some (.bltzall 8#32 0xfffd#32)
-- `bgezall $t0, loop`: instrAddr = textBase+12, nextPc = textBase+16;
-- offset = (0 - 16)/4 = -4.
#guard regimmLikelyProg.getD (textBase + 12#32) 0 = mkIT (0x01#32) (8#32) (0x13#32) (ofInt32 (-4))
#guard decode (regimmLikelyProg.getD (textBase + 12#32) 0) = some (.bgezall 8#32 0xfffc#32)
#guard (assemble "bltzl $t0\n").isOk = false

-- Trap-immediate family: `rs, imm` operands (a plain immediate, not a
-- branch target), same REGIMM opcode 0x01 as `bltz`/etc. above, selected
-- by the `rt` field (docs/spec/MIPS-COVERAGE-GAPS.md section 3.8).
def trapImmSrc : String :=
  "teqi $t0, 5\n" ++ "tnei $t0, 5\n" ++ "tgei $t0, 5\n" ++
  "tgeiu $t0, 5\n" ++ "tlti $t0, 5\n" ++ "tltiu $t0, 5\n"
def trapImmProg : Program :=
  match assemble trapImmSrc with
  | .ok p => p
  | .error _ => ∅

#guard trapImmProg.getD textBase 0 = mkIT (0x01#32) (8#32) (0x0c#32) (5#32)
#guard decode (trapImmProg.getD textBase 0) = some (.teqi 8#32 5#32)
#guard trapImmProg.getD (textBase + 4#32) 0 = mkIT (0x01#32) (8#32) (0x0e#32) (5#32)
#guard decode (trapImmProg.getD (textBase + 4#32) 0) = some (.tnei 8#32 5#32)
#guard trapImmProg.getD (textBase + 8#32) 0 = mkIT (0x01#32) (8#32) (0x08#32) (5#32)
#guard decode (trapImmProg.getD (textBase + 8#32) 0) = some (.tgei 8#32 5#32)
#guard trapImmProg.getD (textBase + 12#32) 0 = mkIT (0x01#32) (8#32) (0x09#32) (5#32)
#guard decode (trapImmProg.getD (textBase + 12#32) 0) = some (.tgeiu 8#32 5#32)
#guard trapImmProg.getD (textBase + 16#32) 0 = mkIT (0x01#32) (8#32) (0x0a#32) (5#32)
#guard decode (trapImmProg.getD (textBase + 16#32) 0) = some (.tlti 8#32 5#32)
#guard trapImmProg.getD (textBase + 20#32) 0 = mkIT (0x01#32) (8#32) (0x0b#32) (5#32)
#guard decode (trapImmProg.getD (textBase + 20#32) 0) = some (.tltiu 8#32 5#32)
#guard (assemble "teqi $t0\n").isOk = false

-- Coprocessor-1 (FPU) mnemonics: cross-checked word-for-word against
-- `Instruction.encode` (an independent encoding path from this assembler's
-- `cop1RtWord`/`itWord`), covering registers/`$fN` parsing and every form.
def cop1Src : String :=
"mtc1 $t0, $f3\n" ++
"mfc1 $t1, $f3\n" ++
"lwc1 $f5, 4($sp)\n" ++
"swc1 $f5, 4($sp)\n" ++
"add.s $f8, $f7, $f6\n" ++
"sub.s $f8, $f7, $f6\n" ++
"mul.s $f8, $f7, $f6\n" ++
"div.s $f8, $f7, $f6\n" ++
"mov.s $f8, $f7\n" ++
"cvt.s.w $f8, $f7\n" ++
"cvt.w.s $f8, $f7\n" ++
"c.eq.s $f7, $f6\n" ++
"c.lt.s $f7, $f6\n" ++
"c.le.s $f7, $f6\n" ++
"loop: bc1t loop\n" ++
"bc1f loop\n" ++
"cfc1 $t0, $f31\n" ++
"ctc1 $t0, $f31\n" ++
"sqrt.s $f8, $f7\n" ++
"abs.s $f8, $f7\n" ++
"neg.s $f8, $f7\n" ++
"round.w.s $f8, $f7\n" ++
"trunc.w.s $f8, $f7\n" ++
"ceil.w.s $f8, $f7\n" ++
"floor.w.s $f8, $f7\n" ++
"c.f.s $f7, $f6\n" ++
"c.un.s $f7, $f6\n" ++
"c.ueq.s $f7, $f6\n" ++
"c.olt.s $f7, $f6\n" ++
"c.ult.s $f7, $f6\n" ++
"c.ole.s $f7, $f6\n" ++
"c.ule.s $f7, $f6\n"

def cop1Prog : Program :=
  match assemble cop1Src with
  | .ok p => p
  | .error _ => ∅

#guard cop1Prog.getD textBase 0 = encode (.mtc1 8#32 3#32)
#guard cop1Prog.getD (textBase + 4#32) 0 = encode (.mfc1 9#32 3#32)
#guard cop1Prog.getD (textBase + 8#32) 0 = encode (.lwc1 29#32 5#32 4#32)
#guard cop1Prog.getD (textBase + 12#32) 0 = encode (.swc1 29#32 5#32 4#32)
#guard cop1Prog.getD (textBase + 16#32) 0 = encode (.addS 8#32 7#32 6#32)
#guard cop1Prog.getD (textBase + 20#32) 0 = encode (.subS 8#32 7#32 6#32)
#guard cop1Prog.getD (textBase + 24#32) 0 = encode (.mulS 8#32 7#32 6#32)
#guard cop1Prog.getD (textBase + 28#32) 0 = encode (.divS 8#32 7#32 6#32)
#guard cop1Prog.getD (textBase + 32#32) 0 = encode (.movS 8#32 7#32)
#guard cop1Prog.getD (textBase + 36#32) 0 = encode (.cvtSW 8#32 7#32)
#guard cop1Prog.getD (textBase + 40#32) 0 = encode (.cvtWS 8#32 7#32)
#guard cop1Prog.getD (textBase + 44#32) 0 = encode (.cCondS 2#32 0#32 7#32 6#32)
#guard cop1Prog.getD (textBase + 48#32) 0 = encode (.cCondS 12#32 0#32 7#32 6#32)
#guard cop1Prog.getD (textBase + 52#32) 0 = encode (.cCondS 14#32 0#32 7#32 6#32)
-- `loop: bc1t loop`: instrAddr = textBase+56 = target; nextPc = +4;
-- offset = (target - nextPc)/4 = -1.
#guard cop1Prog.getD (textBase + 56#32) 0 = encode (.bc1t 0#32 (ofInt32 (-1)))
-- `bc1f loop`: instrAddr = textBase+60, nextPc = textBase+64, target = loop
-- (textBase+56); offset = (56 - 64)/4 = -2.
#guard cop1Prog.getD (textBase + 60#32) 0 = encode (.bc1f 0#32 (ofInt32 (-2)))
-- every emitted COP1 word also round-trips through `decode`
#guard decode (cop1Prog.getD textBase 0) = some (.mtc1 8#32 3#32)
#guard decode (cop1Prog.getD (textBase + 16#32) 0) = some (.addS 8#32 7#32 6#32)
-- `decode`'s `imm` is the raw 16-bit field (zero-extended), not the
-- sign-extended offset value, per `Instruction.lean`'s "raw field" convention
-- (same as `beq`/`bne`'s `imm`); -1 as that raw 16-bit field is 0xffff.
#guard decode (cop1Prog.getD (textBase + 56#32) 0) = some (.bc1t 0#32 0xffff#32)
-- v1.x addition mnemonics appended after `bc1f loop` (textBase+64 onward,
-- unlabeled so earlier addresses/offsets above are unaffected)
#guard cop1Prog.getD (textBase + 64#32) 0 = encode (.cfc1 8#32 31#32)
#guard cop1Prog.getD (textBase + 68#32) 0 = encode (.ctc1 8#32 31#32)
#guard cop1Prog.getD (textBase + 72#32) 0 = encode (.sqrtS 8#32 7#32)
#guard cop1Prog.getD (textBase + 76#32) 0 = encode (.absS 8#32 7#32)
#guard cop1Prog.getD (textBase + 80#32) 0 = encode (.negS 8#32 7#32)
#guard cop1Prog.getD (textBase + 84#32) 0 = encode (.roundWS 8#32 7#32)
#guard cop1Prog.getD (textBase + 88#32) 0 = encode (.truncWS 8#32 7#32)
#guard cop1Prog.getD (textBase + 92#32) 0 = encode (.ceilWS 8#32 7#32)
#guard cop1Prog.getD (textBase + 96#32) 0 = encode (.floorWS 8#32 7#32)
#guard cop1Prog.getD (textBase + 100#32) 0 = encode (.cCondS 0#32 0#32 7#32 6#32)
#guard cop1Prog.getD (textBase + 104#32) 0 = encode (.cCondS 1#32 0#32 7#32 6#32)
#guard cop1Prog.getD (textBase + 108#32) 0 = encode (.cCondS 3#32 0#32 7#32 6#32)
#guard cop1Prog.getD (textBase + 112#32) 0 = encode (.cCondS 4#32 0#32 7#32 6#32)
#guard cop1Prog.getD (textBase + 116#32) 0 = encode (.cCondS 5#32 0#32 7#32 6#32)
#guard cop1Prog.getD (textBase + 120#32) 0 = encode (.cCondS 6#32 0#32 7#32 6#32)
#guard cop1Prog.getD (textBase + 124#32) 0 = encode (.cCondS 7#32 0#32 7#32 6#32)
-- a couple of the new words also round-trip through `decode`
#guard decode (cop1Prog.getD (textBase + 64#32) 0) = some (.cfc1 8#32 31#32)
#guard decode (cop1Prog.getD (textBase + 72#32) 0) = some (.sqrtS 8#32 7#32)
#guard decode (cop1Prog.getD (textBase + 100#32) 0) = some (.cCondS 0#32 0#32 7#32 6#32)

-- an unknown `$f` register is a `badRegister` error
#guard (assemble "mov.s $f8, $f32\n").isOk = false

-- Coprocessor-1 (FPU) double-precision mnemonics (v2 addition): same
-- cross-check style as `cop1Src` above -- every emitted word is checked
-- word-for-word against `Instruction.encode`.
def cop1DSrc : String :=
"ldc1 $f5, 4($sp)\n" ++
"sdc1 $f5, 4($sp)\n" ++
"add.d $f8, $f7, $f6\n" ++
"sub.d $f8, $f7, $f6\n" ++
"mul.d $f8, $f7, $f6\n" ++
"div.d $f8, $f7, $f6\n" ++
"mov.d $f8, $f7\n" ++
"sqrt.d $f8, $f7\n" ++
"abs.d $f8, $f7\n" ++
"neg.d $f8, $f7\n" ++
"cvt.d.s $f8, $f7\n" ++
"cvt.s.d $f8, $f7\n" ++
"cvt.d.w $f8, $f7\n" ++
"cvt.w.d $f8, $f7\n" ++
"c.eq.d $f7, $f6\n" ++
"c.lt.d $f7, $f6\n" ++
"c.le.d $f7, $f6\n" ++
"c.f.d $f7, $f6\n" ++
"c.un.d $f7, $f6\n" ++
"c.ueq.d $f7, $f6\n" ++
"c.olt.d $f7, $f6\n" ++
"c.ult.d $f7, $f6\n" ++
"c.ole.d $f7, $f6\n" ++
"c.ule.d $f7, $f6\n"

def cop1DProg : Program :=
  match assemble cop1DSrc with
  | .ok p => p
  | .error _ => ∅

#guard cop1DProg.getD textBase 0 = encode (.ldc1 29#32 5#32 4#32)
#guard cop1DProg.getD (textBase + 4#32) 0 = encode (.sdc1 29#32 5#32 4#32)
#guard cop1DProg.getD (textBase + 8#32) 0 = encode (.addD 8#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 12#32) 0 = encode (.subD 8#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 16#32) 0 = encode (.mulD 8#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 20#32) 0 = encode (.divD 8#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 24#32) 0 = encode (.movD 8#32 7#32)
#guard cop1DProg.getD (textBase + 28#32) 0 = encode (.sqrtD 8#32 7#32)
#guard cop1DProg.getD (textBase + 32#32) 0 = encode (.absD 8#32 7#32)
#guard cop1DProg.getD (textBase + 36#32) 0 = encode (.negD 8#32 7#32)
#guard cop1DProg.getD (textBase + 40#32) 0 = encode (.cvtDS 8#32 7#32)
#guard cop1DProg.getD (textBase + 44#32) 0 = encode (.cvtSD 8#32 7#32)
#guard cop1DProg.getD (textBase + 48#32) 0 = encode (.cvtDW 8#32 7#32)
#guard cop1DProg.getD (textBase + 52#32) 0 = encode (.cvtWD 8#32 7#32)
#guard cop1DProg.getD (textBase + 56#32) 0 = encode (.cCondD 2#32 0#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 60#32) 0 = encode (.cCondD 12#32 0#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 64#32) 0 = encode (.cCondD 14#32 0#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 68#32) 0 = encode (.cCondD 0#32 0#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 72#32) 0 = encode (.cCondD 1#32 0#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 76#32) 0 = encode (.cCondD 3#32 0#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 80#32) 0 = encode (.cCondD 4#32 0#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 84#32) 0 = encode (.cCondD 5#32 0#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 88#32) 0 = encode (.cCondD 6#32 0#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 92#32) 0 = encode (.cCondD 7#32 0#32 7#32 6#32)
-- every emitted double-precision word also round-trips through `decode`
#guard decode (cop1DProg.getD textBase 0) = some (.ldc1 29#32 5#32 4#32)
#guard decode (cop1DProg.getD (textBase + 8#32) 0) = some (.addD 8#32 7#32 6#32)
#guard decode (cop1DProg.getD (textBase + 40#32) 0) = some (.cvtDS 8#32 7#32)
#guard decode (cop1DProg.getD (textBase + 56#32) 0) = some (.cCondD 2#32 0#32 7#32 6#32)

-- `ll`/`sc`: identical `rt, offset(rs)` parsing to `lw`/`sw`, cross-checked
-- against `Instruction.encode`.
def llscSrc : String :=
"ll $t0, 4($sp)\n" ++
"sc $t0, 4($sp)\n"

def llscProg : Program :=
  match assemble llscSrc with
  | .ok p => p
  | .error _ => ∅

#guard llscProg.getD textBase 0 = encode (.ll 29#32 8#32 4#32)
#guard llscProg.getD (textBase + 4#32) 0 = encode (.sc 29#32 8#32 4#32)
#guard decode (llscProg.getD textBase 0) = some (.ll 29#32 8#32 4#32)
#guard decode (llscProg.getD (textBase + 4#32) 0) = some (.sc 29#32 8#32 4#32)

-- Coprocessor-0 (CP0) register move / execution control: `mfc0`/`mtc0`
-- (`$rt, rd` with `rd` a plain numeric CP0 register reference, e.g.
-- `mfc0 $t0, 12` -- this model has no named CP0 register aliases) and
-- `eret`/`wait` (zero operands, like `break`). Cross-checked word-for-word
-- against `Instruction.encode`, same convention as the COP1 block above.
def cop0Src : String :=
"mfc0 $t0, 12\n" ++
"mtc0 $t0, 12\n" ++
"mfc0 $t1, 13\n" ++
"mtc0 $t1, 13\n" ++
"mfc0 $t2, 14\n" ++
"mtc0 $t2, 14\n" ++
"eret\n" ++
"wait\n"

def cop0Prog : Program :=
  match assemble cop0Src with
  | .ok p => p
  | .error _ => ∅

#guard cop0Prog.getD textBase 0 = encode (.mfc0 8#32 12#32 0#32)
#guard cop0Prog.getD (textBase + 4#32) 0 = encode (.mtc0 8#32 12#32 0#32)
#guard cop0Prog.getD (textBase + 8#32) 0 = encode (.mfc0 9#32 13#32 0#32)
#guard cop0Prog.getD (textBase + 12#32) 0 = encode (.mtc0 9#32 13#32 0#32)
#guard cop0Prog.getD (textBase + 16#32) 0 = encode (.mfc0 10#32 14#32 0#32)
#guard cop0Prog.getD (textBase + 20#32) 0 = encode (.mtc0 10#32 14#32 0#32)
#guard cop0Prog.getD (textBase + 24#32) 0 = encode .eret
#guard cop0Prog.getD (textBase + 28#32) 0 = encode (.wait 0#32)
-- every emitted CP0 word also round-trips through `decode`
#guard decode (cop0Prog.getD textBase 0) = some (.mfc0 8#32 12#32 0#32)
#guard decode (cop0Prog.getD (textBase + 4#32) 0) = some (.mtc0 8#32 12#32 0#32)
#guard decode (cop0Prog.getD (textBase + 24#32) 0) = some .eret
#guard decode (cop0Prog.getD (textBase + 28#32) 0) = some (.wait 0#32)
-- operand errors: wrong operand count, and a non-numeric `rd` token
-- (`mfc0`/`mtc0`'s second operand is a raw register number, not a `$`-named
-- register -- `parseCopRegister` accepts only `$N`/`N`, not GPR aliases).
#guard (assemble "mfc0 $t0\n").isOk = false
#guard (assemble "mfc0 $t0, $t1\n").isOk = false
#guard (assemble "mfc0 $t0, 32\n").isOk = false
#guard (assemble "eret $t0\n").isOk = false
#guard (assemble "wait $t0\n").isOk = false
#guard (assemble "wait 1, 2\n").isOk = false
-- `rdhwr $rt, $rd` (MIPS32r2, SPECIAL3 funct 0x3b): `rdhwr $3, $29` is 0x7c03e83b (the LLVM
-- encoding of the same line); the hardware register is `$N` or `N`; no `sel` operand before Release 6.
#guard (assemble "rdhwr $3, $29\n").toOption.map (·.getD textBase 0) = some 0x7c03e83b#32
#guard (assemble "rdhwr $t0, 2\n").toOption.map (·.getD textBase 0) = some (encode (.rdhwr 8#32 2#32))
#guard (assemble "rdhwr $t0, $2\n").toOption.map (fun p => decode (p.getD textBase 0)) =
  some (some (.rdhwr 8#32 2#32))
#guard (assemble "rdhwr $t0\n").isOk = false
#guard (assemble "rdhwr $t0, $2, 0\n").isOk = false
#guard (assemble "rdhwr $t0, 32\n").isOk = false
-- `lwl`/`lwr`/`swl`/`swr`: identical `rt, offset(rs)` parsing to `lw`/`sw`,
-- cross-checked against `Instruction.encode`.
def unalignedSrc : String :=
"lwl $t0, 1($sp)\n" ++
"lwr $t0, 4($sp)\n" ++
"swl $t0, 1($sp)\n" ++
"swr $t0, 4($sp)\n"

def unalignedProg : Program :=
  match assemble unalignedSrc with
  | .ok p => p
  | .error _ => ∅

#guard unalignedProg.getD textBase 0 = encode (.lwl 29#32 8#32 1#32)
#guard unalignedProg.getD (textBase + 4#32) 0 = encode (.lwr 29#32 8#32 4#32)
#guard unalignedProg.getD (textBase + 8#32) 0 = encode (.swl 29#32 8#32 1#32)
#guard unalignedProg.getD (textBase + 12#32) 0 = encode (.swr 29#32 8#32 4#32)
#guard decode (unalignedProg.getD textBase 0) = some (.lwl 29#32 8#32 1#32)
#guard decode (unalignedProg.getD (textBase + 4#32) 0) = some (.lwr 29#32 8#32 4#32)
#guard decode (unalignedProg.getD (textBase + 8#32) 0) = some (.swl 29#32 8#32 1#32)
#guard decode (unalignedProg.getD (textBase + 12#32) 0) = some (.swr 29#32 8#32 4#32)

-- `sync`/`synci`: real MIPS32 memory-ordering barrier / instruction-cache-
-- flush hint, completing the atomics story alongside `ll`/`sc` above (see
-- `docs/spec/MIPS-COVERAGE-GAPS.md` section 3.7 and
-- `docs/spec/INSTRUCTION-REF.md`). `sync` is zero-operand like `break`;
-- `synci` takes `offset(rs)` only, identical addressing syntax to `lw`/`sw`
-- but with no destination/source register operand.
def syncSrc : String :=
"sync\n" ++
"synci 4($sp)\n"

def syncProg : Program :=
  match assemble syncSrc with
  | .ok p => p
  | .error _ => ∅

#guard syncProg.getD textBase 0 = encode (.sync 0#32)
#guard syncProg.getD (textBase + 4#32) 0 = encode (.synci 29#32 4#32)
-- both emitted words also round-trip through `decode`
#guard decode (syncProg.getD textBase 0) = some (.sync 0#32)
#guard decode (syncProg.getD (textBase + 4#32) 0) = some (.synci 29#32 4#32)
-- operand errors: `sync` takes no operands; `synci` requires the
-- `offset(rs)` memory-operand syntax, not a bare register.
#guard (assemble "sync $t0\n").isOk = false
#guard (assemble "synci $t0\n").isOk = false
#guard (assemble "synci $t0, 4($sp)\n").isOk = false

-- One error case per major `AsmError` kind.
#guard (assemble "frobnicate $t0, $t1\n").isOk = false

#guard (assemble "add $t0, $bogus, $t1\n").isOk = false

#guard (assemble "j nosuchlabel\n").isOk = false

#guard (assemble "li $t0, notanumber\n").isOk = false

#guard (assemble ".bogus 1,2,3\n").isOk = false

#guard (assemble "add $t0, $t1\n").isOk = false

#guard (assemble "foo: add $t0,$zero,$zero\nfoo: add $t1,$zero,$zero\n").isOk = false

-- ====================================================================
-- ## Audit-fix tests (B1-B9) and syntax additions
-- ====================================================================
-- Every expected word below was produced by this assembler and, wherever
-- MARS 4.5 accepts the same source, cross-checked against
-- `java -jar vendor/mars/Mars4_5.jar a dump .text HexText` (differences are
-- noted inline).

/-- Source text from lines. -/
private def srcLines (ls : List String) : String := String.intercalate "\n" ls ++ "\n"

/-- The `n` consecutive words at `addr` (absent words read as 0); `none`
if assembly fails. -/
private def asmWords (src : String) (addr : W32) (n : Nat) : Option (List W32) :=
  match assemble src with
  | .ok p => some ((List.range n).map (fun i => p.getD (addr + natToW32 (4 * i)) 0))
  | .error _ => none

/-- The contiguous run of words starting at `textBase`; `none` if assembly
fails. -/
private def asmText (src : String) : Option (List W32) :=
  match assemble src with
  | .ok p =>
    some (((List.range p.size).map (fun i => p.get? (textBase + natToW32 (4 * i)))).takeWhile
      Option.isSome |>.filterMap id)
  | .error _ => none

private def asmFails (src : String) : Bool := !(assemble src).isOk

/-- Line number carried by the error (`none` if assembly succeeds). -/
private def asmErrLine (src : String) : Option Nat :=
  match assemble src with
  | .ok _ => none
  | .error (.unknownMnemonic _ l) | .error (.badRegister _ l) | .error (.undefinedLabel _ l)
  | .error (.badImmediate _ l) | .error (.badDirective _ l) | .error (.badOperand _ l)
  | .error (.duplicateLabel _ l) => some l

-- --------------------------------------------------------------------
-- B1: immediates are range-checked, never truncated
-- --------------------------------------------------------------------
#guard asmFails "addiu $a0,$t0,70000\n"
#guard asmFails "addiu $a0,$t0,-32769\n"
#guard asmFails "addi $a0,$t0,32768\n"
#guard asmFails "slti $a0,$t0,0xffff\n"
#guard asmFails "sltiu $a0,$t0,65535\n"
#guard asmText "addiu $a0,$t0,32767\naddiu $a0,$t0,-32768\nsltiu $a0,$t0,-1\n"
  = some [0x25047fff#32, 0x25048000#32, 0x2d04ffff#32]
#guard asmFails "andi $a0,$t0,-1\n"
#guard asmFails "ori $a0,$t0,65536\n"
#guard asmFails "xori $a0,$t0,-1\n"
#guard asmText "andi $a0,$t0,65535\nxori $a0,$t0,0xffff\nori $a0,$t0,0\n"
  = some [0x3104ffff#32, 0x3904ffff#32, 0x35040000#32]
#guard asmFails "lui $t0,0x12345\n"
#guard asmFails "lui $t0,-1\n"
#guard asmText "lui $t0,0xffff\n" = some [0x3c08ffff#32]
#guard asmFails "lw $t0,32768($sp)\n"
#guard asmFails "sw $t0,-32769($sp)\n"
#guard asmFails "lwc1 $f2,32768($sp)\n"
#guard asmFails "sdc1 $f2,-32769($sp)\n"
#guard asmFails "synci 32768($t0)\n"
#guard asmText "lw $t0,-32768($sp)\nlw $t0,32767($sp)\nldc1 $f2,-32768($sp)\n"
  = some [0x8fa88000#32, 0x8fa87fff#32, 0xd7a28000#32]
#guard asmFails "teqi $t0,40000\n"
#guard asmFails "tltiu $t0,-32769\n"
#guard asmText "teqi $t0,-5\n" = some [0x050cfffb#32]
#guard asmFails "li $a0,0x100000001\n"
#guard asmFails "li $a0,4294967296\n"
#guard asmFails "li $a0,-2147483649\n"
#guard asmText "li $a0,0xffffffff\nli $a0,-2147483648\n"
  = some [0x3c01ffff#32, 0x3424ffff#32, 0x3c018000#32, 0x34240000#32]
#guard asmFails ".byte 300\n"
#guard asmFails ".byte -129\n"
#guard asmFails ".half 65536\n"
#guard asmFails ".half -32769\n"
#guard asmFails ".word 0x100000000\n"
#guard asmFails ".word -2147483649\n"
#guard asmWords ".data\n.byte 255, -128\n.half 65535, -32768\n.word 0xffffffff, -2147483648\n" dataBase 4
  = some [0xff80ffff#32, 0x80000000#32, 0xffffffff#32, 0x80000000#32]
-- errors carry the line number of the offending statement
#guard asmErrLine "nop\nnop\naddiu $a0,$t0,70000\n" = some 3
#guard asmErrLine ".data\n.word 1\n.byte 300\n" = some 3

-- --------------------------------------------------------------------
-- B2: a label names the *aligned* address of the item that follows it
-- --------------------------------------------------------------------
def alignLabelSrc : String := srcLines
  [".data", "b: .byte 1", "w: .word 77", "h: .half 5", ".text", "la $t0, w", "lw $a0, 0($t0)", "la $t1, h"]
-- w = dataBase+4 (not +1): `la` loads 0x10010004, where the 77 is.
#guard asmText alignLabelSrc
  = some [0x3c011001#32, 0x34280004#32, 0x8d040000#32, 0x3c011001#32, 0x34290008#32]
#guard asmWords alignLabelSrc dataBase 3 = some [0x01000000#32, 77#32, 0x00050000#32]
-- label on its own line(s) before `.word` / `.half`; trailing label = end address
#guard asmWords (srcLines [".data", ".byte 1", "w:", "x: .word w, x, e", ".byte 2", "h:", "", ".half 5", "e:"])
    dataBase 4
  = some [0x01000000#32, 0x10010004#32, 0x10010004#32, 0x10010014#32]
#guard asmWords (srcLines [".data", ".byte 1", "w:", "x: .word w, x, e", ".byte 2", "h:", "", ".half 5", "e:"])
    (dataBase + 16#32) 1
  = some [0x02000005#32]    -- .byte 2, pad byte, .half 5 (h = +0x12, e = +0x14)
-- a label pending at a segment switch names the end of the segment being left
#guard asmWords (srcLines [".data", ".byte 1", "endd:", ".text", "nop", ".data", ".word endd"]) (dataBase + 4#32) 1
  = some [0x10010001#32]
-- instructions are word-aligned too, and their labels follow
#guard asmText (srcLines [".byte 1", "L: nop", "j L"]) = some [0x01000000#32, 0#32, 0x08100001#32]

-- --------------------------------------------------------------------
-- B3: branch / jump targets are validated
-- --------------------------------------------------------------------
#guard asmFails "beq $0,$0,40000\n"
#guard asmFails "beq $0,$0,-32769\n"
#guard asmText "beq $0,$0,-32768\nbeq $0,$0,32767\n" = some [0x10008000#32, 0x10007fff#32]
-- forward: +32767 words is the limit
#guard asmWords (srcLines ["beq $0,$0,L", ".space 131068", "L: nop"]) textBase 1 = some [0x10007fff#32]
#guard asmFails (srcLines ["beq $0,$0,L", ".space 131072", "L: nop"])
-- backward: -32768 words is the limit
#guard asmWords (srcLines ["L: nop", ".space 131064", "beq $0,$0,L"]) (textBase + 131068#32) 1 = some [0x10008000#32]
#guard asmFails (srcLines ["L: nop", ".space 131068", "beq $0,$0,L"])
#guard asmFails (srcLines ["L: nop", ".space 131068", "bc1t L"])
-- data label / unaligned target
#guard asmFails (srcLines [".data", "d: .word 1", ".text", "beq $0,$0,d"])
#guard asmFails (srcLines ["beq $0,$0,L", "nop", ".byte 1", "L: .byte 2"])
#guard asmFails (srcLines ["L: nop", "beq $0,$0,L+2"])
-- j/jal: 256MB region of the delay slot, word alignment
#guard asmFails "j 0x10000000\n"
#guard asmFails "j 0x00400002\n"
#guard asmFails "jal -4\n"
#guard asmFails (srcLines [".data", "d: .word 1", ".text", "j d"])
#guard asmText "j 0x0ffffffc\n" = some [0x0bffffff#32]
-- the region is that of pc+4: a `j` in the last word of a region targets the next one
#guard asmWords (srcLines [".text 0x0ffffffc", "j 0x10000000"]) 0x0ffffffc#32 1 = some [0x08000000#32]
#guard asmFails (srcLines [".text 0x0ffffffc", "j 0x00400000"])

-- --------------------------------------------------------------------
-- B4: label splitting respects quotes; label names are validated
-- --------------------------------------------------------------------
#guard asmText (r#".asciiz "a: b""# ++ "\n") = some [0x613a2062#32, 0#32]
#guard asmText (r#".asciiz "x#y:z"  # com: ment"# ++ "\n") = some [0x7823793a#32, 0x7a000000#32]
#guard asmFails "addi $a0,$a0,5 :\n"
#guard asmFails "1bad: nop\n"
#guard asmFails "a b: nop\n"
#guard asmFails ": nop\n"
#guard asmFails ":\n"
#guard asmText "a: b: .word 1\n.word a, b\n" = some [1#32, 0x00400000#32, 0x00400000#32]
#guard asmText "x:nop\n_y.z$: j x\nj _y.z$\n" = some [0#32, 0x08100000#32, 0x08100001#32]
#guard asmText "li $t0, ':'\nli $t0, '#'  # c\n" = some [0x3408003a#32, 0x34080023#32]

-- --------------------------------------------------------------------
-- B5: string lists, trailing junk, escapes
-- --------------------------------------------------------------------
#guard asmText (r#".asciiz "ab", "cd""# ++ "\n") = some [0x61620063#32, 0x64000000#32]
#guard asmFails (r#".asciiz "ab" junk"# ++ "\n")
#guard asmFails (r#".asciiz "ab" "cd""# ++ "\n")
#guard asmFails (r#".asciiz "abc"# ++ "\n")
#guard asmFails ".asciiz\n"
#guard asmFails ".asciiz 5\n"
-- a \r b \b \f \' \x41 \101 \0 \" \\ \n \t NUL
#guard asmText (r#".asciiz "a\rb\b\f\'\x41\101\0\"\\\n\t""# ++ "\n")
  = some [0x610d6208#32, 0x0c274141#32, 0x00225c0a#32, 0x09000000#32]
-- `\xHH` takes at most two hex digits; octal at most three
#guard asmText (r#".ascii "\x41b\1010""# ++ "\n") = some [0x41624130#32]
#guard asmFails (r#".asciiz "\q""# ++ "\n")
#guard asmFails (r#".asciiz "\a""# ++ "\n")
#guard asmFails (r#".asciiz "\x""# ++ "\n")
#guard asmFails (r#".asciiz "\400""# ++ "\n")
#guard asmFails (r#".asciiz "abc\"# ++ "\n")

-- --------------------------------------------------------------------
-- B6: numeric literals and register numbers
-- --------------------------------------------------------------------
-- leading 0 = octal (GNU as; MARS agrees: `li $t0, 010` loads 8)
#guard asmText "li $t0, 010\nli $t0, 0b101\nli $t0, +5\nli $t0, -0x10\nli $t0, 0\nli $t0, 00\nli $t0, 0X1f\n"
  = some [0x34080008#32, 0x34080005#32, 0x34080005#32, 0x2408fff0#32, 0x34080000#32, 0x34080000#32, 0x3408001f#32]
#guard asmFails "li $t0, 08\n"
#guard asmFails "li $t0, 1_000\n"
#guard asmFails "li $t0, 0x\n"
#guard asmFails "li $t0, 0b2\n"
#guard asmFails "li $t0, 12a\n"
#guard asmFails "add $1_0, $1, $1\n"
#guard asmFails "add $08, $1, $1\n"
#guard asmFails "add $32, $1, $1\n"
#guard asmFails "add $0x1, $1, $1\n"
#guard asmText "add $31, $1, $0\n" = some [0x0020f820#32]

-- --------------------------------------------------------------------
-- B7: segment address operands are honoured (and overlaps rejected)
-- --------------------------------------------------------------------
def segAddrSrc : String := srcLines
  [".data 0x10000000", "x: .word 5", ".text 0x00400100", "la $t0, x", ".data", "y: .word y"]
#guard asmWords segAddrSrc 0x10000000#32 2 = some [5#32, 0x10000004#32]
#guard asmWords segAddrSrc 0x00400100#32 2 = some [0x3c011000#32, 0x34280000#32]
#guard (match assemble segAddrSrc with | .ok p => p.size == 4 | .error _ => false)
#guard asmFails (srcLines [".text 0x00400000", "nop", ".text 0x00400000", "nop"])
#guard asmErrLine (srcLines [".data 0x00400000", ".word 1", ".text", "nop"]) = some 4
#guard asmFails ".text 0x100000000\n"
#guard asmFails ".data -4\n"
#guard asmFails ".data 1, 2\n"
#guard asmFails (srcLines [".text 0xfffffffc", "nop", "nop"])      -- runs past 2^32
#guard asmFails (srcLines [".text 0xfffffffc", "nop", "e:"])       -- label at 2^32
-- `la` is two words whatever the address (a low address must not shrink it)
#guard asmText (srcLines ["la $t0, x", ".text 0x100", "x: nop"]) = some [0x3c010000#32, 0x34280100#32]

-- --------------------------------------------------------------------
-- B8: data in `.text` is allowed and never misaligns code; no code in `.data`
-- --------------------------------------------------------------------
#guard asmText (srcLines ["nop", ".byte 1", "L: nop", "j L"]) = some [0#32, 0x01000000#32, 0#32, 0x08100002#32]
#guard asmFails ".data\nnop\n"
#guard asmFails ".kdata\nadd $1,$1,$1\n"
#guard asmFails ".data\nli $t0, 1\n"

-- --------------------------------------------------------------------
-- B9: empty operands
-- --------------------------------------------------------------------
#guard asmFails "add $t0,, $t1, $t2,\n"
#guard asmFails "add $t0, $t1, $t2,\n"
#guard asmFails "add ,$t0, $t1, $t2\n"
#guard asmFails ".word 1,,2\n"
#guard asmFails "nop ,\n"

-- --------------------------------------------------------------------
-- Syntax additions: registers, coprocessor register operands, codes
-- --------------------------------------------------------------------
#guard asmText "add $s8, $fp, $30\n" = some [0x03def020#32]
#guard asmText "mfc0 $t0, $12\nmfc0 $t0, 12\nmtc0 $t0, $14, 0\n"
  = some [encode (.mfc0 8#32 12#32 0#32), encode (.mfc0 8#32 12#32 0#32), encode (.mtc0 8#32 14#32 0#32)]
#guard asmText "mfc0 $t0, $15, 1\nmtc0 $t0, $15, 1\nmfc0 $t0, $16, 1\nmfc0 $t0, $15\nmfc0 $t0, $16\n"
  = some [encode (.mfc0 8#32 15#32 1#32), encode (.mtc0 8#32 15#32 1#32),
          encode (.mfc0 8#32 16#32 1#32), encode (.mfc0 8#32 15#32 0#32),
          encode (.mfc0 8#32 16#32 0#32)]
#guard asmFails "mfc0 $t0, $12, 8\n"
#guard asmFails "mfc0 $t0, $t4\n"
#guard asmFails "mfc0 $t0, $32\n"
#guard asmFails "mfc0 $t0, $012\n"
#guard asmText "cfc1 $t0, $31\nctc1 $t0, $31\ncfc1 $t0, $f31\n" = some [0x4448f800#32, 0x44c8f800#32, 0x4448f800#32]
#guard asmFails "mfc1 $t0, $31\n"        -- data FP registers stay `$fN` only
#guard asmText "break\nbreak 0\nsyscall 0\nsync 0\nteq $t0, $t1, 0\ntgeu $t0, $t1, 0\n"
  = some [0x0000000d#32, 0x0000000d#32, 0x0000000c#32, 0x0000000f#32, 0x01090034#32, 0x01090031#32]
-- nonzero codes are encoded (GNU as operand syntax); out-of-range ones are errors
#guard asmText "break 7\nbreak 7, 5\nsyscall 1\nsyscall 0xfffff\nsync 0x1f\nwait 3\n"
  = some [encode (.break (7#32 <<< 10)), encode (.break ((7#32 <<< 10) ||| 5#32)),
          encode (.syscall 1#32), encode (.syscall 0xfffff#32), encode (.sync 0x1f#32),
          encode (.wait 3#32)]
#guard asmText "break 7\n" = some [0x0007000d#32]
#guard asmText "teq $t0, $t1, 5\ntgeu $t0, $t1, 1023\n"
  = some [encode (.teq 8#32 9#32 5#32), encode (.tgeu 8#32 9#32 1023#32)]
#guard asmFails "break 1024\n"
#guard asmFails "break 1, 1024\n"
#guard asmFails "syscall 0x100000\n"
#guard asmFails "sync 32\n"
#guard asmFails "wait 0x80000\n"
#guard asmFails "tne $t0, $t1, 2000\n"
#guard asmText "sync 4\nbreak 0, 0\n" = some [encode (.sync 4#32), encode (.break 0#32)]
#guard asmFails "break 1, 2, 3\n"

-- --------------------------------------------------------------------
-- Syntax additions: directives
-- --------------------------------------------------------------------
#guard asmText ".globl main\n.global foo\n.extern bar 4\nmain: nop\n" = some [0#32]
#guard asmFails ".globl\n"
-- `.align n`; a label before `.align` moves with it
#guard asmWords (srcLines [".data", ".byte 1", ".align 2", "x: .word 5", ".byte 1", "y: .align 3", ".byte 9", ".word y, x"])
    dataBase 7
  = some [0x01000000#32, 5#32, 0x01000000#32, 0#32, 0x09000000#32, 0x10010010#32, 0x10010004#32]
-- `.align 0`: no automatic alignment until the next segment directive
#guard asmWords (srcLines [".data", ".byte 1", ".align 0", "x: .word 0x11223344", ".half 0x5566", "y: .byte 7",
    ".word y, x", ".data", ".byte 1", "z: .word z"]) dataBase 6
  = some [0x01112233#32, 0x44556607#32, 0x10010007#32, 0x10010001#32, 0x01000000#32, 0x10010014#32]
#guard asmFails ".data\n.align 17\n"
#guard asmFails ".data\n.align\n"
-- `.ascii` (no NUL), `.asciz`/`.string` aliases
#guard asmWords (srcLines [".data", r#"s: .ascii "ab""#, r#"t: .asciz "cd""#, r#".string "e""#, ".word s, t"]) dataBase 4
  = some [0x61626364#32, 0x00650000#32, 0x10010000#32, 0x10010002#32]
-- `.float`: exact, correctly rounded (ties-to-even), subnormals, overflow to inf
#guard asmWords (".data\n.float 1.0, -2.5, 0.1, 1e10, 3.4028235e38, 1e39, 1e-45, 7e-46, 0, -0.0, inf, " ++
    "-Infinity, NaN, 16777217, 16777219, .5, 5., 1E+2\n") dataBase 18
  = some [0x3f800000#32, 0xc0200000#32, 0x3dcccccd#32, 0x501502f9#32, 0x7f7fffff#32, 0x7f800000#32,
          0x00000001#32, 0x00000000#32, 0x00000000#32, 0x80000000#32, 0x7f800000#32, 0xff800000#32,
          0x7fc00000#32, 0x4b800000#32, 0x4b800002#32, 0x3f000000#32, 0x40a00000#32, 0x42c80000#32]
-- `.double`: most-significant word first, aligned to 8
#guard asmWords (".data\n.byte 1\nd: .double 1.0, 0.1, -2.5e-3, 1.7976931348623157e308, 1e309, 4.9e-324, " ++
    "2.4e-324, 9007199254740993, nan, -inf\n.word d\n") (dataBase + 8#32) 21
  = some [0x3ff00000#32, 0#32, 0x3fb99999#32, 0x9999999a#32, 0xbf647ae1#32, 0x47ae147b#32,
          0x7fefffff#32, 0xffffffff#32, 0x7ff00000#32, 0#32, 0#32, 1#32, 0#32, 0#32,
          0x43400000#32, 0#32, 0x7ff80000#32, 0#32, 0xfff00000#32, 0#32, 0x10010008#32]
#guard asmFails ".data\n.float abc\n"
#guard asmFails ".data\n.float 1e\n"
#guard asmFails ".data\n.float .\n"
#guard asmFails ".data\n.float 0x10\n"
#guard asmFails ".data\n.double 1.5x\n"
#guard asmFails ".data\n.float\n"
-- `.ktext` / `.kdata`: an exception handler assembled at the exception vector
def ktextSrc : String := srcLines
  [".ktext", "h: mfc0 $k0, $13", "eret", ".kdata", "kd: .word h, kd", ".text", "nop", ".ktext", "j h"]
#guard asmWords ktextSrc 0x80000180#32 3 = some [encode (.mfc0 26#32 13#32 0#32), 0x42000018#32, 0x08000060#32]
#guard asmWords ktextSrc 0x90000000#32 2 = some [0x80000180#32, 0x90000000#32]
#guard asmWords ktextSrc textBase 1 = some [0#32]
#guard asmWords ".ktext 0x80000200\nnop\n.kdata 0x90001000\n.word 1\n" 0x90001000#32 1 = some [1#32]
#guard ktextBase = 0x80000180#32 ∧ kdataBase = 0x90000000#32
#guard asmFails (srcLines [".ktext", "h: nop", ".text", "j h"])   -- kernel text is out of `j` range from .text

-- --------------------------------------------------------------------
-- Syntax additions: operands
-- --------------------------------------------------------------------
#guard asmText (r#"li $t0, 'a'"# ++ "\n" ++ r#"li $t0, '\n'"# ++ "\n" ++ r#"li $t0, '\''"# ++ "\n" ++
    r#"li $t0, '\x7f'"# ++ "\n" ++ "li $t0, 'a'+1\naddi $t0, $t0, 'A'\n.byte 'a', 'b', '\\0', ','\n")
  = some [0x34080061#32, 0x3408000a#32, 0x34080027#32, 0x3408007f#32, 0x34080062#32, 0x21080041#32, 0x6162002c#32]
#guard asmFails "li $t0, 'ab'\n"
#guard asmFails "li $t0, ''\n"
#guard asmFails "li $t0, 'a\n"
-- label±const in `.word`, `la`, branch and jump targets
#guard asmWords (srcLines [".data", "x: .word 1, 2, 3", ".word x+4, x-4, x + 8, 4+x"]) (dataBase + 12#32) 4
  = some [0x10010004#32, 0x1000fffc#32, 0x10010008#32, 0x10010004#32]
#guard asmText (srcLines [".data", "x: .word 1, 2, 3", ".text", "la $t0, x+8", "la $t1, x-4", "la $t2, 4+x"])
  = some [0x3c011001#32, 0x34280008#32, 0x3c011000#32, 0x3429fffc#32, 0x3c011001#32, 0x342a0004#32]
#guard asmText (srcLines ["L: nop", "nop", "beq $0,$0,L+4", "j L+4", "bne $0,$0,L-4"])
  = some [0#32, 0#32, 0x1000fffe#32, 0x08100001#32, 0x1400fffa#32]
#guard asmFails (srcLines ["la $t0, x-y", "x: nop", "y: nop"])
#guard asmFails (srcLines ["la $t0, x+y", "x: nop", "y: nop"])
#guard asmFails "la $t0, 5\n"
#guard asmFails (srcLines ["li $t0, x", "x: nop"])
#guard asmFails (srcLines [".half x", "x: nop"])
#guard asmFails (srcLines ["lw $t0, x($sp)", "x: nop"])
-- whitespace around the parts of a memory operand
#guard asmText "lw $t0, 4 ($sp)\nlw $t0, ( $sp )\nlw $t0, -4 ( $sp )\nlw $t0, 4+4($sp)\n"
  = some [0x8fa80004#32, 0x8fa80000#32, 0x8fa8fffc#32, 0x8fa80008#32]

-- --------------------------------------------------------------------
-- Syntax additions: idioms (GNU as expansions; no nops inserted)
-- --------------------------------------------------------------------
#guard asmText "L: b L\nbal L\nbeqz $t0, L\nbnez $t0, L\n"
  = some [encode (.beq 0#32 0#32 0xffff#32), encode (.bgezal 0#32 0xfffe#32),
          encode (.beq 8#32 0#32 0xfffd#32), encode (.bne 8#32 0#32 0xfffc#32)]
#guard asmText "neg $t0, $t1\nnegu $t0, $t1\nnot $t0, $t1\nneg $t0\n"
  = some [encode (.sub 0#32 9#32 8#32), encode (.subu 0#32 9#32 8#32), encode (.nor 9#32 0#32 8#32),
          encode (.sub 0#32 8#32 8#32)]
-- slt/sltu into $at, then bne/beq $at,$0 -- the branch sits one word later,
-- so its offset to `L` is -2
#guard asmText "L: blt $t0, $t1, L\n" = some [encode (.slt 8#32 9#32 1#32), encode (.bne 1#32 0#32 0xfffe#32)]
#guard asmText "L: bge $t0, $t1, L\n" = some [encode (.slt 8#32 9#32 1#32), encode (.beq 1#32 0#32 0xfffe#32)]
#guard asmText "L: bgt $t0, $t1, L\n" = some [encode (.slt 9#32 8#32 1#32), encode (.bne 1#32 0#32 0xfffe#32)]
#guard asmText "L: ble $t0, $t1, L\n" = some [encode (.slt 9#32 8#32 1#32), encode (.beq 1#32 0#32 0xfffe#32)]
#guard asmText "L: bltu $t0, $t1, L\n" = some [encode (.sltu 8#32 9#32 1#32), encode (.bne 1#32 0#32 0xfffe#32)]
#guard asmText "L: bgeu $t0, $t1, L\n" = some [encode (.sltu 8#32 9#32 1#32), encode (.beq 1#32 0#32 0xfffe#32)]
#guard asmText "L: bgtu $t0, $t1, L\n" = some [encode (.sltu 9#32 8#32 1#32), encode (.bne 1#32 0#32 0xfffe#32)]
#guard asmText "L: bleu $t0, $t1, L\n" = some [encode (.sltu 9#32 8#32 1#32), encode (.beq 1#32 0#32 0xfffe#32)]
-- forward target, and the label after a two-word idiom is laid out correctly
#guard asmText "blt $t0, $t1, F\nnop\nF: j F\n" = some [0x0109082a#32, 0x14200001#32, 0#32, 0x08100003#32]
#guard asmFails "blt $t0, 5, L\nL: nop\n"
#guard asmFails "blt $t0, $t1\n"
#guard asmFails "b\n"
#guard asmFails "neg\n"
#guard asmText "ssnop\nehb\n" = some [0x00000040#32, 0x000000c0#32]
-- `pause` = `sll $0,$0,5` (0x00000140), `nal` = `bltzal $0, 0` (0x04100000)
-- (MD00086 Vol II-A Rev 6.06, PAUSE p.317, NAL p.306)
#guard asmText "pause\n" = some [0x00000140#32]
#guard asmText "nal\n" = some [0x04100000#32]
#guard (asmText "pause $t0\n").isNone
#guard (asmText "nal L\nL: nop\n").isNone
#guard decode 0x00000140#32 = some (.sll 0#32 0#32 5#32)
#guard decode 0x04100000#32 = some (.bltzal 0#32 0#32)
#guard decode 0x00000040#32 = some (.sll 0#32 0#32 1#32) ∧ decode 0x000000c0#32 = some (.sll 0#32 0#32 3#32)
-- jr.hb / jalr.hb: hint bit 10 set; `decode` accepts these words as plain jr/jalr
#guard asmText "jr.hb $ra\njalr.hb $t9\njalr.hb $t0, $t9\n" = some [0x03e00408#32, 0x0320fc09#32, 0x03204409#32]
#guard decode 0x03e00408#32 = some (.jr 31#32)
#guard decode 0x0320fc09#32 = some (.jalr 25#32 31#32)
#guard decode 0x03204409#32 = some (.jalr 25#32 8#32)
-- abs: bgez rs, +2 ; move rd, rs (delay slot; nop if rd = rs) ; sub rd, $0, rs
#guard asmText "abs $t0, $t1\n"
  = some [encode (.bgez 9#32 2#32), encode (.addu 0#32 9#32 8#32), encode (.sub 0#32 9#32 8#32)]
#guard asmText "abs $t0, $8\n" = some [encode (.bgez 8#32 2#32), 0#32, encode (.sub 0#32 8#32 8#32)]
-- case-insensitive mnemonics and directives; registers stay case-sensitive
#guard asmText "ADD $t0, $t1, $t2\nAdd $t0, $t1, $t2\nLI $t0, 5\n.WORD 7\nSyscall\n"
  = some [0x012a4020#32, 0x012a4020#32, 0x34080005#32, 7#32, 0x0000000c#32]
#guard asmFails "ADD $T0, $t1, $t2\n"
-- misc: duplicate labels (also across a pending label), unknown directive, missing operands
#guard asmFails "x:\nx: nop\n"
#guard asmFails ".frob 1\n"
#guard asmFails ".word\n"
#guard asmFails ".data\n.space 4, 1\n"
#guard asmFails ".data\n.space -1\n"
-- `sb`
#guard asmText "sb $t0, 0($t1)\nsb $9, -1($8)\n"
  = some [encode (.sb 9#32 8#32 0#32), encode (.sb 8#32 9#32 0xffff#32)]
#guard asmText "sb $9, 1($8)\n" = some [0xa1090001#32]

-- ## FPU additions: condition codes, signaling compares, new mnemonics

-- all sixteen predicates, both formats, default cc = 0
#guard asmText (srcLines (fpCondNames.map fun c => s!"c.{c}.s $f5, $f6"))
  = some ((List.range 16).map fun c => encode (.cCondS (BitVec.ofNat 32 c) 0#32 5#32 6#32))
#guard asmText (srcLines (fpCondNames.map fun c => s!"c.{c}.d $f4, $f6"))
  = some ((List.range 16).map fun c => encode (.cCondD (BitVec.ofNat 32 c) 0#32 4#32 6#32))
-- explicit condition code: `$fccN` or a bare number
#guard asmText "c.seq.d $fcc7, $f4, $f6\nc.ngt.s 3, $f5, $f6\nc.eq.s $fcc0, $f5, $f6\n"
  = some [encode (.cCondD 10#32 7#32 4#32 6#32), encode (.cCondS 15#32 3#32 5#32 6#32),
          encode (.cCondS 2#32 0#32 5#32 6#32)]
#guard asmText "c.eq.s $f5, $f6\n" = some [0x46062832#32]
#guard asmFails "c.eq.s $fcc8, $f5, $f6\n"
#guard asmFails "c.eq.s $f5\n"
-- FP branches with and without cc, likely forms
#guard asmText (srcLines ["L: bc1f L", "bc1t L", "bc1fl L", "bc1tl L", "bc1t $fcc5, L",
    "bc1fl 7, L"])
  = some [encode (.bc1f 0#32 0xffff#32), encode (.bc1t 0#32 0xfffe#32),
          encode (.bc1fl 0#32 0xfffd#32), encode (.bc1tl 0#32 0xfffc#32),
          encode (.bc1t 5#32 0xfffb#32), encode (.bc1fl 7#32 0xfffa#32)]
-- conditional moves
#guard asmText (srcLines ["movf $2, $4", "movt $2, $4, $fcc7", "movf.s $f2, $f4",
    "movt.d $f2, $f4, $fcc7", "movn.s $f2, $f4, $5", "movz.d $f2, $f4, $5",
    "movt.s $f2, $f4, 1", "movf.d $f2, $f4", "movn.d $f2, $f4, $5", "movz.s $f2, $f4, $5"])
  = some [encode (.movf 4#32 0#32 2#32), encode (.movt 4#32 7#32 2#32),
          encode (.movfS 2#32 4#32 0#32), encode (.movtD 2#32 4#32 7#32),
          encode (.movnS 2#32 4#32 5#32), encode (.movzD 2#32 4#32 5#32),
          encode (.movtS 2#32 4#32 1#32), encode (.movfD 2#32 4#32 0#32),
          encode (.movnD 2#32 4#32 5#32), encode (.movzS 2#32 4#32 5#32)]
#guard asmText "movf $2, $4\nmovt.d $f2, $f4, $fcc7\n" = some [0x00801001#32, 0x463d2091#32]
-- high-half moves, indexed loads/stores, prefetches
#guard asmText (srcLines ["mfhc1 $8, $f4", "mthc1 $8, $f4", "lwxc1 $f2, $5($4)",
    "ldxc1 $f2, $5($4)", "swxc1 $f2, $5($4)", "sdxc1 $f2, $5($4)", "prefx 1, $5($4)",
    "pref 1, 16($4)", "pref 0, -4($sp)"])
  = some [encode (.mfhc1 8#32 4#32), encode (.mthc1 8#32 4#32), encode (.lwxc1 2#32 5#32 4#32),
          encode (.ldxc1 2#32 5#32 4#32), encode (.swxc1 2#32 5#32 4#32),
          encode (.sdxc1 2#32 5#32 4#32), encode (.prefx 1#32 5#32 4#32),
          encode (.pref 4#32 1#32 16#32), encode (.pref 29#32 0#32 0xfffc#32)]
#guard asmText "lwxc1 $f2, $5($4)\npref 1, 16($4)\n" = some [0x4c850080#32, 0xcc810010#32]
#guard asmFails "lwxc1 $f2, 4($4)\n"
#guard asmFails "pref 32, 0($4)\n"
-- multiply-add family, recip / rsqrt, double → word
#guard asmText (srcLines ["madd.s $f2, $f4, $f5, $f6", "madd.d $f2, $f4, $f6, $f8",
    "msub.s $f2, $f4, $f5, $f6", "msub.d $f2, $f4, $f6, $f8", "nmadd.s $f2, $f4, $f5, $f6",
    "nmadd.d $f2, $f4, $f6, $f8", "nmsub.s $f2, $f4, $f5, $f6", "nmsub.d $f2, $f4, $f6, $f8",
    "recip.s $f2, $f4", "recip.d $f2, $f4", "rsqrt.s $f2, $f4", "rsqrt.d $f2, $f4",
    "round.w.d $f2, $f4", "trunc.w.d $f2, $f4", "ceil.w.d $f2, $f4", "floor.w.d $f2, $f4"])
  = some [encode (.maddS 2#32 4#32 5#32 6#32), encode (.maddD 2#32 4#32 6#32 8#32),
          encode (.msubS 2#32 4#32 5#32 6#32), encode (.msubD 2#32 4#32 6#32 8#32),
          encode (.nmaddS 2#32 4#32 5#32 6#32), encode (.nmaddD 2#32 4#32 6#32 8#32),
          encode (.nmsubS 2#32 4#32 5#32 6#32), encode (.nmsubD 2#32 4#32 6#32 8#32),
          encode (.recipS 2#32 4#32), encode (.recipD 2#32 4#32), encode (.rsqrtS 2#32 4#32),
          encode (.rsqrtD 2#32 4#32), encode (.roundWD 2#32 4#32), encode (.truncWD 2#32 4#32),
          encode (.ceilWD 2#32 4#32), encode (.floorWD 2#32 4#32)]
#guard asmText "madd.s $f2, $f4, $f5, $f6\n" = some [0x4c8628a0#32]
-- di / ei
#guard asmText "di\ndi $t1\nei\nei $t0\n"
  = some [encode (.di 0#32), encode (.di 9#32), encode (.ei 0#32), encode (.ei 8#32)]
#guard asmText "di\nei $t0\n" = some [0x41606000#32, 0x41686020#32]
-- the FPU mnemonic table has no duplicate names
#guard cop1Mnemonics.eraseDups.length = cop1Mnemonics.length
-- `.set`: noreorder / noat / at accepted, reorder and anything else rejected
#guard asmText ".set noreorder\n.set noat\nnop\n.set at\nnop\n" = some [0#32, 0#32]
#guard asmFails ".set reorder\nnop\n"
#guard asmFails ".set mips32r2\nnop\n"
#guard asmFails ".set\n"
-- under `.set noat` the `$at` idioms are rejected; `.set at` re-enables them
#guard asmFails (srcLines [".set noat", "L: blt $t0, $t1, L"])
#guard (assemble (srcLines [".set noat", ".set at", "L: blt $t0, $t1, L"])).isOk
#guard (assemble (srcLines [".set noat", "L: beq $t0, $t1, L", "li $t0, 0x12345678"])).isOk
