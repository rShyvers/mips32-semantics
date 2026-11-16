import Semantics.Asm

/-!
# Tests for `Semantics/Asm.lean` (the assembler, Release 6, little-endian)

`#guard` only: `Std.HashMap`'s `getD`/`contains` do not kernel-reduce, so `by decide`/`by rfl` are
not usable for `Program`-valued assertions (docs/DESIGN.md §5 sanctions `#guard`).

**Golden words.** The words of `r6Words` are LLVM's: the lines of `r6Lines` assembled with
`llvm-mc-21 -triple=mipsel -mcpu=mips32r6 -filetype=obj` (after `.set noreorder`), linked with
`ld.lld-21 -m elf32ltsmip -Ttext=0x400000` and dumped with `llvm-objcopy-21 -O binary`, read as
little-endian words. `rdpgpr`/`wrpgpr` are not assembled by llvm-mc for `mips32r6` ("instruction
requires a CPU feature not currently enabled"); their words are checked against the manual's field
layout below. Every other data-layout word below is little-endian (`profile.bigEndianMem = false`):
the word value `readMemWord` reads at that address.
-/

open Asm

/-- Source text from lines. -/
private def srcLines (ls : List String) : String := String.intercalate "\n" ls ++ "\n"

/-- The `n` consecutive words at `addr` (absent words read as 0); `none` if assembly fails. -/
private def asmWords (src : String) (addr : W32) (n : Nat) : Option (List W32) :=
  match assemble src with
  | .ok p => some ((List.range n).map (fun i => p.getD (addr + natToW32 (4 * i)) 0))
  | .error _ => none

/-- The contiguous run of words starting at `textBase`; `none` if assembly fails. -/
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

/-- The error is `unknownMnemonic`. -/
private def asmUnknown (src : String) : Bool :=
  match assemble src with
  | .error (.unknownMnemonic _ _) => true
  | _ => false

-- ====================================================================
-- Release 6 encodings: every machine mnemonic against llvm-mc
-- ====================================================================

/-- One line per machine mnemonic and form (`L` is the first line, `textBase`). -/
def r6Lines : List String :=
  ["L: add $t0, $t1, $t2",
   "addu $t0, $t1, $t2",
   "sub $t0, $t1, $t2",
   "subu $t0, $t1, $t2",
   "and $t0, $t1, $t2",
   "or $t0, $t1, $t2",
   "xor $t0, $t1, $t2",
   "nor $t0, $t1, $t2",
   "slt $t0, $t1, $t2",
   "sltu $t0, $t1, $t2",
   "sll $t0, $t1, 7",
   "srl $t0, $t1, 31",
   "sra $t0, $t1, 1",
   "rotr $t0, $t1, 5",
   "sllv $t0, $t1, $t2",
   "srlv $t0, $t1, $t2",
   "srav $t0, $t1, $t2",
   "rotrv $t0, $t1, $t2",
   "pause",
   "jalr $t0, $t1",
   "jalr $t9",
   "jalr.hb $t0, $t1",
   "jalr.hb $t9",
   "clo $t0, $t1",
   "clz $t0, $t1",
   "seb $t0, $t1",
   "seh $t0, $t1",
   "wsbh $t0, $t1",
   "ext $t0, $t1, 6, 10",
   "ins $t0, $t1, 6, 10",
   "rdhwr $t0, $29",
   "rdhwr $t0, $2, 3",
   "addiu $t0, $t1, -5",
   "slti $t0, $t1, 32767",
   "sltiu $t0, $t1, -1",
   "andi $t0, $t1, 0xffff",
   "ori $t0, $t1, 0x1234",
   "xori $t0, $t1, 1",
   "aui $t0, $t1, 0x8001",
   "lui $t0, 0xffff",
   "lw $t0, -4($sp)",
   "sw $t0, 32767($sp)",
   "lb $t0, -32768($t1)",
   "lbu $t0, 1($t1)",
   "lh $t0, 2($t1)",
   "lhu $t0, 2($t1)",
   "sh $t0, -2($t1)",
   "sb $t0, 0($t1)",
   "ll $t0, -256($t1)",
   "sc $t0, 255($t1)",
   "beq $t0, $t1, L",
   "bne $t0, $t1, L",
   "blez $t0, L",
   "bgtz $t0, L",
   "bltz $t0, L",
   "bgez $t0, L",
   "nal",
   "bal L",
   "synci -8($t1)",
   "j L",
   "jal L",
   "syscall",
   "syscall 0x12345",
   "teq $t0, $t1",
   "tne $t0, $t1, 5",
   "tlt $t0, $t1",
   "tge $t0, $t1",
   "tltu $t0, $t1",
   "tgeu $t0, $t1, 1023",
   "break",
   "sync",
   "sync 4",
   "pref 1, -4($sp)",
   "mfc0 $t0, $12",
   "mtc0 $t0, $14",
   "mfc0 $t0, $15, 1",
   "di",
   "ei $t0",
   "eret",
   "wait",
   "mfc1 $t0, $f2",
   "mtc1 $t0, $f2",
   "mfhc1 $t0, $f2",
   "mthc1 $t0, $f2",
   "cfc1 $t0, $31",
   "ctc1 $t0, $31",
   "lwc1 $f2, 4($sp)",
   "swc1 $f2, -4($sp)",
   "ldc1 $f2, 8($sp)",
   "sdc1 $f2, -8($sp)",
   "add.s $f0, $f2, $f4",
   "sub.s $f0, $f2, $f4",
   "mul.s $f0, $f2, $f4",
   "div.s $f0, $f2, $f4",
   "sqrt.s $f0, $f2",
   "abs.s $f0, $f2",
   "mov.s $f0, $f2",
   "neg.s $f0, $f2",
   "recip.s $f0, $f2",
   "rsqrt.s $f0, $f2",
   "round.w.s $f0, $f2",
   "trunc.w.s $f0, $f2",
   "ceil.w.s $f0, $f2",
   "floor.w.s $f0, $f2",
   "cvt.w.s $f0, $f2",
   "cvt.d.s $f0, $f2",
   "cvt.s.w $f0, $f2",
   "cvt.d.w $f0, $f2",
   "add.d $f0, $f2, $f4",
   "sub.d $f0, $f2, $f4",
   "mul.d $f0, $f2, $f4",
   "div.d $f0, $f2, $f4",
   "sqrt.d $f0, $f2",
   "abs.d $f0, $f2",
   "mov.d $f0, $f2",
   "neg.d $f0, $f2",
   "recip.d $f0, $f2",
   "rsqrt.d $f0, $f2",
   "round.w.d $f0, $f2",
   "trunc.w.d $f0, $f2",
   "ceil.w.d $f0, $f2",
   "floor.w.d $f0, $f2",
   "cvt.w.d $f0, $f2",
   "cvt.s.d $f0, $f2",
   "jr $t1",
   "jr.hb $t1",
   "nop",
   "ssnop",
   "ehb"]

/-- LLVM's words for `r6Lines` (see the module docstring). -/
def r6Words : List W32 :=
  [0x012a4020#32, 0x012a4021#32, 0x012a4022#32, 0x012a4023#32, 0x012a4024#32, 0x012a4025#32,
   0x012a4026#32, 0x012a4027#32, 0x012a402a#32, 0x012a402b#32, 0x000941c0#32, 0x000947c2#32,
   0x00094043#32, 0x00294142#32, 0x01494004#32, 0x01494006#32, 0x01494007#32, 0x01494046#32,
   0x00000140#32, 0x01204009#32, 0x0320f809#32, 0x01204409#32, 0x0320fc09#32, 0x01204051#32,
   0x01204050#32, 0x7c094420#32, 0x7c094620#32, 0x7c0940a0#32, 0x7d284980#32, 0x7d287984#32,
   0x7c08e83b#32, 0x7c0810fb#32, 0x2528fffb#32, 0x29287fff#32, 0x2d28ffff#32, 0x3128ffff#32,
   0x35281234#32, 0x39280001#32, 0x3d288001#32, 0x3c08ffff#32, 0x8fa8fffc#32, 0xafa87fff#32,
   0x81288000#32, 0x91280001#32, 0x85280002#32, 0x95280002#32, 0xa528fffe#32, 0xa1280000#32,
   0x7d288036#32, 0x7d287fa6#32, 0x1109ffcd#32, 0x1509ffcc#32, 0x1900ffcb#32, 0x1d00ffca#32,
   0x0500ffc9#32, 0x0501ffc8#32, 0x04100000#32, 0x0411ffc6#32, 0x053ffff8#32, 0x08100000#32,
   0x0c100000#32, 0x0000000c#32, 0x0048d14c#32, 0x01090034#32, 0x01090176#32, 0x01090032#32,
   0x01090030#32, 0x01090033#32, 0x0109fff1#32, 0x0000000d#32, 0x0000000f#32, 0x0000010f#32,
   0x7fa1fe35#32, 0x40086000#32, 0x40887000#32, 0x40087801#32, 0x41606000#32, 0x41686020#32,
   0x42000018#32, 0x42000020#32, 0x44081000#32, 0x44881000#32, 0x44681000#32, 0x44e81000#32,
   0x4448f800#32, 0x44c8f800#32, 0xc7a20004#32, 0xe7a2fffc#32, 0xd7a20008#32, 0xf7a2fff8#32,
   0x46041000#32, 0x46041001#32, 0x46041002#32, 0x46041003#32, 0x46001004#32, 0x46001005#32,
   0x46001006#32, 0x46001007#32, 0x46001015#32, 0x46001016#32, 0x4600100c#32, 0x4600100d#32,
   0x4600100e#32, 0x4600100f#32, 0x46001024#32, 0x46001021#32, 0x46801020#32, 0x46801021#32,
   0x46241000#32, 0x46241001#32, 0x46241002#32, 0x46241003#32, 0x46201004#32, 0x46201005#32,
   0x46201006#32, 0x46201007#32, 0x46201015#32, 0x46201016#32, 0x4620100c#32, 0x4620100d#32,
   0x4620100e#32, 0x4620100f#32, 0x46201024#32, 0x46201020#32, 0x01200009#32, 0x01200409#32,
   0x00000000#32, 0x00000040#32, 0x000000c0#32]

#guard r6Lines.length = r6Words.length
#guard asmText (srcLines r6Lines) = some r6Words
-- every golden word decodes, and re-encodes to itself (the model's decoder accepts exactly these)
#guard r6Words.all fun w => (decode w).map encode == some w

-- BEGIN R6-2
/-- Wave R6-2 mnemonics (ERETNC, SIGRIE, CACHE), with the words of
`llvm-mc -triple=mipsel -mcpu=mips32r6 -show-encoding` (llvm-mc 21). -/
def r62Lines : List String :=
  ["eretnc", "sigrie 5", "sigrie 0", "sigrie 65535", "cache 20, -8($9)", "cache 1, 255($4)",
   "cache 0, 0($0)"]

/-- LLVM's words for `r62Lines`. -/
def r62Words : List W32 :=
  [0x42000058#32, 0x04170005#32, 0x04170000#32, 0x0417ffff#32, 0x7d34fc25#32, 0x7c817fa5#32,
   0x7c000025#32]

#guard r62Lines.length = r62Words.length
#guard asmText (srcLines r62Lines) = some r62Words
#guard r62Words.all fun w => (decode w).map encode == some w
-- `sigrie` without an operand is `sigrie 0`
#guard asmText "sigrie\n" = some [0x04170000#32]
-- out-of-range operands are rejected: a code above 0xFFFF, a cache op above 31, an offset outside
-- the signed 9-bit range
#guard asmText "sigrie 65536\n" = none
#guard asmText "cache 32, 0($4)\n" = none
#guard asmText "cache 1, 256($4)\n" = none
#guard asmText "cache 1, -257($4)\n" = none
-- END R6-2

-- every machine mnemonic of the tables is exercised (`rdpgpr`/`wrpgpr` below), and none is listed twice
#guard instrMnemonics.all fun m =>
  m == "rdpgpr" || m == "wrpgpr" ||
    (r6Lines ++ r62Lines).any fun l => ((l.splitOn " ").filter (· != "L:")).head? == some m
#guard instrMnemonics.eraseDups.length = instrMnemonics.length
-- RDPGPR/WRPGPR: COP0 010000 | 01010 / 01110 | rt | rd | 0 (MD00086 Vol II-A Rev 6.06, RDPGPR p.335,
-- WRPGPR p.444)
#guard asmText "rdpgpr $t0, $t1\nwrpgpr $t0, $t1\nrdpgpr $zero, $ra\n"
  = some [0x41494000#32, 0x41c94000#32, 0x415f0000#32]
#guard asmText "rdpgpr $t0, $t1\nwrpgpr $t0, $t1\n" = some [encode (.rdpgpr 8#32 9#32), encode (.wrpgpr 8#32 9#32)]

-- The Release 6 re-encodings decode to the Release 6 constructors.
#guard asmText "lui $t0, 0x1234\naui $t1, $t2, -1\naui $t1, $t2, 0xffff\n"
  = some [encode (.aui 0#32 8#32 0x1234#32), encode (.aui 10#32 9#32 0xffff#32),
          encode (.aui 10#32 9#32 0xffff#32)]
#guard decode 0x3c081234#32 = some (.aui 0#32 8#32 0x1234#32)
#guard asmText "ll $t0, -4($sp)\nsc $t0, 255($a0)\npref 3, -256($t1)\n"
  = some [encode (.ll 29#32 8#32 0x1fc#32), encode (.sc 4#32 8#32 0xff#32), encode (.pref 9#32 3#32 0x100#32)]
#guard asmText "clo $t0, $t1\nclz $t0, $t1\n" = some [encode (.clo 9#32 8#32), encode (.clz 9#32 8#32)]
#guard asmText "rdhwr $t0, $29\nrdhwr $t0, $29, 7\nrdhwr $t0, 2, 0\n"
  = some [encode (.rdhwr 8#32 29#32 0#32), encode (.rdhwr 8#32 29#32 7#32), encode (.rdhwr 8#32 2#32 0#32)]
#guard asmText "pause\nnal\nL: bal L\n" = some [0x00000140#32, 0x04100000#32, 0x0411ffff#32]
#guard decode 0x00000140#32 = some .pause
#guard decode 0x04100000#32 = some (.nal 0#32)
#guard decode 0x0411ffff#32 = some (.bal 0xffff#32)
-- `sll $0, $0, 5` is the PAUSE word
#guard asmText "sll $0, $0, 5\n" = some [encode .pause]
-- 9-bit offsets: -256..255; 16-bit for the classic loads/stores and SYNCI
#guard asmFails "ll $t0, 256($t1)\n"
#guard asmFails "sc $t0, -257($t1)\n"
#guard asmFails "pref 0, 256($t1)\n"
#guard asmFails "pref 32, 0($4)\n"
#guard asmFails "rdhwr $t0, $29, 8\n"
#guard asmFails "aui $t0, $t1, 65536\n"
#guard asmFails "aui $t0, $t1, -32769\n"
#guard asmFails "nal L\nL: nop\n"
#guard asmFails "pause $t0\n"
#guard asmFails "bal\n"

-- ====================================================================
-- Basic programs
-- ====================================================================

-- A `.text` program mixing `addiu`/`add`/`beq`/`jal` with labels.
def prog1Src : String :=
"loop: addiu $t0, $zero, 1\n" ++
"      add $t1, $t0, $t0\n" ++
"      beq $t1, $zero, loop\n" ++
"      jal loop\n"

def prog1 : Program :=
  match assemble prog1Src with
  | .ok p => p
  | .error _ => ∅

#guard prog1.getD textBase 0 = mkIT (9#32) (0#32) (8#32) (1#32)
#guard prog1.getD (textBase + 4#32) 0 = mkRT (8#32) (8#32) (9#32) (0#32) (0x20#32)
-- beq $t1,$zero,loop: offset = (textBase - (textBase+12))/4 = -3
#guard prog1.getD (textBase + 8#32) 0 = mkIT (4#32) (9#32) (0#32) (ofInt32 (-3) &&& 0xffff#32)
-- jal loop: target = textBase, targetWordAddr = textBase/4
#guard prog1.getD (textBase + 12#32) 0 = (natToW32 0x03 <<< 26) ||| mkJT (textBase >>> 2)

-- `li` needing the two-word split: 0x12345 → `aui $at, $0, 1 ; ori $t0, $at, 0x2345`.
#guard asmText "li $t0, 0x12345\n" = some [encode (.aui 0#32 1#32 1#32), encode (.ori 1#32 8#32 0x2345#32)]
#guard asmText "li $t0, 0x12345\n" = some [0x3c010001#32, 0x34282345#32]
-- a negative `li` in -32768..-1 is one `addiu`
#guard asmText "li $t0, -1\n" = some [0x2408ffff#32]

-- `.data` with `.word`/`.asciiz`/`.space`: little-endian bytes at dataBase.
def dataProg : Program :=
  match assemble (".data\n" ++ "x: .word 0x01020304\n" ++ "y: .asciiz \"Hi\"\n" ++ "z: .space 4\n" ++
      "w: .word 7\n") with
  | .ok p => p
  | .error _ => ∅

-- x at dataBase: the word value is the datum (byte 0x04 at the lowest address)
#guard dataProg.getD dataBase 0 = 0x01020304#32
-- y at dataBase+4: bytes 'H'(0x48) 'i'(0x69) 0x00 at +4,+5,+6 -> word 0x00006948
#guard dataProg.getD (dataBase + 4#32) 0 = 0x00006948#32
-- z: .space 4 reserves +7..+10 (nothing written); w: .word 7 at +12
#guard dataProg.getD (dataBase + 12#32) 0 = 7#32
#guard dataProg.contains (dataBase + 8#32) = false
-- the byte order is the profile's: byte k of a word datum is at bits 8k+7..8k
#guard (assemble ".data\n.byte 1, 2, 3, 4\n.half 0x0506, 0x0708\n").toOption.map (·.getD dataBase 0)
  = some 0x04030201#32
#guard asmWords ".data\n.byte 1, 2, 3, 4\n.half 0x0506, 0x0708\n" dataBase 2 = some [0x04030201#32, 0x07080506#32]

-- `move`/`nop`, `syscall`
#guard asmText "move $t0, $t1\nnop\nsyscall\n" = some [encode (.addu 0#32 9#32 8#32), 0#32, 0x0000000c#32]
#guard decode 0x0000000c#32 = some (.syscall 0#32)

-- ====================================================================
-- Removed pre-Release 6 instructions are errors
-- ====================================================================
#guard removedMnemonics.all fun m => asmUnknown (m ++ " $t0, $t1, $t2\n")
#guard removedMnemonics.all fun m => !isKnownMnemonic m
#guard asmUnknown "mult $t0, $t1\n" ∧ asmUnknown "mfhi $t0\n" ∧ asmUnknown "addi $t0, $t0, 1\n" ∧
  asmUnknown "beql $t0, $t1, 0\n" ∧ asmUnknown "bltzal $t0, 0\n" ∧ asmUnknown "bgezal $0, 0\n" ∧
  asmUnknown "teqi $t0, 1\n" ∧ asmUnknown "lwl $t0, 0($t1)\n" ∧ asmUnknown "c.eq.s $f0, $f2\n" ∧
  asmUnknown "bc1t 0\n" ∧ asmUnknown "madd.s $f0, $f2, $f4, $f6\n" ∧ asmUnknown "lwxc1 $f0, $t0($t1)\n" ∧
  asmUnknown "movn $t0, $t1, $t2\n" ∧ asmUnknown "mul $t0, $t1, $t2\n"

-- One error case per major `AsmError` kind.
#guard asmFails "frobnicate $t0, $t1\n"
#guard asmFails "add $t0, $bogus, $t1\n"
#guard asmFails "j nosuchlabel\n"
#guard asmFails "li $t0, notanumber\n"
#guard asmFails ".bogus 1,2,3\n"
#guard asmFails "add $t0, $t1\n"
#guard asmFails "foo: add $t0,$zero,$zero\nfoo: add $t1,$zero,$zero\n"
#guard asmFails "sync $t0\n"
#guard asmFails "synci $t0\n"
#guard asmFails "synci $t0, 4($sp)\n"
#guard asmFails "rotr $t0, $t1, 32\n"
#guard asmFails "ext $t0, $t1, 30, 3\n"
#guard asmFails "ins $t0, $t1, 0, 33\n"
#guard asmFails "jalr\n"
#guard asmFails "jalr $t0, $t1, $t2\n"
#guard asmFails "jr $t0, $t1\n"
#guard asmFails "mfc1 $t0, $f32\n"

-- ====================================================================
-- ## Audit-fix tests (B1-B9) and syntax additions
-- ====================================================================
-- Every expected word below was produced by this assembler and, wherever
-- MARS 4.5 accepts the same source, cross-checked against
-- `java -jar vendor/mars/Mars4_5.jar a dump .text HexText` (differences are
-- noted inline).

-- --------------------------------------------------------------------
-- B1: immediates are range-checked, never truncated
-- --------------------------------------------------------------------
#guard asmFails "addiu $a0,$t0,70000\n"
#guard asmFails "addiu $a0,$t0,-32769\n"
#guard asmFails "addiu $a0,$t0,32768\n"
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
  = some [0xffff80ff#32, 0x00008000#32, 0xffffffff#32, 0x80000000#32]
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
#guard asmWords alignLabelSrc dataBase 3 = some [0x00000001#32, 77#32, 0x00000005#32]
-- label on its own line(s) before `.word` / `.half`; trailing label = end address
#guard asmWords (srcLines [".data", ".byte 1", "w:", "x: .word w, x, e", ".byte 2", "h:", "", ".half 5", "e:"])
    dataBase 4
  = some [0x00000001#32, 0x10010004#32, 0x10010004#32, 0x10010014#32]
#guard asmWords (srcLines [".data", ".byte 1", "w:", "x: .word w, x, e", ".byte 2", "h:", "", ".half 5", "e:"])
    (dataBase + 16#32) 1
  = some [0x00050002#32]    -- .byte 2, pad byte, .half 5 (h = +0x12, e = +0x14)
-- a label pending at a segment switch names the end of the segment being left
#guard asmWords (srcLines [".data", ".byte 1", "endd:", ".text", "nop", ".data", ".word endd"]) (dataBase + 4#32) 1
  = some [0x10010001#32]
-- instructions are word-aligned too, and their labels follow
#guard asmText (srcLines [".byte 1", "L: nop", "j L"]) = some [0x00000001#32, 0#32, 0x08100001#32]

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
#guard asmFails (srcLines ["L: nop", ".space 131068", "bgez $0, L"])
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
#guard asmText (r#".asciiz "a: b""# ++ "\n") = some [0x62203a61#32, 0#32]
#guard asmText (r#".asciiz "x#y:z"  # com: ment"# ++ "\n") = some [0x3a792378#32, 0x0000007a#32]
#guard asmFails "addiu $a0,$a0,5 :\n"
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
#guard asmText (r#".asciiz "ab", "cd""# ++ "\n") = some [0x63006261#32, 0x00000064#32]
#guard asmFails (r#".asciiz "ab" junk"# ++ "\n")
#guard asmFails (r#".asciiz "ab" "cd""# ++ "\n")
#guard asmFails (r#".asciiz "abc"# ++ "\n")
#guard asmFails ".asciiz\n"
#guard asmFails ".asciiz 5\n"
-- a \r b \b \f \' \x41 \101 \0 \" \\ \n \t NUL
#guard asmText (r#".asciiz "a\rb\b\f\'\x41\101\0\"\\\n\t""# ++ "\n")
  = some [0x08620d61#32, 0x4141270c#32, 0x0a5c2200#32, 0x00000009#32]
-- `\xHH` takes at most two hex digits; octal at most three
#guard asmText (r#".ascii "\x41b\1010""# ++ "\n") = some [0x30416241#32]
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
#guard asmText (srcLines ["nop", ".byte 1", "L: nop", "j L"]) = some [0#32, 0x00000001#32, 0#32, 0x08100002#32]
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
  = some [0x00000001#32, 5#32, 0x00000001#32, 0#32, 0x00000009#32, 0x10010010#32, 0x10010004#32]
-- `.align 0`: no automatic alignment until the next segment directive
#guard asmWords (srcLines [".data", ".byte 1", ".align 0", "x: .word 0x11223344", ".half 0x5566", "y: .byte 7",
    ".word y, x", ".data", ".byte 1", "z: .word z"]) dataBase 6
  = some [0x22334401#32, 0x07556611#32, 0x10010007#32, 0x10010001#32, 0x00000001#32, 0x10010014#32]
#guard asmFails ".data\n.align 17\n"
#guard asmFails ".data\n.align\n"
-- `.ascii` (no NUL), `.asciz`/`.string` aliases
#guard asmWords (srcLines [".data", r#"s: .ascii "ab""#, r#"t: .asciz "cd""#, r#".string "e""#, ".word s, t"]) dataBase 4
  = some [0x64636261#32, 0x00006500#32, 0x10010000#32, 0x10010002#32]
-- `.float`: exact, correctly rounded (ties-to-even), subnormals, overflow to inf
#guard asmWords (".data\n.float 1.0, -2.5, 0.1, 1e10, 3.4028235e38, 1e39, 1e-45, 7e-46, 0, -0.0, inf, " ++
    "-Infinity, NaN, 16777217, 16777219, .5, 5., 1E+2\n") dataBase 18
  = some [0x3f800000#32, 0xc0200000#32, 0x3dcccccd#32, 0x501502f9#32, 0x7f7fffff#32, 0x7f800000#32,
          0x00000001#32, 0x00000000#32, 0x00000000#32, 0x80000000#32, 0x7f800000#32, 0xff800000#32,
          0x7fc00000#32, 0x4b800000#32, 0x4b800002#32, 0x3f000000#32, 0x40a00000#32, 0x42c80000#32]
-- `.double`: little-endian (least-significant byte first, so the low word first), aligned to 8
#guard asmWords (".data\n.byte 1\nd: .double 1.0, 0.1, -2.5e-3, 1.7976931348623157e308, 1e309, 4.9e-324, " ++
    "2.4e-324, 9007199254740993, nan, -inf\n.word d\n") (dataBase + 8#32) 21
  = some [0#32, 0x3ff00000#32, 0x9999999a#32, 0x3fb99999#32, 0x47ae147b#32, 0xbf647ae1#32,
          0xffffffff#32, 0x7fefffff#32, 0#32, 0x7ff00000#32, 1#32, 0#32, 0#32, 0#32,
          0#32, 0x43400000#32, 0#32, 0x7ff80000#32, 0#32, 0xfff00000#32, 0x10010008#32]
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
    r#"li $t0, '\x7f'"# ++ "\n" ++ "li $t0, 'a'+1\naddiu $t0, $t0, 'A'\n.byte 'a', 'b', '\\0', ','\n")
  = some [0x34080061#32, 0x3408000a#32, 0x34080027#32, 0x3408007f#32, 0x34080062#32, 0x25080041#32, 0x2c006261#32]
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
  = some [encode (.beq 0#32 0#32 0xffff#32), encode (.bal 0xfffe#32),
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
#guard decode 0x00000040#32 = some (.sll 0#32 0#32 1#32) ∧ decode 0x000000c0#32 = some (.sll 0#32 0#32 3#32)
-- jr.hb rs = jalr.hb $0, rs (JR.HB p.208); jalr.hb: hint bit 10 set (JALR.HB p.198)
#guard asmText "jr.hb $ra\njalr.hb $t9\njalr.hb $t0, $t9\njr $ra\n"
  = some [0x03e00409#32, 0x0320fc09#32, 0x03204409#32, 0x03e00009#32]
#guard decode 0x03e00409#32 = some (.jalrHb 31#32 0#32)
#guard decode 0x0320fc09#32 = some (.jalrHb 25#32 31#32)
#guard decode 0x03204409#32 = some (.jalrHb 25#32 8#32)
#guard decode 0x03e00009#32 = some (.jalr 31#32 0#32)
-- the pre-Release 6 JR / JR.HB words (funct 0x08) do not decode (JR p.207: "removed in Release 6")
#guard decode 0x03e00008#32 = none ∧ decode 0x03e00408#32 = none
-- any other hint value is no defined encoding (Reserved Instruction; the review reproducer r4)
#guard decode 0x01000048#32 = none   -- jr $t0, hint 1
#guard decode 0x010007c8#32 = none   -- jr $t0, hint 31
#guard decode 0x0100f849#32 = none   -- jalr $ra, $t0, hint 1
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

-- ## FPU: high-half moves; PREF (Release 6 SPECIAL3, 9-bit offset)
#guard asmText (srcLines ["mfhc1 $8, $f4", "mthc1 $8, $f4", "pref 1, 16($4)", "pref 0, -4($sp)"])
  = some [encode (.mfhc1 8#32 4#32), encode (.mthc1 8#32 4#32),
          encode (.pref 4#32 1#32 16#32), encode (.pref 29#32 0#32 0x1fc#32)]
#guard asmText "pref 1, 16($4)\n" = some [0x7c810835#32]
-- recip / rsqrt, double → word
#guard asmText (srcLines ["recip.s $f2, $f4", "recip.d $f2, $f4", "rsqrt.s $f2, $f4", "rsqrt.d $f2, $f4",
    "round.w.d $f2, $f4", "trunc.w.d $f2, $f4", "ceil.w.d $f2, $f4", "floor.w.d $f2, $f4"])
  = some [encode (.recipS 2#32 4#32), encode (.recipD 2#32 4#32), encode (.rsqrtS 2#32 4#32),
          encode (.rsqrtD 2#32 4#32), encode (.roundWD 2#32 4#32), encode (.truncWD 2#32 4#32),
          encode (.ceilWD 2#32 4#32), encode (.floorWD 2#32 4#32)]
-- di / ei
#guard asmText "di\ndi $t1\nei\nei $t0\n"
  = some [encode (.di 0#32), encode (.di 9#32), encode (.ei 0#32), encode (.ei 8#32)]
#guard asmText "di\nei $t0\n" = some [0x41606000#32, 0x41686020#32]
-- `.set`: noreorder / noat / at accepted, reorder and anything else rejected
#guard asmText ".set noreorder\n.set noat\nnop\n.set at\nnop\n" = some [0#32, 0#32]
#guard asmFails ".set reorder\nnop\n"
#guard asmFails ".set mips32r2\nnop\n"
#guard asmFails ".set\n"
-- under `.set noat` the `$at` idioms are rejected; `.set at` re-enables them
#guard asmFails (srcLines [".set noat", "L: blt $t0, $t1, L"])
#guard (assemble (srcLines [".set noat", ".set at", "L: blt $t0, $t1, L"])).isOk
#guard (assemble (srcLines [".set noat", "L: beq $t0, $t1, L", "li $t0, 0x12345678"])).isOk
