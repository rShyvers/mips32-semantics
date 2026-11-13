# Bare-metal MIPS32r2 big-endian harness for `qemu-system-mips -M malta -cpu 24Kf`.
# See scripts/README.md ("Differential oracle") for the full design.
#
# Physical memory map (all addresses below are kseg0 = 0x80000000 + phys):
#   0x80000000  TLB-refill vector (j refill)          \ 0x80000180 = general vector: the DEFAULT
#   0x80000180  default exception handler (defvec)    / handler, omitted if the test has .ktext
#   0x80010000  this boot code + dump/service code
#   0x80020000  CFG: configuration words generated per test by oracle.py (layout below)
#   0x80030000  BUF: dump buffer (words 0..73), outlen @ +0x400, digit scratch @ +0x500
#   0x80031000  OUTBUF: 8192 bytes of emulated-syscall output
#   0x80100000+ guest text pages, 0x80200000+ guest data pages, 0x80300000 guest stack pages
#   0x80310000  page 0 (virtual 0x0..0xfff of the guest is mapped here): harness scratch
#               at 0xE00..0xFFF (the guest must not use that range of page 0)
#
# CFG word layout: 0..31 GPR, 32 HI, 33 LO, 34 FCSR, 35 Status, 36 Cause, 37 EPC,
#   38 ErrorEPC, 39 start PC, 40 TLB entry count (16), 41..72 FPR, 73.. TLB (EntryHi,Lo0,Lo1)*16
# BUF word layout (printed in this order after magic, kind): 0..31 GPR, 32 HI, 33 LO, 34 FCSR,
#   35 Status, 36 Cause, 37 EPC, 38 BadVAddr, 39 ErrorEPC, 40 pc, 41..72 FPR; 73 = kind
# kinds: 0 exit (syscall, $v0=10)  1 unhandled exception  2 TLB refill/invalid (guest touched an
#   unmapped page)  3 harness limitation (unsupported branch type under a syscall delay slot)
.set noreorder
.set noat
.equ CFG, 0x8002
.equ BUF, 0x8003

.section .text.refill,"ax"
.globl refill
refill:
    sw   $k0,0xF00($zero)
    sw   $k1,0xF04($zero)
    li   $k0,2
    j    dump_entry
    nop

.section .text.defvec,"ax"
.globl defvec
defvec:
    sw   $k0,0xF00($zero)
    sw   $k1,0xF04($zero)
    mfc0 $k0,$13
    andi $k0,$k0,0x7c
    li   $k1,0x20
    bne  $k0,$k1,unh
    nop
    li   $k1,10
    beq  $v0,$k1,do_exit
    li   $k1,1
    beq  $v0,$k1,svc
    li   $k1,4
    beq  $v0,$k1,svc
    li   $k1,11
    beq  $v0,$k1,svc
    nop
unh:                              # k0 = ExcCode<<2
    li   $k1,8                    # TLBL (2) / TLBS (3) => kind 2
    beq  $k0,$k1,1f
    li   $k1,12
    beq  $k0,$k1,1f
    nop
    li   $k0,1
    j    dump_entry
    nop
1:  li   $k0,2
    j    dump_entry
    nop
do_exit:
    li   $k0,0
    j    dump_entry
    nop

.text
.globl _start
_start:
    mtc0 $zero,$12                # Status = 0 (clear BEV/ERL), no CU1 yet
    ehb
    lui  $t0,CFG
    mtc0 $zero,$5                 # PageMask = 4 KB
    mtc0 $zero,$6                 # Wired = 0
    lw   $t2,40*4($t0)
    li   $t1,0
    addiu $t3,$t0,73*4
1:  mtc0 $t1,$0
    lw   $t4,0($t3)
    mtc0 $t4,$10
    lw   $t4,4($t3)
    mtc0 $t4,$2
    lw   $t4,8($t3)
    mtc0 $t4,$3
    ehb
    tlbwi
    addiu $t1,$t1,1
    bne  $t1,$t2,1b
    addiu $t3,$t3,12
    lui  $t4,0x2000               # CU1 so the FPU can be initialised
    mtc0 $t4,$12
    ehb
    .irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
    lw   $t4,(41+\r)*4($t0)
    mtc1 $t4,$f\r
    .endr
    lw   $t4,34*4($t0)
    ctc1 $t4,$31
    lw   $t4,32*4($t0)
    mthi $t4
    lw   $t4,33*4($t0)
    mtlo $t4
    lw   $t4,36*4($t0)
    mtc0 $t4,$13
    lw   $t4,37*4($t0)
    mtc0 $t4,$14
    lw   $t4,38*4($t0)
    mtc0 $t4,$30
    lw   $t4,35*4($t0)
    mtc0 $t4,$12                  # final Status (config includes CU1 if forced)
    ehb
    .irp r,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,27,28,29,30,31
    lw   $\r,4*\r($t0)
    .endr
    lw   $k0,39*4($t0)
    lw   $t0,8*4($t0)
    jr   $k0
    move $k0,$zero                # delay slot: k0 = 0 as in the model (oracle.py checks cfg k0 == 0)

# ---- dump: $k0 = kind; originals of k0/k1 are in the scratch slots 0xF00/0xF04 ----
dump_entry:
    lui  $k1,BUF
    sw   $k0,73*4($k1)
    .irp r,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,28,29,30,31
    sw   $\r,4*\r($k1)
    .endr
    sw   $zero,0($k1)
    lw   $t0,0xF00($zero)
    sw   $t0,26*4($k1)
    lw   $t0,0xF04($zero)
    sw   $t0,27*4($k1)
    mfhi $t0
    sw   $t0,32*4($k1)
    mflo $t0
    sw   $t0,33*4($k1)
    mfc0 $t0,$12
    sw   $t0,35*4($k1)
    mfc0 $t1,$13
    sw   $t1,36*4($k1)
    mfc0 $t2,$14
    sw   $t2,37*4($k1)
    mfc0 $t0,$8
    sw   $t0,38*4($k1)
    mfc0 $t0,$30
    sw   $t0,39*4($k1)
    lui  $t0,0x2000               # CU1 on, IE/EXL off, for the rest of the dump
    mtc0 $t0,$12
    ehb
    cfc1 $t0,$31
    sw   $t0,34*4($k1)
    .irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
    swc1 $f\r,(41+\r)*4($k1)
    .endr
    # pc word, by kind
    lw   $t3,73*4($k1)
    beqz $t3,k_exit
    li   $t4,1
    beq  $t3,$t4,k_unh
    li   $t4,2
    beq  $t3,$t4,k_refill
    nop
    b    k_done
    sw   $zero,40*4($k1)
k_exit:                           # pc = syscall address (EPC, +4 if in a delay slot); hide the
    bgez $t1,1f                   # syscall exception's own Status.EXL / Cause.BD,ExcCode
    move $t5,$t2
    addiu $t5,$t5,4
1:  sw   $t5,40*4($k1)
    lw   $t0,35*4($k1)
    li   $t4,-3
    and  $t0,$t0,$t4
    sw   $t0,35*4($k1)
    lui  $t4,0x7fff
    ori  $t4,$t4,0xff83
    and  $t1,$t1,$t4
    b    k_done
    sw   $t1,36*4($k1)
k_unh:
    lui  $t0,0x8000
    ori  $t0,$t0,0x180
    b    k_done
    sw   $t0,40*4($k1)
k_refill:
    sw   $t2,40*4($k1)
k_done:
    # ---- print ----
    lui  $s7,0xb800
    ori  $s7,$s7,0x03f8
    li   $a0,0x4f524331
    jal  putw
    nop
    lw   $a0,73*4($k1)
    jal  putw
    nop
    li   $s0,0
2:  sll  $t0,$s0,2
    addu $t0,$t0,$k1
    lw   $a0,0($t0)
    jal  putw
    nop
    addiu $s0,$s0,1
    sltiu $t0,$s0,73
    bnez $t0,2b
    nop
    lw   $s1,0x400($k1)           # outlen (may exceed 8192: oracle.py reports overflow)
    move $a0,$s1
    jal  putw
    nop
    sltiu $t0,$s1,8193
    bnez $t0,3f
    nop
    li   $s1,8192
3:  lui  $s2,BUF
    ori  $s2,$s2,0x1000
4:  beqz $s1,5f
    nop
    lbu  $a0,0($s2)
    jal  putw
    nop
    addiu $s2,$s2,1
    b    4b
    addiu $s1,$s1,-1
5:  # memory: nonzero words of guest data (8 pages) and stack (2 pages)
    lui  $s2,0x1001
    li   $s1,8192
    jal  memdump
    nop
    lui  $s2,0x7fff
    ori  $s2,$s2,0xe000
    li   $s1,2048
    jal  memdump
    nop
    li   $a0,-1
    jal  putw
    nop
    lui  $t0,0xbf00               # Malta SOFTRES: exit QEMU
    li   $t1,0x42
    sb   $t1,0x500($t0)
6:  b    6b
    nop

memdump:                          # s2 = start, s1 = word count
    move $s6,$ra
7:  beqz $s1,8f
    nop
    lw   $s3,0($s2)
    beqz $s3,9f
    nop
    move $a0,$s2
    jal  putw
    nop
    move $a0,$s3
    jal  putw
    nop
9:  addiu $s2,$s2,4
    b    7b
    addiu $s1,$s1,-1
8:  jr   $s6
    nop

putw:                             # print $a0 as 8 hex digits + newline on COM1 ($s7); clobbers t5-t8
    li   $t5,28
1:  srlv $t6,$a0,$t5
    andi $t6,$t6,15
    sltiu $t7,$t6,10
    bnez $t7,2f
    addiu $t6,$t6,48
    addiu $t6,$t6,39
2:  lbu  $t8,5($s7)               # LSR: wait for THR empty
    andi $t8,$t8,0x20
    beqz $t8,2b
    nop
    sb   $t6,0($s7)
    bnez $t5,1b
    addiu $t5,$t5,-4
3:  lbu  $t8,5($s7)
    andi $t8,$t8,0x20
    beqz $t8,3b
    nop
    li   $t6,10
    jr   $ra
    sb   $t6,0($s7)

# ---- emulated environment calls 1 (print int), 4 (print string), 11 (print char) ----
svc:
    lui  $k1,BUF
    .irp r,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,28,29,30,31
    sw   $\r,4*\r($k1)
    .endr
    lw   $t0,0xF00($zero)
    sw   $t0,26*4($k1)
    lw   $t0,0xF04($zero)
    sw   $t0,27*4($k1)
    mfhi $t0
    sw   $t0,32*4($k1)
    mflo $t0
    sw   $t0,33*4($k1)
    li   $t0,1
    beq  $v0,$t0,svc_int
    li   $t0,4
    beq  $v0,$t0,svc_str
    nop
svc_chr:
    andi $t0,$a0,0xff
    jal  putb
    nop
    j    svc_done
    nop
svc_str:
1:  lbu  $t0,0($a0)
    beqz $t0,svc_done
    nop
    jal  putb
    nop
    b    1b
    addiu $a0,$a0,1
svc_int:
    bgez $a0,1f
    move $t7,$a0
    li   $t0,45
    jal  putb
    nop
    subu $a0,$zero,$t7
1:  li   $t5,10
    lui  $s1,BUF
    ori  $s1,$s1,0x500
    move $s2,$s1
2:  divu $a0,$t5
    mfhi $t6
    mflo $a0
    addiu $t6,$t6,48
    sb   $t6,0($s2)
    bnez $a0,2b
    addiu $s2,$s2,1
3:  addiu $s2,$s2,-1
    lbu  $t0,0($s2)
    jal  putb
    nop
    bne  $s2,$s1,3b
    nop
svc_done:
    lui  $k1,BUF
    lw   $t0,32*4($k1)
    mthi $t0
    lw   $t0,33*4($k1)
    mtlo $t0
    # --- resume address -> $s0 ---
    mfc0 $s0,$14
    mfc0 $s1,$13
    bltz $s1,bd
    nop
    addiu $s0,$s0,4
    j    resume
    nop
bd: lw   $s2,0($s0)               # the branch whose delay slot held the syscall
    srl  $s3,$s2,26
    addiu $s4,$s0,4               # delay-slot address
    sll  $t5,$s2,16               # branch target = s4 + (simm16<<2)
    sra  $t5,$t5,14
    addu $t6,$s4,$t5
    srl  $t0,$s2,21               # rs, rt values from the saved GPR table
    andi $t0,$t0,31
    sll  $t0,$t0,2
    addu $t0,$t0,$k1
    lw   $s5,0($t0)               # s5 = rs value
    srl  $t0,$s2,16
    andi $t0,$t0,31
    sll  $t0,$t0,2
    addu $t0,$t0,$k1
    lw   $s6,0($t0)               # s6 = rt value
    li   $t0,2
    beq  $s3,$t0,b_j
    li   $t0,3
    beq  $s3,$t0,b_j
    nop
    beqz $s3,b_spec
    li   $t0,1
    beq  $s3,$t0,b_regimm
    li   $t0,4
    beq  $s3,$t0,b_beq
    li   $t0,5
    beq  $s3,$t0,b_bne
    li   $t0,6
    beq  $s3,$t0,b_blez
    li   $t0,7
    beq  $s3,$t0,b_bgtz
    nop
    sltiu $t0,$s3,0x14            # 0x14..0x17: branch-likely: delay slot ran => taken
    bnez $t0,1f
    sltiu $t0,$s3,0x18
    bnez $t0,b_taken
    nop
1:  li   $t0,0x11                 # COP1 branch
    bne  $s3,$t0,unsup
    srl  $t1,$s2,21
    andi $t1,$t1,31
    li   $t0,8
    bne  $t1,$t0,unsup
    srl  $t1,$s2,17               # nd bit
    andi $t1,$t1,1
    bnez $t1,b_taken
    nop
    cfc1 $t2,$31
    srl  $t3,$s2,18
    andi $t3,$t3,7                # cc
    li   $t4,23
    beqz $t3,2f
    nop
    addiu $t4,$t3,24
2:  srlv $t2,$t2,$t4
    andi $t2,$t2,1
    srl  $t3,$s2,16               # tf
    andi $t3,$t3,1
    beq  $t2,$t3,b_taken
    nop
b_nt:
    addiu $s0,$s4,4
    j    resume
    nop
b_taken:
    move $s0,$t6
    j    resume
    nop
b_j:
    sll  $t1,$s2,6
    srl  $t1,$t1,4
    lui  $t2,0xf000
    and  $t2,$s4,$t2
    or   $s0,$t1,$t2
    j    resume
    nop
b_spec:
    andi $t0,$s2,0x3f
    li   $t1,8
    beq  $t0,$t1,1f
    li   $t1,9
    bne  $t0,$t1,unsup
    nop
1:  move $s0,$s5
    j    resume
    nop
b_beq:
    beq  $s5,$s6,b_taken
    nop
    b    b_nt
    nop
b_bne:
    bne  $s5,$s6,b_taken
    nop
    b    b_nt
    nop
b_blez:
    blez $s5,b_taken
    nop
    b    b_nt
    nop
b_bgtz:
    bgtz $s5,b_taken
    nop
    b    b_nt
    nop
b_regimm:
    srl  $t0,$s2,16
    andi $t0,$t0,31
    beqz $t0,r_bltz
    li   $t1,16
    beq  $t0,$t1,r_bltz
    li   $t1,1
    beq  $t0,$t1,r_bgez
    li   $t1,17
    beq  $t0,$t1,r_bgez
    nop
    li   $t1,2                    # likely forms 2,3,18,19: taken
    beq  $t0,$t1,b_taken
    li   $t1,3
    beq  $t0,$t1,b_taken
    li   $t1,18
    beq  $t0,$t1,b_taken
    li   $t1,19
    beq  $t0,$t1,b_taken
    nop
unsup:
    li   $k0,3
    j    dump_entry
    nop
r_bltz:
    bltz $s5,b_taken
    nop
    b    b_nt
    nop
r_bgez:
    bgez $s5,b_taken
    nop
    b    b_nt
    nop
resume:
    sw   $s0,0xF10($zero)
    lui  $k1,BUF
    .irp r,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,28,29,30,31
    lw   $\r,4*\r($k1)
    .endr
    lw   $k0,0xF10($zero)
    mtc0 $k0,$14
    lw   $k0,0xF00($zero)
    lw   $k1,0xF04($zero)
    ehb
    eret

putb:                             # append byte $t0 to OUTBUF; clobbers t1-t4
    lui  $t1,BUF
    lw   $t2,0x400($t1)
    sltiu $t3,$t2,8192
    beqz $t3,1f
    ori  $t4,$t1,0x1000
    addu $t4,$t4,$t2
    sb   $t0,0($t4)
1:  addiu $t2,$t2,1
    jr   $ra
    sw   $t2,0x400($t1)
