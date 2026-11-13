# Audit item B2: a label in front of an auto-aligned directive must name the
# aligned datum, whether it is on the same line or on its own line.
# Expected output: "77 88 5" (MARS 4.5 prints the same).
        .data
b:      .byte 1
w:      .word 77            # w = b + 4, not b + 1
        .byte 2
v:
        .word 88            # own-line label (here already aligned, so MARS agrees)
        .byte 3
h:      .half 5
        .text
        la   $t0, w
        lw   $a0, 0($t0)
        li   $v0, 1
        syscall
        li   $a0, ' '
        li   $v0, 11
        syscall
        la   $t0, v
        lw   $a0, 0($t0)
        li   $v0, 1
        syscall
        li   $a0, ' '
        li   $v0, 11
        syscall
        la   $t0, h
        lh   $a0, 0($t0)
        li   $v0, 1
        syscall
        li   $v0, 10
        syscall
