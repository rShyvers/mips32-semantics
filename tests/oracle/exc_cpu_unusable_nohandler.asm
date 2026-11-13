# Status.CU1 cleared via mtc0, then add.s: Coprocessor Unusable (ExcCode 11, Cause.CE = 1), unhandled.
# MD00090 Vol III Rev 6.02 sec 6.2.22 (Coprocessor Unusable: ExcCode 11, Cause.CE = coprocessor number when Status.CU1 = 0); MD00086 Vol II-A Rev 6.06 each FP instruction's 'Exceptions: Coprocessor Unusable'.
# oracle: expect cause=0x1000002c
.data
res: .space 64
.text
mtc0 $zero, $12
add.s $f2, $f4, $f6
