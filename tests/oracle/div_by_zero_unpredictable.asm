# Division by zero: no exception, HI/LO UNPREDICTABLE. MD00086 Vol II-A Rev 6.06: DIV p.165 ("If the divisor in GPR
# rt is zero, the arithmetic result value is UNPREDICTABLE"), DIVU p.171. Only 'no exception, execution continues' is checked.
# oracle: unpredictable hi MD00086 DIV p.165: divisor zero => HI UNPREDICTABLE
# oracle: unpredictable lo MD00086 DIV p.165: divisor zero => LO UNPREDICTABLE
li $t0, 123
div $t0, $zero
divu $t0, $zero
li $s0, 1                  # reached: no exception
li $v0, 10
syscall
