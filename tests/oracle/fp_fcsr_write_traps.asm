# Moving a value into FCSR with an enabled Cause bit takes the Floating Point exception at the ctc1 itself (ExcCode 15, FCSR keeps the written value).
# MD00082 Vol I-A Rev 6.01 sec 6.7.1 p.99: 'A floating point trap is generated any time both a Cause bit and its corresponding Enable bit are set. This occurs either during the execution of a floating point operation or by moving a value into the FCSR.'
# oracle: expect cause=0x3c
.data
res: .space 64
.text
li $t0, 0x00011800
ctc1 $t0, $31
li $s0, 5
