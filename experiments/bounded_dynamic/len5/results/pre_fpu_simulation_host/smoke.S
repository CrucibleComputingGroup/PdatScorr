.option norvc
.section .text
.globl _start
_start:
    li t0, 0
    li t1, 0
    li t2, 64
1:  add t0, t0, t1
    addi t1, t1, 1
    bne t1, t2, 1b
    li t3, 2016
    bne t0, t3, fail
    li t4, 0x400
    sd t0, 0(t4)
    ld t5, 0(t4)
    bne t5, t3, fail
    li t0, 0
    j exit
fail:
    li t0, 1
exit:
    li t1, 0x20000100
    sb t0, 0(t1)
2:  j 2b
.org 0x400
    .dword 0
