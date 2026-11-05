.option norvc
.option norelax
.section .text
.globl _start
_start:
    li t4, 0x400
    ld t5, 0(t4)
    li t6, 3
    bne t5, t6, fail
    li t0, -1
    divu t2, t0, t5
consumers:
    addi a0, t2, 1
    addi a1, t2, 2
    addi a2, t2, 3
    addi a3, t2, 4
    addi a4, t2, 5
    addi a5, t2, 6
    addi a6, t2, 7
    addi a7, t2, 8
    li t3, 0x5555555555555555
    bne t2, t3, fail
    addi t3, t3, 1
    bne a0, t3, fail
    addi t3, t3, 1
    bne a1, t3, fail
    addi t3, t3, 1
    bne a2, t3, fail
    addi t3, t3, 1
    bne a3, t3, fail
    addi t3, t3, 1
    bne a4, t3, fail
    addi t3, t3, 1
    bne a5, t3, fail
    addi t3, t3, 1
    bne a6, t3, fail
    addi t3, t3, 1
    bne a7, t3, fail
    li t0, 0
    j exit
fail:
    li t0, 1
exit:
    li t1, 0x20000100
    sb t0, 0(t1)
1:  j 1b
.org 0x400
    .dword 3
