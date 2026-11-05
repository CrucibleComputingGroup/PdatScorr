.option norvc
.option norelax
.section .text,"ax",@progbits
.globl _start
_start:
    li s0, 0x1000
    li s1, 0x2000
    li s2, 64
loop:
    ld a0, 0(s0)
    addi a1, a0, 1
    sd a1, 0(s1)
    addi s0, s0, 8
    addi s1, s1, 8
    addi s2, s2, -1
    bnez s2, loop
    li t0, 0x20000100
    sb zero, 0(t0)
halt:
    j halt

.section .rodata,"a",@progbits
.balign 8
input_values:
    .incbin "input.bin"
input_padding:
    .zero 128
