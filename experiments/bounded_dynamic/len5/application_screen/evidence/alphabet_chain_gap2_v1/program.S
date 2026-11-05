.option norvc
.option norelax
.section .text
.globl _start
_start:
    lui s0, 0x1
    .rept 64
    addi s0, s0, 8
    .endr
    lui t0, 0x20000
    addiw t0, t0, 256
    sb zero, 0(t0)
halt:
    jal zero, halt
// Map speculative fetches after the halt with words from the same alphabet.
    .rept 64
    .word 0x0000006f
    .endr
