.option norelax
.option norvc
.section .text.start
.globl _start, _end
_start:
  j init
_end:
  j _end
init:
  la t0, trap
  csrw mtvec, t0
  li sp, 0x80020000
  la t0, __data_load
  la t1, __data_start
  la t2, __data_end
1:
  bgeu t1, t2, 2f
  lw t3, 0(t0)
  sw t3, 0(t1)
  addi t0, t0, 4
  addi t1, t1, 4
  j 1b
2:
  la t1, __bss_start
  la t2, __bss_end
3:
  bgeu t1, t2, 4f
  sw zero, 0(t1)
  addi t1, t1, 4
  j 3b
4:
  li a0, 0
  li a1, 0
  call main
  fence rw, rw
  j _end
trap:
  li t0, 0x40002000
  li t1, 33
  sb t1, 0(t0)
5:
  j 5b
