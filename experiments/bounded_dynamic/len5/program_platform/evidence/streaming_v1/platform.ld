OUTPUT_ARCH(riscv)
ENTRY(_start)
PHDRS
{
  text PT_LOAD FLAGS(5);   /* read, execute */
  data PT_LOAD FLAGS(4);   /* read, no execution */
}
SECTIONS
{
  .text 0 : { KEEP(*(.text)) *(.text.*) } :text
  .rodata 0x1000 : { *(.rodata .rodata.*) } :data
  /DISCARD/ : { *(.comment) *(.note*) }
}
ASSERT(SIZEOF(.text) == 56, "Streaming instruction bytes changed")
ASSERT(SIZEOF(.rodata) == 640, "Expected 64 uint64 inputs plus 128 padding bytes")
