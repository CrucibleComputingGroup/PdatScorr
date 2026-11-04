OUTPUT_ARCH(riscv)
ENTRY(_start)
MEMORY {
  ROM (rx) : ORIGIN = 0x1000, LENGTH = 60K
  RAM (rw) : ORIGIN = 0x80000000, LENGTH = 128K
}
SECTIONS {
  .text : { *(.text.start) *(.text .text.*) } > ROM
  .rodata : { *(.rodata .rodata.* .srodata .srodata.*) . = ALIGN(4); } > ROM
  .data : {
    __data_start = .;
    *(.data .data.* .sdata .sdata.*)
    . = ALIGN(4);
    __data_end = .;
  } > RAM AT> ROM
  __data_load = LOADADDR(.data);
  .bss (NOLOAD) : {
    __bss_start = .;
    *(.bss .bss.* .sbss .sbss.* COMMON)
    . = ALIGN(4);
    __bss_end = .;
  } > RAM
  /DISCARD/ : { *(.comment .eh_frame .riscv.attributes) }
}
