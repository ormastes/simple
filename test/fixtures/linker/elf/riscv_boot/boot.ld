ENTRY(_start)
SECTIONS { . = 0x200000; .text : { *(.text.boot) *(.text*) } . = ALIGN(16); .rodata : { *(.rodata*) } . = ALIGN(16); .data : { *(.data*) } }
