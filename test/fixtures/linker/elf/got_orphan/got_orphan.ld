ENTRY(_start)
SECTIONS {
    . = 0x50000000;
    .text : { *(.text*) }
    . = ALIGN(4096);
    .data : { *(.data*) }
    . = ALIGN(8);
    .got : { *(.got) *(.got.*) }
    . = ALIGN(16);
    .init_array : { __init_array_start = .; KEEP(*(.init_array*)) __init_array_end = .; }
    . = ALIGN(4096);
    .bss : { *(.bss*) }
}
