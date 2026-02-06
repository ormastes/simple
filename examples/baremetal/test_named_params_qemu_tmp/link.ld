ENTRY(_start)
SECTIONS
{
    . = 0x80000000;
    .text : { *(.text) }
    . = 0x80000100;
    .smt : { *(.smt) }
    . = 0x80001000;
    .data : { *(.data) }
}
