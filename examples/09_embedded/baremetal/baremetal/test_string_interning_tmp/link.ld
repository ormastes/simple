ENTRY(_start)
SECTIONS
{
    . = 0x80000000;
    .text : { *(.text) }
    . = 0x80000100;           /* Align .smt to expected location */
    .smt : { *(.smt) }
}
