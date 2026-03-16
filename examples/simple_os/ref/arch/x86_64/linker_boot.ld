/*
 * linker_boot.ld — 32-bit ELF linker script for x86_64 boot wrapper
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * Produces an ELF32-i386 binary that QEMU's Multiboot1 loader accepts.
 * The boot wrapper occupies the first 4 KB (0x100000..0x100FFF).
 * The embedded 64-bit kernel payload (.payload section) is placed at
 * 0x101000, matching kernel64.elf's link address.
 */

OUTPUT_FORMAT(elf32-i386)
ENTRY(_start)

SECTIONS
{
    . = 0x00100000;

    /* ── Multiboot header (must be in first 8 KB of file) ───── */
    .multiboot ALIGN(4) :
    {
        *(.multiboot)
    }

    /* ── 32-bit boot trampoline code ─────────────────────────── */
    .text ALIGN(16) :
    {
        *(.text)
        *(.text.*)
    }

    /* ── Boot GDT (read-only data) ───────────────────────────── */
    .rodata ALIGN(16) :
    {
        *(.rodata)
        *(.rodata.*)
    }

    /* ── Embedded 64-bit kernel — MUST be at 0x101000 ────────── */
    .payload 0x00101000 :
    {
        *(.payload)
    }

    /* ── BSS: boot page tables ───────────────────────────────── */
    .bss ALIGN(4096) :
    {
        *(.bss)
        *(.bss.*)
        *(COMMON)
    }

    /* ── Discard unwanted sections ───────────────────────────── */
    /DISCARD/ :
    {
        *(.comment)
        *(.note)
        *(.note.*)
        *(.eh_frame)
    }
}
