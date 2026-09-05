/*
 * x86_64 Bare-Metal Linker Script
 *
 * Target: x86_64 processors (QEMU, physical hardware)
 * Bootloader: Multiboot1 compatible (QEMU -kernel)
 *
 * Memory Layout:
 *   0x00100000 - Kernel load address (1MB mark)
 *   0x00200000 - Stack (grows down)
 *   Identity-mapped first 1GB via page tables
 *
 * Sections:
 *   .text.entry - Multiboot1 header + _start (must be in first 8KB)
 *   .text       - Code and read-only data
 *   .rodata     - Read-only data (GDT, etc.)
 *   .data       - Initialized data
 *   .bss        - Uninitialized data (page tables, stack)
 *   .heap       - Dynamic memory allocation
 */

ENTRY(_entry32)

SECTIONS
{
    /* Kernel load base.
     *
     * Historically 1MB (0x100000, the classic multiboot low-memory mark). That
     * works for QEMU `-kernel` and for a small (~2MB text) kernel under
     * GRUB-EFI/OVMF. But the large merged ring-3 kernel (~22.6MB text) occupies
     * the whole low region [1MB, ~237MB] once its file image + 236MB BSS are
     * placed there, which starves GRUB-EFI's multiboot1 relocator of a safe
     * low scratch/trampoline slot and makes it fault (#UD at RIP~0x1012 in the
     * relocator, caught by OVMF, before the kernel _start ever runs).
     *
     * Loading at 128MB leaves the entire [1MB, 128MB) low region free for
     * GRUB's relocator trampoline + multiboot info, while staying well within
     * the crt0 identity map (first 4GiB) and below the PMM heap region
     * (0x80000000). QEMU `-kernel` honours p_paddr identically, so that path is
     * unaffected. */
    . = 0x100000; /* low-1MB variant for the QEMU -kernel getfile lane. Ring-3 payloads (clang_static) now link at 0x40000000 (1GiB, see sysroot.shs), so they are clear of the kernel .bss at either the 1MB or the 128MB base. This variant stays at 1MB for the proven QEMU -kernel lane; the OVMF/GRUB-EFI lane uses linker_128mb.ld (128MB base) so GRUB's multiboot1 relocator has a low scratch slot. */
    _kernel_start = .;

    /* Code section — .text.entry first for Multiboot header */
    .text ALIGN(4K) :
    {
        KEEP(*(.text.entry))
        KEEP(*(.multiboot))
        *(.text)
        *(.text.*)
    }
    /* The x86_64 boot crt0 places a fixed 28-byte Multiboot1 header at the
     * start of .text.entry, followed immediately by the 32-bit boot entry.
     * Some current toolchain paths are dropping the assembler's _entry32
     * symbol from the final ELF symbol table, which leaves e_entry as 0 and
     * makes QEMU reject the kernel image. Recreate the symbol at link time so
     * ENTRY(_entry32) always resolves to the actual boot code. */
    _entry32 = ADDR(.text) + 28;
    _start = _entry32;

    /* Read-only data */
    .rodata ALIGN(4K) :
    {
        *(.rodata)
        *(.rodata.*)
    }

    /* Initialized data */
    .data ALIGN(4K) :
    {
        *(.data)
        *(.data.*)
    }

    /* Uninitialized data */
    .bss ALIGN(4K) :
    {
        __bss_start = .;
        *(COMMON)
        *(.bss)
        *(.bss.*)
        __bss_end = .;
    }

    /* Heap (grows upward) — NOLOAD so ld emits SHT_NOBITS and QEMU's
     * multiboot loader does not have to read/write megabytes of zero
     * content out of the ELF file. */
    .heap ALIGN(4K) (NOLOAD) :
    {
        __heap_start = .;
        . = . + 16M;  /* 16MB linker-script heap (in addition to _heap[]) */
        __heap_end = .;
    }

    /* Stack (grows downward) — NOLOAD for the same reason. Without this
     * ld marks the section PROGBITS, inflates the ELF file by the stack
     * size, and QEMU either truncates the kernel load or extends the
     * kernel image beyond the configured -m memory. The resulting
     * stack-pointer-above-physical-RAM was the root cause of Agent M's
     * 0x950a cascading fault. */
    .stack ALIGN(4K) (NOLOAD) :
    {
        . = . + 8M;  /* 8MB stack — Simple code uses large stack frames */
        _stack_top = .;
    }

    /* End of kernel */
    _kernel_end = .;


    /* Debug sections */
    .debug_info 0 : { *(.debug_info) }
    .debug_abbrev 0 : { *(.debug_abbrev) }
    .debug_line 0 : { *(.debug_line) }
    .debug_str 0 : { *(.debug_str) }
    .debug_frame 0 : { *(.debug_frame) }
    .debug_loc 0 : { *(.debug_loc) }
    .debug_ranges 0 : { *(.debug_ranges) }

    /* Discard unwanted sections */
    /DISCARD/ :
    {
        *(.note*)
        *(.eh_frame*)
        *(.comment)
    }
}
