/*
 * x86_64 Bare-Metal Linker Script — 128 MiB base (GRUB-EFI / OVMF)
 *
 * Target: x86_64 processors booted via UEFI firmware (OVMF) -> GRUB-EFI ->
 *         multiboot1. This is the real-board boot chain (NOT QEMU `-kernel`).
 * Bootloader: Multiboot1 compatible.
 *
 * Why 128 MiB (0x08000000) instead of 1 MiB:
 *   The large merged ring-3 kernel occupies the whole low region [1MB, ~229MB]
 *   at a 1MB base (its file image + ~211MB NOBITS .bss). That starves GRUB-EFI's
 *   multiboot1 relocator of a safe low scratch/trampoline slot and faults
 *   (#UD at RIP~0x1012 in the relocator, caught by OVMF, before _start runs).
 *   Loading at 128MB leaves [1MB,128MB) free for GRUB's relocator + multiboot
 *   info while staying within the crt0 identity map (first 4GiB) and below the
 *   PMM heap (0x80000000). Kernel .bss then reaches ~0x16400000 (~356MB); the
 *   ring-3 payload is linked at 0x40000000 (1GiB, see sysroot.shs simpleos.ld)
 *   and the mmap base at 0x50000000, both clear of that band.
 *
 * Memory Layout:
 *   0x08000000 - Kernel load address (128MB mark)
 *   Identity-mapped first 4GB via page tables
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
    /* Kernel base 128MB — leaves [1MB,128MB) free for GRUB-EFI's multiboot1
     * relocator trampoline + boot info (see header). QEMU `-kernel` honours
     * p_paddr identically, but this variant is intended for the OVMF/GRUB-EFI
     * lane; the QEMU `-kernel` getfile lane keeps linker_low1mb.ld at 1MB. */
    . = 0x8000000;
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

    /*
     * Strong C-ABI aliases for spl_handle_* syscall shims.
     *
     * The Simple compiler's --entry-closure DCE retains the functions (visible
     * as kernel__abi__syscall_shim__spl_handle_* W symbols) but does NOT emit
     * strong --defsym aliases for @export("C") on non-entry functions.
     * The weak stubs in baremetal_stubs.c therefore win the W vs W arbitration.
     *
     * These linker-script assignments create strong (T) aliases that override
     * both the weak baremetal stubs and the internal mangled names.
     *
     * One entry per spl_handle_* function defined in
     * src/os/kernel/abi/syscall_shim.spl (62 shims, Wave 10D).
     */
    /* Syscall-shim aliases.
     *
     * GENERATED, not hand-maintained.  The previous hand-written block assumed
     * every shim lived in one module and mangled as
     * `kernel__abi__syscall_shim__spl_handle_*`.  That layout no longer exists:
     * the shims were split into syscall_shim_{process,ipc,file,net,device,...}
     * and the seed emits a `src__os__` prefix, so all 66 assignments named
     * symbols that are defined nowhere and ld.lld failed the link outright.
     * Same staleness class as the B1 facade re-exports, in the linker script.
     *
     * PROVIDE() rather than `=`: a plain assignment to a missing symbol is a
     * hard error even when nothing references the alias, which made the script
     * brittle against --entry-closure pruning.  PROVIDE is evaluated only when
     * the alias is actually referenced and still undefined.
     *
     * UPDATE: the regenerated PROVIDE table is gone too. Regenerating a static
     * table from one build's `nm` output only resets the rot clock -- the
     * mangling carries an entry-specific prefix, so the table is correct for
     * exactly the entry and seed it was generated against.
     *
     * The aliasing is now DERIVED at link time by the compiler:
     * NativeLinker::freestanding_weak_boot_defsyms
     * (src/compiler_rust/compiler/src/pipeline/native_project/linker.rs) reads
     * the boot objects' weak-DEFINED spl_handle_* symbols with `nm`, finds the
     * unique strongly defined `*__spl_handle_X` among the Simple objects --
     * whatever module it now lives in -- and passes
     * `--defsym=spl_handle_X=<real symbol>` to lld. Split-agnostic, entry
     * agnostic, seed agnostic.
     *
     * This script is shared with the SSH lane. Do not re-add a static table;
     * guarded by scripts/check/check-simpleos-x86-64-linker-alias-derived.shs.
     */

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
