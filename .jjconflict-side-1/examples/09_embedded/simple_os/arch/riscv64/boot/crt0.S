/* riscv64 SimpleOS early-boot stub with RISC-V Linux `Image` boot header.
 *
 * Mirrors the arm64 design (arch/arm64/boot/crt0.S): the kernel's flat image
 * begins with the standard RISC-V Linux boot-image header
 * (Linux Documentation/arch/riscv/boot-image-header.rst, header version 0.2),
 * so ANY Image-protocol loader (U-Boot `booti`, Limine `protocol: linux`,
 * an EFI chain) can load it — and code0 is a real jump, so a direct S-mode
 * handover (OpenSBI fw_payload / fw_jump to 0x80200000) executes the very
 * same bytes and simply jumps over the header. One artifact, both chains.
 *
 * Entry contract (identical for both chains, the OpenSBI S-mode handover):
 *   a0 = hartid, a1 = physical address of the device tree blob.
 *   MMU off, running physically at the link address 0x80200000
 *   (= RAM base 0x80000000 + text_offset 0x200000).
 *
 * The stub sets gp/sp, zeroes .bss, preserves a0/a1, and calls
 * `boot_entry(hartid, dtb)`.  Gated by
 * scripts/check/check-simpleos-riscv64-image-header-contract.shs and booted
 * under real firmware by
 * scripts/check/check-simpleos-riscv64-opensbi-guest-boot.shs.
 */

    .section .text.entry, "ax", %progbits
    .globl _start
_start:
    /* -- 64-byte RISC-V Linux Image header (version 0.2) ------------------ */
.option push
.option norvc                       /* code0 must be a full 4-byte JAL, not c.j */
    j    _start_kernel              /* code0: executable jump over header */
.option pop
    .word 0                         /* code1 */
    .dword 0x200000                 /* text_offset: 2MB from RAM base (RV64) */
    .dword _kernel_end - _start /* image_size (mandatory, le) */
    .dword 0                        /* flags: bit0=0 -> little-endian */
    .word 0x00000002                /* version 0.2 (major 0, minor 2) */
    .word 0                         /* res1 */
    .dword 0                        /* res2 */
    .dword 0x5643534952             /* magic "RISCV" (deprecated, kept) */
    .word 0x05435352                /* magic2 "RSC\x05" — what loaders test */
    .word 0                         /* res3 (PE/COFF offset; 0 = no EFI stub) */

_start_kernel:
    /* gp must be set with relaxation off, or la gp is optimised via gp. */
.option push
.option norelax
    la   gp, __global_pointer$
.option pop
    la   sp, _stack_top

    /* Preserve the firmware handover registers across bss zeroing. */
    mv   s0, a0                     /* hartid */
    mv   s1, a1                     /* dtb */

    /* Zero .bss (linker provides _sbss/_ebss, both 8-byte aligned enough). */
    la   t0, _sbss
    la   t1, _ebss
1:  bgeu t0, t1, 2f
    sd   zero, 0(t0)
    addi t0, t0, 8
    j    1b
2:
    mv   a0, s0
    mv   a1, s1
    call boot_entry

3:  wfi
    j    3b

/* End of the LOADED image (bss/stack/heap are NOLOAD and not in the flat
 * Image; a loader still gets a nonzero, truthful loaded-size to reserve). */
    .section .rodata
    .globl _kernel_image_size_ref
_kernel_image_size_ref:
    .dword _kernel_end - _start
