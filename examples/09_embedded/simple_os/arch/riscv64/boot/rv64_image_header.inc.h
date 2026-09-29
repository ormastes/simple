/* rv64_image_header.inc.h — RISC-V Linux boot-image header v0.2 as an asm
 * fragment for naked-C `_start` stubs.
 *
 * Same 64-byte header as arch/riscv64/boot/crt0.S (the contract artifact,
 * gated by scripts/check/check-simpleos-riscv64-image-header-contract.shs):
 * code0 is a real 4-byte JAL over the header, so a direct OpenSBI S-mode
 * handover to 0x80200000 executes unchanged, while an Image-protocol loader
 * (U-Boot booti / Limine `protocol: linux`) recognises magic2 "RSC\x05".
 *
 * Usage inside the naked _start asm, as the FIRST statements:
 *     __asm__ volatile(
 *         RV64_IMAGE_HEADER_ASM
 *         "la sp, _stack_top\n"
 *         ...);
 * The header jump lands on 1000f (a local numeric label defined by the
 * fragment right after the header), i.e. exactly where the stub's own code
 * begins — direct-entry semantics are preserved bit-for-bit.
 *
 * image_size uses `_kernel_end - 0x80200000` (linker_riscv_common.ld /
 * ghdl_boot_info_linker.ld both define _kernel_end; both link at
 * 0x80200000): the mandatory nonzero loaded-size field, little-endian.
 */
#ifndef RV64_IMAGE_HEADER_INC_H
#define RV64_IMAGE_HEADER_INC_H

#define RV64_IMAGE_HEADER_ASM                                            \
    ".option push\n"                                                     \
    ".option norvc\n"           /* code0 must be a full 4-byte JAL */    \
    "j 1000f\n"                 /* code0 */                              \
    ".option pop\n"                                                      \
    ".word 0\n"                 /* code1 */                              \
    ".dword 0x200000\n"         /* text_offset: 2MB from RAM base */     \
    ".dword _kernel_end - 0x80200000\n" /* image_size (mandatory) */     \
    ".dword 0\n"                /* flags: little-endian */               \
    ".word 0x00000002\n"        /* header version 0.2 */                 \
    ".word 0\n"                 /* res1 */                               \
    ".dword 0\n"                /* res2 */                               \
    ".dword 0x5643534952\n"     /* magic \"RISCV\" (deprecated) */       \
    ".word 0x05435352\n"        /* magic2 \"RSC\\x05\" */                \
    ".word 0\n"                 /* res3 (no PE/COFF stub) */             \
    "1000:\n"

#endif /* RV64_IMAGE_HEADER_INC_H */
