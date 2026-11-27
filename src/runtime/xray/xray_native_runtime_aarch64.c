/*
 * xray_native_runtime_aarch64.c -- stage-2 resident XRay runtime for the
 * pure-Simple native AArch64 backend (XRay PR5b).
 *
 * Design: doc/04_architecture/compiler/xray/xray_compiler_structural_change_2026-11-06.md
 * sections A.5, C.2-C.5. Linked ONLY into `--xray` native builds (driver:
 * src/compiler/80.driver/driver_xray_link.spl); never part of the core
 * runtime archive, so an OFF build is unchanged.
 *
 * Three pieces, smallest possible C/asm boundary:
 *  1. `__simple_xray_trampoline_v1` (asm): the target of every sled's BL.
 *     Irreplaceable save/restore only. Simple twin:
 *     src/lib/common/trace/xray_native_trampoline_aarch64_v1.spl encodes the
 *     same instruction words; scripts/check/check-xray-native-inprocess-e2e.shs
 *     compares them with this object's disassembly word for word.
 *  2. The AArch64 sled leaf for registration: the activation word is the
 *     V1 OFF/ON word and the sled's BL targets this TU's trampoline.
 *  3. Everything ISA-neutral -- hot-path handler, module registration and
 *     channel publication -- is shared with the x86-64 runtime through
 *     xray_native_registry_v1.h (called by the Simple control plane
 *     src/lib/nogc_sync_mut/trace/xray_native_module_v1.spl).
 *
 * Sled contract (trace_native_off_template_v1, Arm64Branch26): on entry
 * x0 = site id (w0, zero-extended by MOVZ/MOVK), x30 = sled + 24 (the BL is at
 * sled + 20), and the sled has already pushed x16/x17 and x0/x30. SP is
 * 16-byte aligned. The trampoline must return with every other register,
 * NZCV and FPCR/FPSR exactly as found; the sled restores x0/x30/x16/x17.
 *
 * Saved here: x1-x15, x18 (x0/x16/x17/x30 by the sled), x29/x30 frame, NZCV,
 * FPCR, FPSR and ALL of q0-q31 (the AAPCS64 caller-saved FP set is v0-v7,
 * v16-v31 and the upper halves of v8-v15; saving q0-q31 whole covers it
 * without trusting the handler's code generation). x19-x28 are callee-saved
 * by the handler per AAPCS64.
 *
 * Hot-path rules (plan section 7): no lock, no allocation, no libc call, no
 * syscall. Build with -mgeneral-regs-only -mno-outline-atomics. Not `rt_*`.
 *
 * Visibility: the trampoline and entry points are PROTECTED, so the sleds of
 * the module that carries this TU bind to its own copy with a direct BL (no
 * PLT veneer between sled and trampoline) and every --xray module owns one
 * resident runtime instance; the entry points stay dlsym-able for the
 * loaded-module path.
 */
#include <stdint.h>

#if defined(__linux__) && defined(__aarch64__)
#define SIMPLE_XRAY_NATIVE_SUPPORTED 1
#endif

/* AArch64 sled shape (xray_native_map_format_v1.spl). */
#define XMAP_ISA 2
#define XMAP_ABI 1
#define XMAP_SLED_BYTES 32
#define XMAP_SLED_ALIGN 4
#define XMAP_OFF_WORD 0x14000008u /* B +32 */
#define XMAP_ON_WORD 0xD503201Fu  /* NOP */
/* x30 = sled + 24: the BL is at sled + 20. */
#define XMAP_RETURN_TO_SLED 24

#ifdef SIMPLE_XRAY_NATIVE_SUPPORTED

extern void __simple_xray_trampoline_v1(void);

/* Registration leaf: first word OFF or ON, and the BL at +20 reaches THIS
 * runtime's trampoline. */
static int xray_isa_sled_calls_trampoline(uintptr_t sled, uint32_t site_id) {
    (void)site_id; /* materialised by MOVZ/MOVK; the map row index binds it */
    uint32_t word = __atomic_load_n((const uint32_t *)sled, __ATOMIC_RELAXED);
    if (word != XMAP_OFF_WORD && word != XMAP_ON_WORD) return 0;
    uint32_t bl = __atomic_load_n((const uint32_t *)(sled + 20), __ATOMIC_RELAXED);
    if ((bl & 0xFC000000u) != 0x94000000u) return 0;
    int64_t imm = (int64_t)(bl & 0x3FFFFFFu);
    if (imm >= 0x2000000) imm -= 0x4000000;
    return sled + 20 + (uintptr_t)(imm * 4) == (uintptr_t)&__simple_xray_trampoline_v1;
}

/* Saves x1-x15, x18, x29/x30, NZCV, FPCR, FPSR, q0-q31 (688-byte frame incl.
 * the x29/x30 pair), passes x0 = site id and x1 = sled return address. */
__asm__(
    ".text\n"
    /* The TU is -mgeneral-regs-only for the handler; the trampoline itself
     * must name FP/SIMD state to save it. */
    ".arch_extension fp\n"
    ".arch_extension simd\n"
    ".p2align 2\n"
    ".globl __simple_xray_trampoline_v1\n"
    ".protected __simple_xray_trampoline_v1\n"
    ".type __simple_xray_trampoline_v1, %function\n"
    "__simple_xray_trampoline_v1:\n"
    "    stp x29, x30, [sp, #-16]!\n"
    "    mov x29, sp\n"
    "    sub sp, sp, #672\n"
    "    stp x1, x2, [sp, #0]\n"
    "    stp x3, x4, [sp, #16]\n"
    "    stp x5, x6, [sp, #32]\n"
    "    stp x7, x8, [sp, #48]\n"
    "    stp x9, x10, [sp, #64]\n"
    "    stp x11, x12, [sp, #80]\n"
    "    stp x13, x14, [sp, #96]\n"
    "    stp x15, x18, [sp, #112]\n"
    "    mrs x9, nzcv\n"
    "    mrs x10, fpcr\n"
    "    mrs x11, fpsr\n"
    "    stp x9, x10, [sp, #128]\n"
    "    str x11, [sp, #144]\n"
    "    add x9, sp, #160\n"
    "    stp q0, q1, [x9, #0]\n"
    "    stp q2, q3, [x9, #32]\n"
    "    stp q4, q5, [x9, #64]\n"
    "    stp q6, q7, [x9, #96]\n"
    "    stp q8, q9, [x9, #128]\n"
    "    stp q10, q11, [x9, #160]\n"
    "    stp q12, q13, [x9, #192]\n"
    "    stp q14, q15, [x9, #224]\n"
    "    stp q16, q17, [x9, #256]\n"
    "    stp q18, q19, [x9, #288]\n"
    "    stp q20, q21, [x9, #320]\n"
    "    stp q22, q23, [x9, #352]\n"
    "    stp q24, q25, [x9, #384]\n"
    "    stp q26, q27, [x9, #416]\n"
    "    stp q28, q29, [x9, #448]\n"
    "    stp q30, q31, [x9, #480]\n"
    "    mov w0, w0\n"
    "    mov x1, x30\n"
    "    bl simple_xray_native_handler_v1\n"
    "    add x9, sp, #160\n"
    "    ldp q0, q1, [x9, #0]\n"
    "    ldp q2, q3, [x9, #32]\n"
    "    ldp q4, q5, [x9, #64]\n"
    "    ldp q6, q7, [x9, #96]\n"
    "    ldp q8, q9, [x9, #128]\n"
    "    ldp q10, q11, [x9, #160]\n"
    "    ldp q12, q13, [x9, #192]\n"
    "    ldp q14, q15, [x9, #224]\n"
    "    ldp q16, q17, [x9, #256]\n"
    "    ldp q18, q19, [x9, #288]\n"
    "    ldp q20, q21, [x9, #320]\n"
    "    ldp q22, q23, [x9, #352]\n"
    "    ldp q24, q25, [x9, #384]\n"
    "    ldp q26, q27, [x9, #416]\n"
    "    ldp q28, q29, [x9, #448]\n"
    "    ldp q30, q31, [x9, #480]\n"
    "    ldp x9, x10, [sp, #128]\n"
    "    ldr x11, [sp, #144]\n"
    "    msr nzcv, x9\n"
    "    msr fpcr, x10\n"
    "    msr fpsr, x11\n"
    "    ldp x1, x2, [sp, #0]\n"
    "    ldp x3, x4, [sp, #16]\n"
    "    ldp x5, x6, [sp, #32]\n"
    "    ldp x7, x8, [sp, #48]\n"
    "    ldp x9, x10, [sp, #64]\n"
    "    ldp x11, x12, [sp, #80]\n"
    "    ldp x13, x14, [sp, #96]\n"
    "    ldp x15, x18, [sp, #112]\n"
    "    mov sp, x29\n"
    "    ldp x29, x30, [sp], #16\n"
    "    ret\n"
    ".size __simple_xray_trampoline_v1, .-__simple_xray_trampoline_v1\n");

#endif /* SIMPLE_XRAY_NATIVE_SUPPORTED */

#include "xray_native_registry_v1.h"

SIMPLE_XRAY_NATIVE_ENTRY_POINTS_V1
