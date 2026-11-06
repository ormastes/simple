/*
 * xray_native_runtime_x86_64.c -- stage-2 resident XRay runtime for the
 * pure-Simple native x86-64 backend, SysV profile (XRay PR6).
 *
 * Design: doc/04_architecture/compiler/xray/xray_compiler_structural_change_2026-11-06.md
 * sections A.5, C.2-C.5. Linked ONLY into `--xray` native x86-64 builds
 * (driver: src/compiler/80.driver/driver_xray_link.spl); never part of the
 * core runtime archive, so an OFF build is unchanged. The ISA-neutral half
 * (handler, registry, installer) is xray_native_registry_v1.h, shared with
 * the AArch64 runtime; this TU owns only the x86-64 leaves:
 *  1. `__simple_xray_trampoline_v1` (asm): the target of every sled's CALL.
 *     Irreplaceable save/restore only. Simple twin:
 *     src/lib/common/trace/xray_native_trampoline_x86_64_v1.spl encodes the
 *     same bytes; the x86-64 e2e check compares them with this object's
 *     disassembly byte for byte.
 *  2. The registration sled leaf: activation word OFF (`EB 0B`) or ON
 *     (`66 90`), `E8 rel32` to this TU's trampoline, `EB 04`, and the imm32
 *     site id equal to the row's dense id.
 *
 * Sled contract (trace_native_off_template_v1, X64Rel32), 13 bytes, 2-aligned:
 *   +0 EB 0B | 66 90   activation word (off: jump over; on: 2-byte NOP)
 *   +2 E8 rel32        CALL __simple_xray_trampoline_v1 (R_X86_64_PLT32)
 *   +7 EB 04           jump over the id (the CALL returns here)
 *   +9 imm32           site id
 * The sled saves NOTHING: on entry [rsp] = sled + 7 and every other register,
 * RFLAGS and the SSE state must come back exactly as found. A CALL is safe at
 * both sites: at the entry sled the callee owns no stack below rsp yet, and
 * the exit sled sits after the epilogue, where rsp points at the return
 * address and any red-zone data below it is dead.
 *
 * BOUNDED REMEDY (same class as the merged Windows x64 experiment
 * test/integration/xray/trampoline_x64_bounded.S, PR #5962), SysV variant:
 * saved here are RFLAGS (pushfq first, before any flag-writing instruction),
 * the SysV caller-saved GPRs rax rcx rdx rsi rdi r8-r11, xmm0-xmm15 (all of
 * them: SysV has no callee-saved XMM) and MXCSR. DF is cleared for the
 * handler and restored with RFLAGS. The stack is realigned explicitly
 * (`and rsp, -16`) instead of trusting the sled site's parity. Differences
 * from the Windows file: rsi/rdi are caller-saved on SysV, there is no 32-byte
 * shadow space, there is no kind push (the kind is in the map row), and the
 * vector save is SSE `movdqu xmm` (no AVX requirement). NOT preserved: the
 * upper halves of ymm/zmm, AVX-512 opmask, x87/MMX state, AMX/APX state. The
 * handler is built with -mgeneral-regs-only so it cannot touch any of them;
 * production must reject a live-state profile needing more, or provide a
 * separately verified extended-state trampoline.
 *
 * Quiescent only (design C.2, Q6): the patcher stores the aligned 2-byte
 * activation word with one store while no thread executes the sled's page;
 * cross-modifying-code rules for live patching are not qualified here.
 */
#include <stdint.h>

#if defined(__linux__) && defined(__x86_64__)
#define SIMPLE_XRAY_NATIVE_SUPPORTED 1
#endif

/* x86-64 SysV sled shape (xray_native_map_format_v1.spl). */
#define XMAP_ISA 1
#define XMAP_ABI 2
#define XMAP_SLED_BYTES 13
#define XMAP_SLED_ALIGN 2
#define XMAP_OFF_WORD 0x0BEBu /* EB 0B  jmp +11 */
#define XMAP_ON_WORD 0x9066u  /* 66 90  2-byte nop */
/* The CALL at +2 returns to +7. */
#define XMAP_RETURN_TO_SLED 7

#ifdef SIMPLE_XRAY_NATIVE_SUPPORTED

extern void __simple_xray_trampoline_v1(void);

/* Registration leaf: activation word OFF or ON, `E8 rel32` at +2 reaching
 * THIS runtime's trampoline, `EB 04` at +7, imm32 at +9 == the row's id. */
static int xray_isa_sled_calls_trampoline(uintptr_t sled, uint32_t site_id) {
    const volatile uint8_t *bytes = (const volatile uint8_t *)sled;
    uint32_t word = __atomic_load_n((const uint16_t *)sled, __ATOMIC_RELAXED);
    if (word != XMAP_OFF_WORD && word != XMAP_ON_WORD) return 0;
    if (bytes[2] != 0xE8 || bytes[7] != 0xEB || bytes[8] != 0x04) return 0;
    uint32_t rel = (uint32_t)bytes[3] | ((uint32_t)bytes[4] << 8) | ((uint32_t)bytes[5] << 16) |
                   ((uint32_t)bytes[6] << 24);
    uint32_t id = (uint32_t)bytes[9] | ((uint32_t)bytes[10] << 8) | ((uint32_t)bytes[11] << 16) |
                  ((uint32_t)bytes[12] << 24);
    if (id != site_id) return 0;
    return sled + 7 + (uintptr_t)(int64_t)(int32_t)rel == (uintptr_t)&__simple_xray_trampoline_v1;
}

/* Frame below the realigned rsp: xmm0-15 at 0..255, MXCSR at 256, 12 bytes
 * pad (272 total, 16-aligned). Above it, from rbp down: rbp+16 = sled return
 * (sled + 7), rbp+8 = RFLAGS, rbp+0 = caller rbp, rbp-8..-72 = rax rcx rdx
 * rsi rdi r8 r9 r10 r11. Handler args: edi = site id (imm32 at sled+9, i.e.
 * [return + 2], zero-extended), rsi = sled return address. */
__asm__(
    ".text\n"
    ".p2align 4\n"
    ".globl __simple_xray_trampoline_v1\n"
    ".protected __simple_xray_trampoline_v1\n"
    ".type __simple_xray_trampoline_v1, @function\n"
    "__simple_xray_trampoline_v1:\n"
    "    pushfq\n"
    "    pushq %rbp\n"
    "    movq %rsp, %rbp\n"
    "    cld\n"
    "    pushq %rax\n"
    "    pushq %rcx\n"
    "    pushq %rdx\n"
    "    pushq %rsi\n"
    "    pushq %rdi\n"
    "    pushq %r8\n"
    "    pushq %r9\n"
    "    pushq %r10\n"
    "    pushq %r11\n"
    "    andq $-16, %rsp\n"
    "    subq $272, %rsp\n"
    "    movdqu %xmm0, 0(%rsp)\n"
    "    movdqu %xmm1, 16(%rsp)\n"
    "    movdqu %xmm2, 32(%rsp)\n"
    "    movdqu %xmm3, 48(%rsp)\n"
    "    movdqu %xmm4, 64(%rsp)\n"
    "    movdqu %xmm5, 80(%rsp)\n"
    "    movdqu %xmm6, 96(%rsp)\n"
    "    movdqu %xmm7, 112(%rsp)\n"
    "    movdqu %xmm8, 128(%rsp)\n"
    "    movdqu %xmm9, 144(%rsp)\n"
    "    movdqu %xmm10, 160(%rsp)\n"
    "    movdqu %xmm11, 176(%rsp)\n"
    "    movdqu %xmm12, 192(%rsp)\n"
    "    movdqu %xmm13, 208(%rsp)\n"
    "    movdqu %xmm14, 224(%rsp)\n"
    "    movdqu %xmm15, 240(%rsp)\n"
    "    stmxcsr 256(%rsp)\n"
    "    movq 16(%rbp), %rsi\n"
    "    movl 2(%rsi), %edi\n"
    "    call simple_xray_native_handler_v1\n"
    "    ldmxcsr 256(%rsp)\n"
    "    movdqu 0(%rsp), %xmm0\n"
    "    movdqu 16(%rsp), %xmm1\n"
    "    movdqu 32(%rsp), %xmm2\n"
    "    movdqu 48(%rsp), %xmm3\n"
    "    movdqu 64(%rsp), %xmm4\n"
    "    movdqu 80(%rsp), %xmm5\n"
    "    movdqu 96(%rsp), %xmm6\n"
    "    movdqu 112(%rsp), %xmm7\n"
    "    movdqu 128(%rsp), %xmm8\n"
    "    movdqu 144(%rsp), %xmm9\n"
    "    movdqu 160(%rsp), %xmm10\n"
    "    movdqu 176(%rsp), %xmm11\n"
    "    movdqu 192(%rsp), %xmm12\n"
    "    movdqu 208(%rsp), %xmm13\n"
    "    movdqu 224(%rsp), %xmm14\n"
    "    movdqu 240(%rsp), %xmm15\n"
    "    leaq -72(%rbp), %rsp\n"
    "    popq %r11\n"
    "    popq %r10\n"
    "    popq %r9\n"
    "    popq %r8\n"
    "    popq %rdi\n"
    "    popq %rsi\n"
    "    popq %rdx\n"
    "    popq %rcx\n"
    "    popq %rax\n"
    "    popq %rbp\n"
    "    popfq\n"
    "    ret\n"
    ".size __simple_xray_trampoline_v1, .-__simple_xray_trampoline_v1\n");

#endif /* SIMPLE_XRAY_NATIVE_SUPPORTED */

#include "xray_native_registry_v1.h"

SIMPLE_XRAY_NATIVE_ENTRY_POINTS_V1
