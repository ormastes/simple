/*
 * xray_native_runtime_win64.c -- stage-3 resident XRay runtime for the
 * pure-Simple native backend, Windows x64 (Microsoft ABI) profile.
 *
 * Plan: doc/03_plan/compiler/aspect_dynload/simple_xray_staged_implementation_plan_2026-11-03.md
 * section 9 (Stage 3, Windows x64) and 10.4; same 13-byte X64Rel32 sled as the
 * SysV profile (xray_native_runtime_x86_64.c), different trampoline, unwind
 * data and map ABI profile (3). Linked only into `--xray` Windows x64 builds;
 * never part of the core runtime archive.
 *
 *  1. `__simple_xray_trampoline_win64_v1` (asm, with .seh_* directives so the
 *     assembler emits its .pdata RUNTIME_FUNCTION and .xdata UNWIND_INFO):
 *     the target of every sled's CALL. Simple twin + unwind encoder:
 *     src/lib/common/trace/xray_native_trampoline_win64_v1.spl, compared byte
 *     for byte by scripts/check/check-xray-native-win64-objects.shs.
 *  2. The registration sled leaf (same contract as SysV).
 *  3. The registry/handler (xray_native_registry_v1.h) with the Windows
 *     text_base rule: the map header's text_base field holds the .text RVA
 *     (IMAGE_REL_AMD64_ADDR32NB), resolved against this module's __ImageBase.
 *
 * Windows x64 bounded AVX profile (plan 3.3, the PR #5962 remedy): saves
 * rbp, the volatile GPRs rax rcx rdx r8-r11, ymm0-15 in full (their upper
 * halves are volatile for every register), MXCSR and RFLAGS; 32 bytes of
 * shadow space; DF clear and rsp 16-aligned at the handler CALL; canonical
 * epilog (lea rsp,[rbp]; pops; ret) so the unwinder can recognise it.
 * Handler args: ecx = site id (imm32 at [return + 2]), rdx = sled return.
 * The host must refuse install on a CPU / OS without AVX state.
 *
 * Patching: the Simple control plane flips the aligned 16-bit activation word
 * through rt_mprotect, which on Windows is VirtualProtect followed by
 * FlushInstructionCache (src/runtime/platform/platform_win.h); quiescent
 * only, exactly as on Linux.
 */
#include <stdint.h>

#if defined(_WIN32) && defined(__x86_64__)
#define SIMPLE_XRAY_NATIVE_SUPPORTED 1
#define SIMPLE_XRAY_API __declspec(dllexport)
/* Linker-defined base of the image this TU is linked into (link.exe / lld-link). */
extern const uint8_t __ImageBase[];
#define XMAP_TEXT_BASE(field_address, value) ((uintptr_t)__ImageBase + (uintptr_t)(uint32_t)(value))
#endif

/* x86-64 sled shape, Windows x64 ABI profile (xray_native_map_format_v1.spl). */
#define XMAP_ISA 1
#define XMAP_ABI 3
#define XMAP_SLED_BYTES 13
#define XMAP_SLED_ALIGN 2
#define XMAP_OFF_WORD 0x0BEBu /* EB 0B  jmp +11 */
#define XMAP_ON_WORD 0x9066u  /* 66 90  2-byte nop */
/* The CALL at +2 returns to +7. */
#define XMAP_RETURN_TO_SLED 7

#ifdef SIMPLE_XRAY_NATIVE_SUPPORTED

/* The registry header calls the trampoline __simple_xray_trampoline_v1. */
#define __simple_xray_trampoline_v1 __simple_xray_trampoline_win64_v1
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

/* Frame (0x238 bytes below rbp-after-pushes): [rsp+0x00..0x20) shadow space,
 * ymm0-15 at +0x20, MXCSR at +0x220, RFLAGS at +0x228. rbp+0x40 = sled return. */
__asm__(
    ".text\n"
    ".globl __simple_xray_trampoline_win64_v1\n"
    ".p2align 4\n"
    ".def __simple_xray_trampoline_win64_v1; .scl 2; .type 32; .endef\n"
    "__simple_xray_trampoline_win64_v1:\n"
    ".seh_proc __simple_xray_trampoline_win64_v1\n"
    "    pushq %rbp\n"
    "    .seh_pushreg %rbp\n"
    "    pushq %rax\n"
    "    .seh_pushreg %rax\n"
    "    pushq %rcx\n"
    "    .seh_pushreg %rcx\n"
    "    pushq %rdx\n"
    "    .seh_pushreg %rdx\n"
    "    pushq %r8\n"
    "    .seh_pushreg %r8\n"
    "    pushq %r9\n"
    "    .seh_pushreg %r9\n"
    "    pushq %r10\n"
    "    .seh_pushreg %r10\n"
    "    pushq %r11\n"
    "    .seh_pushreg %r11\n"
    "    movq %rsp, %rbp\n"
    "    .seh_setframe %rbp, 0\n"
    "    subq $0x238, %rsp\n"
    "    .seh_stackalloc 0x238\n"
    "    .seh_endprologue\n"
    "    pushfq\n"
    "    popq 0x228(%rsp)\n"
    "    cld\n"
    "    vmovdqu %ymm0, 0x20(%rsp)\n"
    "    vmovdqu %ymm1, 0x40(%rsp)\n"
    "    vmovdqu %ymm2, 0x60(%rsp)\n"
    "    vmovdqu %ymm3, 0x80(%rsp)\n"
    "    vmovdqu %ymm4, 0xa0(%rsp)\n"
    "    vmovdqu %ymm5, 0xc0(%rsp)\n"
    "    vmovdqu %ymm6, 0xe0(%rsp)\n"
    "    vmovdqu %ymm7, 0x100(%rsp)\n"
    "    vmovdqu %ymm8, 0x120(%rsp)\n"
    "    vmovdqu %ymm9, 0x140(%rsp)\n"
    "    vmovdqu %ymm10, 0x160(%rsp)\n"
    "    vmovdqu %ymm11, 0x180(%rsp)\n"
    "    vmovdqu %ymm12, 0x1a0(%rsp)\n"
    "    vmovdqu %ymm13, 0x1c0(%rsp)\n"
    "    vmovdqu %ymm14, 0x1e0(%rsp)\n"
    "    vmovdqu %ymm15, 0x200(%rsp)\n"
    "    stmxcsr 0x220(%rsp)\n"
    "    movq 0x40(%rbp), %rdx\n"
    "    movl 2(%rdx), %ecx\n"
    "    callq simple_xray_native_handler_v1\n"
    "    ldmxcsr 0x220(%rsp)\n"
    "    vmovdqu 0x20(%rsp), %ymm0\n"
    "    vmovdqu 0x40(%rsp), %ymm1\n"
    "    vmovdqu 0x60(%rsp), %ymm2\n"
    "    vmovdqu 0x80(%rsp), %ymm3\n"
    "    vmovdqu 0xa0(%rsp), %ymm4\n"
    "    vmovdqu 0xc0(%rsp), %ymm5\n"
    "    vmovdqu 0xe0(%rsp), %ymm6\n"
    "    vmovdqu 0x100(%rsp), %ymm7\n"
    "    vmovdqu 0x120(%rsp), %ymm8\n"
    "    vmovdqu 0x140(%rsp), %ymm9\n"
    "    vmovdqu 0x160(%rsp), %ymm10\n"
    "    vmovdqu 0x180(%rsp), %ymm11\n"
    "    vmovdqu 0x1a0(%rsp), %ymm12\n"
    "    vmovdqu 0x1c0(%rsp), %ymm13\n"
    "    vmovdqu 0x1e0(%rsp), %ymm14\n"
    "    vmovdqu 0x200(%rsp), %ymm15\n"
    "    pushq 0x228(%rsp)\n"
    "    popfq\n"
    "    leaq 0(%rbp), %rsp\n"
    "    popq %r11\n"
    "    popq %r10\n"
    "    popq %r9\n"
    "    popq %r8\n"
    "    popq %rdx\n"
    "    popq %rcx\n"
    "    popq %rax\n"
    "    popq %rbp\n"
    "    retq\n"
    "    .seh_endproc\n"
);

#endif /* SIMPLE_XRAY_NATIVE_SUPPORTED */

#include "xray_native_registry_v1.h"

SIMPLE_XRAY_NATIVE_ENTRY_POINTS_V1
