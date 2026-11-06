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
 *  2. The hot-path handler: resolves (return address, site id) to a
 *     registered module's map row, then the shared channel producer
 *     (xray_channel_producer_v1.h, Simple twin trace_native_channel_record_words_v1).
 *  3. Module registration + channel publication, called by the Simple control
 *     plane (src/lib/nogc_sync_mut/trace/xray_native_module_v1.spl). The map
 *     itself is found and validated in Simple; registration re-checks its
 *     header and every sled row before any hook can read it (fail closed).
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
#include <stddef.h>
#include <stdint.h>

#include "xray_channel_producer_v1.h"

#if defined(__linux__) && defined(__aarch64__)
#define SIMPLE_XRAY_NATIVE_SUPPORTED 1
#endif

#define SIMPLE_XRAY_API __attribute__((visibility("protected"), used))

/* .simple_xray_map format v1 (src/lib/common/trace/xray_native_map_format_v1.spl). */
#define XMAP_HEADER_BYTES 48
#define XMAP_FN_ROW_BYTES 16
#define XMAP_SITE_ROW_BYTES 24
#define XMAP_TEXT_BASE_OFFSET 36
#define XMAP_SLED_BYTES 32
#define XMAP_OFF_WORD 0x14000008u /* B +32 */
#define XMAP_ON_WORD 0xD503201Fu  /* NOP */
#define XMAP_MAX_ROWS 1048576u
#define SIMPLE_XRAY_NATIVE_MAX_MODULES 64

struct simple_xray_native_module {
    uintptr_t text_lo;      /* first sled */
    uintptr_t text_hi;      /* one past the last sled */
    uintptr_t text_base;    /* relocated .text base of the module's object */
    const uint8_t *sites;   /* site rows inside the resident map */
    uint32_t site_count;
    uint64_t module_instance;
    int64_t *arena;         /* published channel, NULL until install */
};

static struct simple_xray_native_module g_modules[SIMPLE_XRAY_NATIVE_MAX_MODULES];
static uint32_t g_module_count; /* release-published; entries are immutable after */
/* Per runtime instance (each --xray module links its own copy): sequence
 * numbers are monotonic per module, and an arena is published to exactly one
 * module (install keys it by module instance). */
static uint64_t g_sequence;

static inline uint32_t xmap_u16(const uint8_t *p) { return (uint32_t)p[0] | ((uint32_t)p[1] << 8); }
static inline uint32_t xmap_u32(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}
static inline uint64_t xmap_u64(const uint8_t *p) {
    return (uint64_t)xmap_u32(p) | ((uint64_t)xmap_u32(p + 4) << 32);
}

#ifdef SIMPLE_XRAY_NATIVE_SUPPORTED

extern void __simple_xray_trampoline_v1(void);

/* Hot path. Never blocks, allocates or calls out. A return address outside
 * every registered module, an out-of-range id, or a row whose sled is not the
 * caller is ignored: such a call is not one of ours. */
__attribute__((used, noinline)) static void simple_xray_native_handler_v1(uint64_t site_id,
                                                                         uintptr_t sled_return) {
    uint32_t count = __atomic_load_n(&g_module_count, __ATOMIC_ACQUIRE);
    uintptr_t sled = sled_return - 24;
    for (uint32_t index = 0; index < count; index++) {
        const struct simple_xray_native_module *module = &g_modules[index];
        if (sled < module->text_lo || sled >= module->text_hi) continue;
        int64_t *base = __atomic_load_n(&module->arena, __ATOMIC_ACQUIRE);
        if (base == NULL || site_id < 1 || site_id > module->site_count) return;
        const uint8_t *row = module->sites + (site_id - 1) * XMAP_SITE_ROW_BYTES;
        if (module->text_base + xmap_u64(row) != sled) return;
        uint64_t function_id = xmap_u32(row + 8);
        uint64_t kind = row[12]; /* 1 entry, 2 exit, 3 tail exit == event codes */
        simple_xray_channel_produce_v1(base, kind, module->module_instance,
                                       function_id | (site_id << 32), &g_sequence);
        return;
    }
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

/* Register a resident, already-validated `.simple_xray_map` (control plane
 * only, serialized by its single owner; never callable from a hook). Every
 * row is re-checked: aligned sled, known kind, 32-byte AArch64 sled with the
 * V1 off/on words, and the sled's first word currently OFF or ON. Returns the
 * 1-based module slot, 0 on any rejection (nothing published). A map already
 * registered returns its slot (idempotent); an overlapping one is rejected. */
SIMPLE_XRAY_API int64_t simple_xray_native_register_module_v1(int64_t map_address,
                                                              int64_t module_instance) {
    if (map_address <= 0 || module_instance <= 0) return 0;
    const uint8_t *map = (const uint8_t *)(uintptr_t)map_address;
    if (map[0] != 'S' || map[1] != 'X' || map[2] != 'R' || map[3] != 'M') return 0;
    if (xmap_u16(map + 4) != 1 || xmap_u16(map + 6) != 2 || xmap_u16(map + 8) != 1 ||
        xmap_u16(map + 10) != 1)
        return 0; /* format 1, isa aarch64, abi simple-aarch64, sled abi 1 */
    uint32_t fn_count = xmap_u32(map + 12);
    uint32_t site_count = xmap_u32(map + 16);
    if (fn_count == 0 || site_count == 0 || fn_count > XMAP_MAX_ROWS || site_count > XMAP_MAX_ROWS)
        return 0;
    /* text_base: PREL64 resolved by the static linker -> field address + value. */
    uintptr_t field = (uintptr_t)map_address + XMAP_TEXT_BASE_OFFSET;
    uintptr_t text_base = field + (uintptr_t)(int64_t)xmap_u64(map + XMAP_TEXT_BASE_OFFSET);
    const uint8_t *sites = map + XMAP_HEADER_BYTES + (size_t)fn_count * XMAP_FN_ROW_BYTES;
    uintptr_t lo = UINTPTR_MAX, hi = 0;
    for (uint32_t index = 0; index < site_count; index++) {
        const uint8_t *row = sites + (size_t)index * XMAP_SITE_ROW_BYTES;
        uintptr_t sled = text_base + (uintptr_t)xmap_u64(row);
        uint32_t kind = row[12];
        if ((sled & 3u) != 0 || kind < 1 || kind > 3 || row[13] != XMAP_SLED_BYTES ||
            xmap_u32(row + 16) != XMAP_OFF_WORD || xmap_u32(row + 20) != XMAP_ON_WORD)
            return 0;
        uint32_t word = __atomic_load_n((const uint32_t *)sled, __ATOMIC_RELAXED);
        if (word != XMAP_OFF_WORD && word != XMAP_ON_WORD) return 0;
        /* The sled must call THIS runtime instance: a map registered with
         * another module's runtime would patch ON and record nowhere. */
        uint32_t bl = __atomic_load_n((const uint32_t *)(sled + 20), __ATOMIC_RELAXED);
        if ((bl & 0xFC000000u) != 0x94000000u) return 0;
        int64_t imm = (int64_t)(bl & 0x3FFFFFFu);
        if (imm >= 0x2000000) imm -= 0x4000000;
        if (sled + 20 + (uintptr_t)(imm * 4) != (uintptr_t)&__simple_xray_trampoline_v1) return 0;
        if (sled < lo) lo = sled;
        if (sled + XMAP_SLED_BYTES > hi) hi = sled + XMAP_SLED_BYTES;
    }
    uint32_t count = __atomic_load_n(&g_module_count, __ATOMIC_ACQUIRE);
    for (uint32_t index = 0; index < count; index++) {
        if (g_modules[index].sites == sites) {
            if (g_modules[index].module_instance != (uint64_t)module_instance) return 0;
            return (int64_t)index + 1;
        }
        if (lo < g_modules[index].text_hi && g_modules[index].text_lo < hi) return 0;
    }
    if (count >= SIMPLE_XRAY_NATIVE_MAX_MODULES) return 0;
    g_modules[count] = (struct simple_xray_native_module){
        .text_lo = lo, .text_hi = hi, .text_base = text_base, .sites = sites,
        .site_count = site_count, .module_instance = (uint64_t)module_instance, .arena = NULL};
    __atomic_store_n(&g_module_count, count + 1, __ATOMIC_RELEASE);
    return (int64_t)count + 1;
}

/* Publish an initialized, open, resident channel arena for a registered
 * module (design C.2 step 3: before any selected sled can reach it). Returns
 * 1 on success, 0 when the module is unknown or the arena does not describe
 * the stated generation / an open, empty-gate channel. The arena stays
 * resident until process exit; a replaced arena is never freed here. */
SIMPLE_XRAY_API int64_t simple_xray_native_install_v1(int64_t module_instance, int64_t arena,
                                                      int64_t generation) {
    if (module_instance <= 0 || arena <= 0 || (arena % 8) != 0 || generation <= 0) return 0;
    int64_t *base = (int64_t *)(intptr_t)arena;
    int64_t capacity = base[CH_CAPACITY];
    if (capacity <= 0 || capacity > CH_MAX_RECORDS) return 0;
    if (base[CH_GENERATION] != generation || base[CH_CONTEXT] <= 0) return 0;
    if (base[CH_ARENA_BYTES] != (CH_HEADER_WORDS + capacity * CH_RECORD_WORDS) * 8) return 0;
    if (__atomic_load_n(&base[CH_GATE], __ATOMIC_SEQ_CST) != 0) return 0;
    uint32_t count = __atomic_load_n(&g_module_count, __ATOMIC_ACQUIRE);
    for (uint32_t index = 0; index < count; index++) {
        if (g_modules[index].module_instance == (uint64_t)module_instance) {
            __atomic_store_n(&g_modules[index].arena, base, __ATOMIC_RELEASE);
            return 1;
        }
    }
    return 0;
}

#else /* unsupported target: no sleds, nothing can be registered or installed */

SIMPLE_XRAY_API int64_t simple_xray_native_register_module_v1(int64_t map_address,
                                                              int64_t module_instance) {
    (void)map_address;
    (void)module_instance;
    (void)g_modules;
    (void)g_module_count;
    (void)g_sequence;
    return 0;
}

SIMPLE_XRAY_API int64_t simple_xray_native_install_v1(int64_t module_instance, int64_t arena,
                                                      int64_t generation) {
    (void)module_instance;
    (void)arena;
    (void)generation;
    return 0;
}

#endif
