/*
 * xray_native_registry_v1.h -- the ISA-neutral half of the stage-2 resident
 * XRay runtime (module registry, hot-path handler, channel installer).
 *
 * Design: doc/04_architecture/compiler/xray/xray_compiler_structural_change_2026-11-06.md
 * sections A.5, C.2-C.5. Included ONLY by the per-ISA resident runtime TUs
 * (xray_native_runtime_aarch64.c, PR5b; xray_native_runtime_x86_64.c, PR6),
 * which own the irreplaceable trampoline asm and the ISA sled shape. Exactly
 * one of them is linked into an `--xray` native build
 * (src/compiler/80.driver/driver_xray_link.spl); neither is part of the core
 * runtime archive, so an OFF build is unchanged.
 *
 * The including TU defines, before including this header:
 *   SIMPLE_XRAY_NATIVE_SUPPORTED  when compiled for its own Linux target
 *   XMAP_ISA, XMAP_ABI            .simple_xray_map header isa / abi_profile
 *   XMAP_SLED_BYTES, XMAP_SLED_ALIGN, XMAP_OFF_WORD, XMAP_ON_WORD
 *                                 the site-row shape (len, align, words)
 *   XMAP_RETURN_TO_SLED           bytes from the trampoline's sled return
 *                                 address back to the sled start
 * and, when supported, the ISA leaf
 *   static int xray_isa_sled_calls_trampoline(uintptr_t sled, uint32_t site_id);
 * which checks the sled's CURRENT activation word is OFF or ON and that it
 * calls THIS runtime instance's `__simple_xray_trampoline_v1`.
 *
 * No external-linkage definition lives here (ODR): the bodies are static
 * inline `*_impl_v1`, and each ISA TU defines the two exported, dlsym-able
 * entry points as one-line wrappers below the include
 * (SIMPLE_XRAY_NATIVE_ENTRY_POINTS_V1). The handler and the registry state
 * are internal-linkage and exist once per TU, i.e. once per --xray module.
 *
 * Hot-path rules (plan section 7): no lock, no allocation, no libc call, no
 * syscall. Not `rt_*`. Map format: src/lib/common/trace/xray_native_map_format_v1.spl.
 */
#ifndef SIMPLE_XRAY_NATIVE_REGISTRY_V1_H
#define SIMPLE_XRAY_NATIVE_REGISTRY_V1_H

#include <stddef.h>
#include <stdint.h>

#include "xray_channel_producer_v1.h"

#define SIMPLE_XRAY_API __attribute__((visibility("protected"), used))

/* .simple_xray_map format v1 (src/lib/common/trace/xray_native_map_format_v1.spl). */
#define XMAP_HEADER_BYTES 48
#define XMAP_FN_ROW_BYTES 16
#define XMAP_SITE_ROW_BYTES 24
#define XMAP_TEXT_BASE_OFFSET 36
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

/* Hot path, called only by the trampoline. Never blocks, allocates or calls
 * out. A return address outside every registered module, an out-of-range id,
 * or a row whose sled is not the caller is ignored: such a call is not ours. */
__attribute__((used, noinline)) static void simple_xray_native_handler_v1(uint64_t site_id,
                                                                         uintptr_t sled_return) {
    uint32_t count = __atomic_load_n(&g_module_count, __ATOMIC_ACQUIRE);
    uintptr_t sled = sled_return - XMAP_RETURN_TO_SLED;
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

/* Register a resident, already-validated `.simple_xray_map` (control plane
 * only, serialized by its single owner; never callable from a hook). Every
 * row is re-checked: aligned sled, known kind, this ISA's sled length and
 * off/on words, the sled's activation word currently OFF or ON, and its call
 * bound to this runtime's trampoline. Returns the 1-based module slot, 0 on
 * any rejection (nothing published). A map already registered returns its
 * slot (idempotent); an overlapping one is rejected. */
static inline int64_t simple_xray_native_register_module_impl_v1(int64_t map_address,
                                                                  int64_t module_instance) {
    if (map_address <= 0 || module_instance <= 0) return 0;
    const uint8_t *map = (const uint8_t *)(uintptr_t)map_address;
    if (map[0] != 'S' || map[1] != 'X' || map[2] != 'R' || map[3] != 'M') return 0;
    if (xmap_u16(map + 4) != 1 || xmap_u16(map + 6) != XMAP_ISA || xmap_u16(map + 8) != XMAP_ABI ||
        xmap_u16(map + 10) != 1)
        return 0; /* format 1, this ISA, this ABI profile, sled abi 1 */
    uint32_t fn_count = xmap_u32(map + 12);
    uint32_t site_count = xmap_u32(map + 16);
    if (fn_count == 0 || site_count == 0 || fn_count > XMAP_MAX_ROWS || site_count > XMAP_MAX_ROWS)
        return 0;
    /* text_base: PC-relative 64-bit relocation resolved by the static linker
     * -> field address + value. */
    uintptr_t field = (uintptr_t)map_address + XMAP_TEXT_BASE_OFFSET;
    uintptr_t text_base = field + (uintptr_t)(int64_t)xmap_u64(map + XMAP_TEXT_BASE_OFFSET);
    const uint8_t *sites = map + XMAP_HEADER_BYTES + (size_t)fn_count * XMAP_FN_ROW_BYTES;
    uintptr_t lo = UINTPTR_MAX, hi = 0;
    for (uint32_t index = 0; index < site_count; index++) {
        const uint8_t *row = sites + (size_t)index * XMAP_SITE_ROW_BYTES;
        uintptr_t sled = text_base + (uintptr_t)xmap_u64(row);
        uint32_t kind = row[12];
        if ((sled & (XMAP_SLED_ALIGN - 1u)) != 0 || kind < 1 || kind > 3 ||
            row[13] != XMAP_SLED_BYTES || row[14] != XMAP_SLED_ALIGN ||
            xmap_u32(row + 16) != XMAP_OFF_WORD || xmap_u32(row + 20) != XMAP_ON_WORD)
            return 0;
        /* The sled must call THIS runtime instance: a map registered with
         * another module's runtime would patch ON and record nowhere. */
        if (!xray_isa_sled_calls_trampoline(sled, index + 1)) return 0;
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
static inline int64_t simple_xray_native_install_impl_v1(int64_t module_instance, int64_t arena,
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

static inline int64_t simple_xray_native_register_module_impl_v1(int64_t map_address,
                                                                  int64_t module_instance) {
    (void)map_address;
    (void)module_instance;
    (void)g_modules;
    (void)g_module_count;
    (void)g_sequence;
    return 0;
}

static inline int64_t simple_xray_native_install_impl_v1(int64_t module_instance, int64_t arena,
                                                          int64_t generation) {
    (void)module_instance;
    (void)arena;
    (void)generation;
    return 0;
}

#endif /* SIMPLE_XRAY_NATIVE_SUPPORTED */

/* The exported entry points (declarations; each including TU defines them
 * with SIMPLE_XRAY_NATIVE_ENTRY_POINTS_V1 exactly once). */
SIMPLE_XRAY_API int64_t simple_xray_native_register_module_v1(int64_t map_address,
                                                              int64_t module_instance);
SIMPLE_XRAY_API int64_t simple_xray_native_install_v1(int64_t module_instance, int64_t arena,
                                                      int64_t generation);

#define SIMPLE_XRAY_NATIVE_ENTRY_POINTS_V1                                                       \
    SIMPLE_XRAY_API int64_t simple_xray_native_register_module_v1(int64_t map_address,           \
                                                                  int64_t module_instance) {     \
        return simple_xray_native_register_module_impl_v1(map_address, module_instance);         \
    }                                                                                            \
    SIMPLE_XRAY_API int64_t simple_xray_native_install_v1(int64_t module_instance, int64_t arena, \
                                                          int64_t generation) {                  \
        return simple_xray_native_install_impl_v1(module_instance, arena, generation);           \
    }

#endif /* SIMPLE_XRAY_NATIVE_REGISTRY_V1_H */
