/*
 * xray_llvm_runtime_darwin.c -- Darwin Mach-O LLVM XRay flag-guard runtime
 * and stage-1 Simple trace adapter (aarch64-apple-darwin / x86_64-apple-darwin).
 *
 * On Apple Silicon macOS, ld64 emits ad-hoc linker-signed binaries with
 * __TEXT maxprot = r-x and packs __TEXT,__stubs onto the trailing 16 KiB page
 * of __TEXT,__text. Modifying __TEXT in place violates W^X / code-signing
 * invariants without special JIT/debugger entitlements.
 *
 * MirToLlvm therefore lowers Darwin `--xray` through per-function 32-byte
 * writable activation slots in (__DATA,__xray_fn_slots) (`xray_flag_guard`).
 * When dormant (`enabled == 0`), each instrumented function executes a single
 * predicted-not-taken branch with zero .text mutation. When patched
 * (`enabled != 0`), entry and exit edges invoke `__simple_darwin_xray_edge_v1`.
 *
 * This TU provides:
 *   1. Dynamic O(F) discovery of (__DATA,__xray_fn_slots) across loaded 64-bit
 *      Mach-O images (zero fixed-size table truncation; fail-closed on OOM).
 *   2. The standard XRay C control surface (__xray_set_handler,
 *      __xray_remove_handler, __xray_max_function_id, __xray_function_address,
 *      __xray_function_name_v1, __xray_patch_function, __xray_unpatch_function,
 *      __xray_patch, __xray_unpatch).
 *   3. The Simple stage-1 adapter leaves (simple_xray_llvm_max_function_id,
 *      simple_xray_llvm_install, simple_xray_llvm_patch_function,
 *      simple_xray_llvm_unpatch_function) over xray_channel_producer_v1.h.
 *   4. Built-in C ABI diagnostic counter probes (simple_xray_darwin_*_v1) for
 *      in-process runtime verification.
 *
 * Linked ONLY into `--xray` Darwin LLVM builds (driver_xray_llvm_link.spl);
 * never part of the core runtime archive, so OFF/release builds are unchanged.
 */
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

#include "xray_channel_producer_v1.h"

#define SIMPLE_XRAY_STATUS_INVALID_ID (-1)

enum XRayEntryType {
    ENTRY = 0,
    EXIT = 1,
    TAIL = 2,
    LOG_ARGS_ENTRY = 3,
    CUSTOM_EVENT = 4,
    TYPED_EVENT = 5,
};

enum XRayPatchingStatus {
    NOT_INITIALIZED = 0,
    SUCCESS = 1,
    ONGOING = 2,
    FAILED = 3,
};

#if defined(__APPLE__) && (defined(__aarch64__) || defined(__x86_64__))
#define SIMPLE_XRAY_DARWIN_LLVM_SUPPORTED 1
#endif

#ifdef SIMPLE_XRAY_DARWIN_LLVM_SUPPORTED

#include <mach-o/dyld.h>
#include <mach-o/getsect.h>
#include <mach-o/loader.h>
#include <pthread.h>

#define DARWIN_XRAY_EXPORT __attribute__((visibility("default"), used))
#define XRAY_MAIN_OBJECT_MAX_ID ((1 << 24) - 1)
#define DARWIN_XRAY_SLOT_MAGIC_V1 0x5358525944534c31ULL /* "SXRYDSL1" */

typedef struct SimpleDarwinXraySlotV1 {
    uint64_t magic;
    const void *func_addr;
    const char *func_name;
    int32_t func_id;
    int32_t enabled;
} SimpleDarwinXraySlotV1;

_Static_assert(sizeof(SimpleDarwinXraySlotV1) == 32,
               "SimpleDarwinXraySlotV1 must match 32-byte LLVM IR slot layout");

typedef void (*darwin_xray_handler_fn)(int32_t, enum XRayEntryType);

static pthread_mutex_t g_darwin_index_mutex = PTHREAD_MUTEX_INITIALIZER;
static SimpleDarwinXraySlotV1 **g_darwin_slots;
static uint32_t g_darwin_slot_count;
static uint32_t g_darwin_index_state; /* 0 = uninit, 1 = ready, 2 = failed */
static darwin_xray_handler_fn g_darwin_user_handler;
static _Thread_local uint32_t g_darwin_in_handler;

static int64_t *g_simple_xray_arena;
static uint64_t g_simple_xray_module_instance;
static uint64_t g_simple_xray_sequence;
static uint64_t g_xray_handler_mode;

static int64_t g_counter_entries;
static int64_t g_counter_exits;
static int64_t g_counter_last_fid;

static size_t darwin_xray_count_section_slots(uint8_t *raw, unsigned long byte_size) {
    size_t count = 0u;
    size_t offset = 0u;
    while (offset + sizeof(SimpleDarwinXraySlotV1) <= (size_t)byte_size) {
        const SimpleDarwinXraySlotV1 *cand =
            (const SimpleDarwinXraySlotV1 *)(const void *)(raw + offset);
        if (cand->magic == DARWIN_XRAY_SLOT_MAGIC_V1) {
            ++count;
            offset += sizeof(SimpleDarwinXraySlotV1);
        } else {
            offset += 8u;
        }
    }
    return count;
}

static size_t darwin_xray_collect_section_slots(uint8_t *raw,
                                                unsigned long byte_size,
                                                SimpleDarwinXraySlotV1 **table,
                                                size_t next_id) {
    size_t offset = 0u;
    while (offset + sizeof(SimpleDarwinXraySlotV1) <= (size_t)byte_size) {
        SimpleDarwinXraySlotV1 *slot =
            (SimpleDarwinXraySlotV1 *)(void *)(raw + offset);
        if (slot->magic == DARWIN_XRAY_SLOT_MAGIC_V1) {
            int32_t fid = (int32_t)next_id;
            __atomic_store_n(&slot->func_id, fid, __ATOMIC_RELEASE);
            table[next_id] = slot;
            ++next_id;
            offset += sizeof(SimpleDarwinXraySlotV1);
        } else {
            offset += 8u;
        }
    }
    return next_id;
}

static int darwin_xray_ensure_indexed(void) {
    uint32_t state = __atomic_load_n(&g_darwin_index_state, __ATOMIC_ACQUIRE);
    if (state == 1u) return 1;
    if (state == 2u) return 0;

    pthread_mutex_lock(&g_darwin_index_mutex);
    state = __atomic_load_n(&g_darwin_index_state, __ATOMIC_RELAXED);
    if (state == 1u) {
        pthread_mutex_unlock(&g_darwin_index_mutex);
        return 1;
    }
    if (state == 2u) {
        pthread_mutex_unlock(&g_darwin_index_mutex);
        return 0;
    }

    uint32_t image_count = _dyld_image_count();
    size_t total_slots = 0u;
    for (uint32_t i = 0u; i < image_count; ++i) {
        const struct mach_header *mh = _dyld_get_image_header(i);
        if (mh == NULL || mh->magic != MH_MAGIC_64) continue;
        unsigned long sec_bytes = 0u;
        uint8_t *raw = getsectiondata((const struct mach_header_64 *)mh,
                                      "__DATA", "__xray_fn_slots", &sec_bytes);
        if (raw == NULL || sec_bytes < sizeof(SimpleDarwinXraySlotV1)) continue;
        size_t img_slots = darwin_xray_count_section_slots(raw, sec_bytes);
        if (img_slots > (size_t)XRAY_MAIN_OBJECT_MAX_ID - total_slots) {
            __atomic_store_n(&g_darwin_index_state, 2u, __ATOMIC_RELEASE);
            pthread_mutex_unlock(&g_darwin_index_mutex);
            return 0;
        }
        total_slots += img_slots;
    }

    SimpleDarwinXraySlotV1 **table = NULL;
    if (total_slots > 0u) {
        table = (SimpleDarwinXraySlotV1 **)calloc(
            total_slots + 1u, sizeof(SimpleDarwinXraySlotV1 *));
        if (table == NULL) {
            __atomic_store_n(&g_darwin_index_state, 2u, __ATOMIC_RELEASE);
            pthread_mutex_unlock(&g_darwin_index_mutex);
            return 0;
        }
        size_t next_id = 1u;
        for (uint32_t i = 0u; i < image_count; ++i) {
            const struct mach_header *mh = _dyld_get_image_header(i);
            if (mh == NULL || mh->magic != MH_MAGIC_64) continue;
            unsigned long sec_bytes = 0u;
            uint8_t *raw = getsectiondata((const struct mach_header_64 *)mh,
                                          "__DATA", "__xray_fn_slots", &sec_bytes);
            if (raw == NULL || sec_bytes < sizeof(SimpleDarwinXraySlotV1)) continue;
            next_id = darwin_xray_collect_section_slots(raw, sec_bytes, table, next_id);
        }
        total_slots = next_id - 1u;
    }

    g_darwin_slots = table;
    g_darwin_slot_count = (uint32_t)total_slots;
    __atomic_store_n(&g_darwin_index_state, 1u, __ATOMIC_RELEASE);
    pthread_mutex_unlock(&g_darwin_index_mutex);
    return 1;
}

DARWIN_XRAY_EXPORT void __simple_darwin_xray_edge_v1(SimpleDarwinXraySlotV1 *slot,
                                                     int32_t raw_kind) {
    if (slot == NULL || g_darwin_in_handler != 0u) return;
    int32_t fid = __atomic_load_n(&slot->func_id, __ATOMIC_ACQUIRE);
    if (fid <= 0) return;
    darwin_xray_handler_fn handler =
        __atomic_load_n(&g_darwin_user_handler, __ATOMIC_ACQUIRE);
    if (handler == NULL) return;
    g_darwin_in_handler = 1u;
    handler(fid, (enum XRayEntryType)raw_kind);
    g_darwin_in_handler = 0u;
}

static void simple_darwin_xray_channel_handler(int32_t fid, enum XRayEntryType type) {
    if (fid <= 0 || fid > XRAY_MAIN_OBJECT_MAX_ID) return;
    uint64_t kind = 0u;
    switch (type) {
        case ENTRY:
        case LOG_ARGS_ENTRY:
            kind = 1u;
            break;
        case EXIT:
            kind = 2u;
            break;
        case TAIL:
            kind = 3u;
            break;
        default:
            return;
    }
    int64_t *base = __atomic_load_n(&g_simple_xray_arena, __ATOMIC_ACQUIRE);
    if (base == NULL) return;
    uint64_t id = (uint64_t)(uint32_t)fid;
    simple_xray_channel_produce_v1(
        base, kind,
        __atomic_load_n(&g_simple_xray_module_instance, __ATOMIC_RELAXED),
        id | (id << 32), &g_simple_xray_sequence);
}

static enum XRayPatchingStatus darwin_xray_patch_impl(int32_t func_id, int enable) {
    if (!darwin_xray_ensure_indexed()) return FAILED;
    if (g_darwin_slot_count == 0u) return NOT_INITIALIZED;
    int32_t flag = enable ? 1 : 0;
    if (func_id != 0) {
        if (func_id < 1 || (uint32_t)func_id > g_darwin_slot_count) {
            return FAILED;
        }
        SimpleDarwinXraySlotV1 *slot = g_darwin_slots[(uint32_t)func_id];
        if (slot == NULL) return FAILED;
        __atomic_store_n(&slot->enabled, flag, __ATOMIC_RELEASE);
        return SUCCESS;
    }
    for (uint32_t fid = 1u; fid <= g_darwin_slot_count; ++fid) {
        SimpleDarwinXraySlotV1 *slot = g_darwin_slots[fid];
        if (slot != NULL) {
            __atomic_store_n(&slot->enabled, flag, __ATOMIC_RELEASE);
        }
    }
    return SUCCESS;
}

DARWIN_XRAY_EXPORT int __xray_set_handler(void (*entry)(int32_t, enum XRayEntryType)) {
    if (!darwin_xray_ensure_indexed()) return 0;
    __atomic_store_n(&g_darwin_user_handler, entry, __ATOMIC_RELEASE);
    return 1;
}

DARWIN_XRAY_EXPORT int __xray_remove_handler(void) {
    __atomic_store_n(&g_darwin_user_handler, (darwin_xray_handler_fn)NULL, __ATOMIC_RELEASE);
    return 1;
}

DARWIN_XRAY_EXPORT size_t __xray_max_function_id(void) {
    if (!darwin_xray_ensure_indexed()) return 0u;
    return (size_t)g_darwin_slot_count;
}

DARWIN_XRAY_EXPORT uintptr_t __xray_function_address(int32_t FuncId) {
    if (!darwin_xray_ensure_indexed()) return 0u;
    if (FuncId < 1 || (uint32_t)FuncId > g_darwin_slot_count) return 0u;
    SimpleDarwinXraySlotV1 *slot = g_darwin_slots[(uint32_t)FuncId];
    return (slot != NULL) ? (uintptr_t)slot->func_addr : 0u;
}

DARWIN_XRAY_EXPORT const char *__xray_function_name_v1(int32_t FuncId) {
    if (!darwin_xray_ensure_indexed()) return "";
    if (FuncId < 1 || (uint32_t)FuncId > g_darwin_slot_count) return "";
    SimpleDarwinXraySlotV1 *slot = g_darwin_slots[(uint32_t)FuncId];
    return (slot != NULL && slot->func_name != NULL) ? slot->func_name : "";
}

DARWIN_XRAY_EXPORT enum XRayPatchingStatus __xray_patch_function(int32_t FuncId) {
    if (FuncId <= 0) return FAILED;
    return darwin_xray_patch_impl(FuncId, 1);
}

DARWIN_XRAY_EXPORT enum XRayPatchingStatus __xray_unpatch_function(int32_t FuncId) {
    if (FuncId <= 0) return FAILED;
    return darwin_xray_patch_impl(FuncId, 0);
}

DARWIN_XRAY_EXPORT enum XRayPatchingStatus __xray_patch(void) {
    return darwin_xray_patch_impl(0, 1);
}

DARWIN_XRAY_EXPORT enum XRayPatchingStatus __xray_unpatch(void) {
    return darwin_xray_patch_impl(0, 0);
}

DARWIN_XRAY_EXPORT int64_t simple_xray_llvm_max_function_id(void) {
    size_t max_id = __xray_max_function_id();
    if (max_id > (size_t)XRAY_MAIN_OBJECT_MAX_ID) return 0;
    return (int64_t)max_id;
}

DARWIN_XRAY_EXPORT int64_t simple_xray_llvm_install(int64_t arena, int64_t generation,
                                                    int64_t context,
                                                    int64_t module_instance) {
    if (arena <= 0 || (arena % 8) != 0 || generation <= 0 || context <= 0 ||
        module_instance <= 0) {
        return 0;
    }
    uint64_t previous_module =
        __atomic_load_n(&g_simple_xray_module_instance, __ATOMIC_RELAXED);
    if (previous_module != 0 && previous_module != (uint64_t)module_instance) {
        return 0;
    }
    int64_t *base = (int64_t *)(intptr_t)arena;
    int64_t capacity = base[CH_CAPACITY];
    if (capacity <= 0 || capacity > CH_MAX_RECORDS) return 0;
    if (base[CH_GENERATION] != generation || base[CH_CONTEXT] != context) return 0;
    if (base[CH_ARENA_BYTES] != (CH_HEADER_WORDS + capacity * CH_RECORD_WORDS) * 8) {
        return 0;
    }
    if (__atomic_load_n(&base[CH_GATE], __ATOMIC_SEQ_CST) != 0) return 0;
    uint64_t mode = __atomic_load_n(&g_xray_handler_mode, __ATOMIC_ACQUIRE);
    if (mode == 0) {
        uint64_t expected = 0;
        if (!__atomic_compare_exchange_n(&g_xray_handler_mode, &expected, 1, 0,
                                         __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
            mode = expected;
        } else {
            mode = 1;
        }
    }
    if (mode != 1) return 0;
    int64_t *previous = __atomic_load_n(&g_simple_xray_arena, __ATOMIC_ACQUIRE);
    __atomic_store_n(&g_simple_xray_module_instance, (uint64_t)module_instance,
                     __ATOMIC_RELAXED);
    __atomic_store_n(&g_simple_xray_arena, base, __ATOMIC_RELEASE);
    if (__xray_set_handler(simple_darwin_xray_channel_handler) != 1) {
        __atomic_store_n(&g_simple_xray_arena, previous, __ATOMIC_RELEASE);
        __atomic_store_n(&g_simple_xray_module_instance, previous_module,
                         __ATOMIC_RELAXED);
        return 0;
    }
    return 1;
}

DARWIN_XRAY_EXPORT int64_t simple_xray_llvm_patch_function(int64_t id) {
    int64_t max_id = simple_xray_llvm_max_function_id();
    if (id < 1 || id > max_id) return SIMPLE_XRAY_STATUS_INVALID_ID;
    return (int64_t)__xray_patch_function((int32_t)id);
}

DARWIN_XRAY_EXPORT int64_t simple_xray_llvm_unpatch_function(int64_t id) {
    int64_t max_id = simple_xray_llvm_max_function_id();
    if (id < 1 || id > max_id) return SIMPLE_XRAY_STATUS_INVALID_ID;
    return (int64_t)__xray_unpatch_function((int32_t)id);
}

/* Built-in live runtime diagnostic counter handler for in-process verification.
 * Not rt_*: private XRay diagnostic leaves, not core runtime primitives. */
static void darwin_xray_counter_handler(int32_t fid, enum XRayEntryType type) {
    __atomic_store_n(&g_counter_last_fid, (int64_t)fid, __ATOMIC_RELAXED);
    if (type == ENTRY || type == LOG_ARGS_ENTRY) {
        __atomic_fetch_add(&g_counter_entries, 1, __ATOMIC_RELAXED);
    } else if (type == EXIT || type == TAIL) {
        __atomic_fetch_add(&g_counter_exits, 1, __ATOMIC_RELAXED);
    }
}

DARWIN_XRAY_EXPORT int64_t simple_xray_darwin_enable_counter_v1(void) {
    __atomic_store_n(&g_counter_entries, 0, __ATOMIC_RELEASE);
    __atomic_store_n(&g_counter_exits, 0, __ATOMIC_RELEASE);
    __atomic_store_n(&g_counter_last_fid, 0, __ATOMIC_RELEASE);
    if (__xray_set_handler(darwin_xray_counter_handler) != 1) return 0;
    return (__xray_patch() == SUCCESS) ? 1 : 0;
}

DARWIN_XRAY_EXPORT int64_t simple_xray_darwin_disable_counter_v1(void) {
    enum XRayPatchingStatus st = __xray_unpatch();
    __xray_remove_handler();
    return (st == SUCCESS) ? 1 : 0;
}

DARWIN_XRAY_EXPORT int64_t simple_xray_darwin_entry_count_v1(void) {
    return __atomic_load_n(&g_counter_entries, __ATOMIC_ACQUIRE);
}

DARWIN_XRAY_EXPORT int64_t simple_xray_darwin_exit_count_v1(void) {
    return __atomic_load_n(&g_counter_exits, __ATOMIC_ACQUIRE);
}

DARWIN_XRAY_EXPORT int64_t simple_xray_darwin_max_func_id_v1(void) {
    return simple_xray_llvm_max_function_id();
}

DARWIN_XRAY_EXPORT int64_t simple_xray_darwin_last_func_id_v1(void) {
    return __atomic_load_n(&g_counter_last_fid, __ATOMIC_ACQUIRE);
}

/* Resident mode-2 descriptor hooks remain Linux-ELF-only; provide fail-closed
 * definitions so Darwin std.nogc_sync_mut.trace closures link cleanly. */
DARWIN_XRAY_EXPORT int64_t simple_xray_llvm_resident_publish_v1(int64_t descriptor) {
    (void)descriptor;
    return 0;
}

DARWIN_XRAY_EXPORT int64_t simple_xray_llvm_resident_close_v1(void) {
    return 0;
}

DARWIN_XRAY_EXPORT int64_t simple_xray_llvm_resident_drained_v1(void) {
    return 1;
}

DARWIN_XRAY_EXPORT int64_t simple_xray_llvm_resident_loss_inexact_v1(void) {
    return 0;
}

#else /* Non-Apple syntax-check stub */

int simple_xray_darwin_runtime_unused_tu_anchor(void) {
    return 0;
}

#endif
