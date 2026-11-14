/*
 * xray_llvm_adapter_linux.c -- stage-1 Linux LLVM XRay C boundary (PR4).
 *
 * Design: doc/04_architecture/compiler/xray/xray_compiler_structural_change_2026-11-06.md
 * section C. Stage 1 delegates sled patching to compiler-rt's XRay runtime
 * (libclang_rt.xray, linked with `clang -fxray-instrument`); the control plane
 * (selection, quiescent ordering, rollback, fail-closed status mapping) is the
 * Simple module src/lib/nogc_sync_mut/trace/xray_llvm_adapter_v1.spl, bound by
 * src/lib/nogc_sync_mut/trace/xray_llvm_host_leaf_v1.spl.
 *
 * Simple twin of the hot path: the handler shim's producer (shared with the
 * stage-2 native handler in xray_channel_producer_v1.h) is a word-for-word
 * mirror of trace_native_channel_record_words_v1 in
 * src/lib/nogc_sync_mut/trace/observer_native_channel_v1.spl (same arena
 * layout, same gate CAS, same bounded loss counter). The consumer stays Simple
 * (trace_native_channel_poll_into_v1). Keep the two in lockstep.
 *
 * Hot path rules (plan section 7 "Handler policy"): no lock, no allocation, no
 * libc call, no syscall, no floating-point/vector register use. It is
 * excluded from instrumentation. Build this TU WITHOUT -fxray-instrument and
 * with -mgeneral-regs-only (+ -mno-outline-atomics on aarch64) so the compiler
 * cannot touch vector state the upstream trampoline does not save, nor call
 * out-of-line atomic helpers. Not an #error guard: the C-runtime syntax gate
 * compiles every src/runtime TU with default flags. The flags are enforced on
 * the produced object by scripts/check/check-xray-llvm-adapter-e2e.shs
 * (handler disassembly: no call/branch out, no FP/vector register).
 *
 * Not part of the core runtime archive: linked only into `--xray` binaries.
 * Not `rt_*`: a private adapter leaf, not a runtime primitive.
 */
#include <stddef.h>
#include <stdint.h>

#include "xray_channel_producer_v1.h"

#if defined(__linux__) && (defined(__x86_64__) || defined(__aarch64__))
#define SIMPLE_XRAY_LLVM_SUPPORTED 1
#endif

#define SIMPLE_XRAY_STATUS_INVALID_ID (-1)

#ifdef SIMPLE_XRAY_LLVM_SUPPORTED

#include "xray_resident_admission_v1.h"
#include "xray_resident_descriptor_v1.h"

/* compiler-rt include/xray/xray_interface.h (LLVM 23.1.0), declared locally so
 * a host without the clang resource headers can still syntax-check this TU. */
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
extern int __xray_set_handler(void (*entry)(int32_t, enum XRayEntryType));
extern enum XRayPatchingStatus __xray_patch_function(int32_t FuncId);
extern enum XRayPatchingStatus __xray_unpatch_function(int32_t FuncId);
extern size_t __xray_max_function_id(void);

/* compiler-rt packs ids as 24-bit function | 8-bit object (XRayNFnBits=24);
 * object 0 is the main executable, the only stage-1 image. */
#define XRAY_MAIN_OBJECT_MAX_ID ((1 << 24) - 1)

static int64_t *g_simple_xray_arena;
static uint64_t g_simple_xray_module_instance;
static uint64_t g_simple_xray_sequence;


/* One process owner; legacy tests/native adapter cannot replace this handler
 * once the resident provider claims mode2. All reachable storage is resident. */
static simple_xray_resident_admission_v1 g_resident_admission = SIMPLE_XRAY_RESIDENT_ADMISSION_INIT_V1;
static uint64_t g_xray_handler_mode;
static uint64_t g_xray_control;
static uint64_t g_xray_runtime_ready;
/* HELD=1, EVER_OWNED_SPAWN_ATTEMPT=2, WINDOW_SPENT=4. */
static uint64_t g_xray_startup_owned_threads;
static uint64_t g_xray_last_generation;
static uint64_t g_xray_admission_lost;
static __thread __attribute__((tls_model("initial-exec"))) int g_xray_control_owned;
static __thread __attribute__((tls_model("initial-exec"))) int g_xray_startup_window_owned;
static __thread __attribute__((tls_model("initial-exec"))) int g_xray_in_handler;
static __thread __attribute__((tls_model("initial-exec"))) uint64_t g_xray_context_sequence;

/* Called only by the owned hosted entry wrapper after runtime/TLS init.
 * This is readiness, never target/profile or quiescence admission. */
void simple_xray_resident_runtime_ready_v1(void) {
    __atomic_store_n(&g_xray_runtime_ready, 1, __ATOMIC_RELEASE);
}
int64_t simple_xray_resident_runtime_is_ready_v1(void) {
    return (int64_t)__atomic_load_n(&g_xray_runtime_ready, __ATOMIC_ACQUIRE);
}
int64_t simple_xray_resident_in_hook_v1(void) { return g_xray_in_handler != 0; }

int64_t simple_xray_resident_control_enter_v1(void) {
    uint64_t expected = 0;
    if (g_xray_in_handler || g_xray_control_owned ||
        !__atomic_compare_exchange_n(&g_xray_control, &expected, 1, 0,
                                     __ATOMIC_ACQUIRE, __ATOMIC_RELAXED)) return 0;
    g_xray_control_owned = 1;
    return 1;
}
void simple_xray_resident_control_leave_v1(void) {
    if (!g_xray_control_owned) return;
    g_xray_control_owned = 0;
    __atomic_store_n(&g_xray_control, 0, __ATOMIC_RELEASE);
}
/* This ledger proves only absence of owned spawn attempts. The actual linked
 * profile must separately exclude foreign/constructor execution before any
 * startup observation authority can be issued. No profile is enabled here. */
int64_t simple_xray_startup_owned_spawn_admit_v1(void) {
    uint64_t state = __atomic_load_n(&g_xray_startup_owned_threads, __ATOMIC_ACQUIRE);
    for (int attempt = 0; attempt < 8; ++attempt) {
        if (state & 1u) return 0;
        uint64_t desired = state | 2u;
        if (__atomic_compare_exchange_n(&g_xray_startup_owned_threads, &state,
                desired, 0, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) return 1;
    }
    return 0;
}
int64_t simple_xray_startup_no_owned_threads_begin_v1(void) {
    if (!g_xray_control_owned || g_xray_in_handler ||
        !__atomic_load_n(&g_xray_runtime_ready, __ATOMIC_ACQUIRE)) return 0;
    uint64_t expected = 0;
    if (!__atomic_compare_exchange_n(&g_xray_startup_owned_threads, &expected,
        1, 0, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) return 0;
    g_xray_startup_window_owned = 1;
    return 1;
}
/* Necessary thread/window association only; never a qualified profile grant. */
int64_t simple_xray_startup_current_owner_v1(void) {
    if (!g_xray_control_owned || !g_xray_startup_window_owned || g_xray_in_handler ||
        !__atomic_load_n(&g_xray_runtime_ready, __ATOMIC_ACQUIRE)) return 0;
    uint64_t state = __atomic_load_n(&g_xray_startup_owned_threads, __ATOMIC_ACQUIRE);
    return (state & 5u) == 1u;
}
int64_t simple_xray_startup_no_owned_threads_end_v1(void) {
    if (!simple_xray_startup_current_owner_v1()) return 0;
    uint64_t state = __atomic_load_n(&g_xray_startup_owned_threads, __ATOMIC_ACQUIRE);
    for (int attempt = 0; attempt < 8; ++attempt) {
        if ((state & 5u) != 1u) return 0;
        uint64_t desired = (state | 4u) & ~UINT64_C(1);
        if (__atomic_compare_exchange_n(&g_xray_startup_owned_threads, &state,
                desired, 0, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
            g_xray_startup_window_owned = 0;
            return 1;
        }
    }
    return 0;
}
/* Actual entry owner seals idle or held state before main, even if no startup
 * consumer ran. Mark SPENT first so no competing begin can reopen the window. */
void simple_xray_startup_window_seal_v1(void) {
    __atomic_fetch_or(&g_xray_startup_owned_threads, 4, __ATOMIC_ACQ_REL);
    __atomic_fetch_and(&g_xray_startup_owned_threads, ~UINT64_C(1), __ATOMIC_ACQ_REL);
    g_xray_startup_window_owned = 0;
}
static int64_t simple_xray_thread_attach_internal_v1(int cold_root) {
    if (g_xray_in_handler) return -1;
    g_xray_in_handler = 1;
    SimpleXrayResidentDescriptorV1 *descriptor = simple_xray_resident_acquire_v1(&g_resident_admission);
    if (!descriptor) { g_xray_in_handler = 0; return -1; }
    const void *pool = (const void *)(uintptr_t)descriptor->pool;
    int already = simple_xray_thread_current_pool_v1 == pool && simple_xray_thread_current_slot_v1 != NULL;
    if (cold_root && !already && simple_xray_thread_current_slot_v1 != NULL)
        (void)simple_xray_thread_detach_pool_v1();
    int64_t status = simple_xray_thread_attach_pool_v1(pool, descriptor->pool_bytes);
    if (status == 1 && !already) {
        g_xray_context_sequence = 1;
        int64_t *arena = (void *)(intptr_t)simple_xray_thread_current_arena_v1(pool);
        /* Mandatory context/generation transition precedes its first data.
         * New, exclusively claimed arenas are empty before this publication. */
        simple_xray_channel_produce_selected_sequence_v1(arena, 4,
            descriptor->module_instance, 0, NULL, g_xray_context_sequence);
    }
    simple_xray_resident_release_v1(&g_resident_admission);
    g_xray_in_handler = 0;
    return status;
}
int64_t simple_xray_thread_attach_v1(void) {
    return simple_xray_thread_attach_internal_v1(0);
}
void simple_xray_thread_detach_v1(void) {
    (void)simple_xray_thread_detach_pool_v1();
}

__attribute__((always_inline)) static inline void simple_xray_resident_event_v1(
        int32_t fid, uint64_t kind) {
    if (g_xray_in_handler) {
        /* Reentry may precede first TLS publication or refer to a retired
         * pool. Never silently charge an unidentifiable generation. */
        __atomic_store_n(&g_xray_admission_lost, UINT64_MAX, __ATOMIC_RELAXED);
        simple_xray_thread_note_unattached_v1(simple_xray_thread_current_pool_v1);
        return;
    }
    g_xray_in_handler = 1;
    SimpleXrayResidentDescriptorV1 *descriptor = simple_xray_resident_acquire_v1(&g_resident_admission);
    if (!descriptor) {
        if ((atomic_load_explicit(&g_resident_admission.gate, memory_order_relaxed) & 1u) == 0)
            __atomic_store_n(&g_xray_admission_lost, UINT64_MAX, __ATOMIC_RELAXED);
        g_xray_in_handler = 0;
        return;
    }
    const SimpleXrayResidentBindingV1 *binding = simple_xray_resident_find_v1(descriptor, (uint64_t)fid);
    if (binding && (descriptor->event_mask & (UINT64_C(1) << (kind - 1)))) {
        const void *pool = (const void *)(uintptr_t)descriptor->pool;
        int64_t arena = simple_xray_thread_current_arena_v1(pool);
        if (arena == 0) {
            simple_xray_thread_note_unattached_v1((const SimpleXrayThreadContextHeaderV1 *)pool);
        } else {
            int64_t *base = (int64_t *)(intptr_t)arena;
            if (g_xray_context_sequence == UINT64_MAX) {
                simple_xray_loss(base);
                __atomic_fetch_or(&base[CH_GATE], INT64_C(2), __ATOMIC_SEQ_CST);
            } else {
                ++g_xray_context_sequence; /* after map/mask, before queue admission */
                simple_xray_channel_produce_selected_sequence_v1(base, kind,
                    descriptor->module_instance, binding->function_site, NULL, g_xray_context_sequence);
            }
        }
    }
    simple_xray_resident_release_v1(&g_resident_admission);
    g_xray_in_handler = 0;
}

/* The handler registered with compiler-rt: map the compiler-rt id and entry
 * type, then the shared producer (xray_channel_producer_v1.h). */
__attribute__((xray_never_instrument, used)) static void simple_xray_handler(int32_t fid,
                                                                     enum XRayEntryType type) {
    if (fid <= 0 || fid > XRAY_MAIN_OBJECT_MAX_ID) return;
    uint64_t kind;
    if (type == ENTRY) kind = 1;
    else if (type == EXIT) kind = 2;
    else if (type == TAIL) kind = 3;
    else return;
    if (__atomic_load_n(&g_xray_handler_mode, __ATOMIC_ACQUIRE) == 2) {
        simple_xray_resident_event_v1(fid, kind);
        return;
    }
    int64_t *base = __atomic_load_n(&g_simple_xray_arena, __ATOMIC_ACQUIRE);
    if (base == NULL) return;
    /* Legacy private harness path: dense site id == LLVM function id (one image). */
    uint64_t id = (uint64_t)(uint32_t)fid;
    simple_xray_channel_produce_v1(base, kind,
                                   __atomic_load_n(&g_simple_xray_module_instance, __ATOMIC_RELAXED),
                                   id | (id << 32), &g_simple_xray_sequence);
}

int64_t simple_xray_llvm_max_function_id(void) {
    size_t max_id = __xray_max_function_id();
    if (max_id > (size_t)XRAY_MAIN_OBJECT_MAX_ID) return 0; /* would alias a DSO object id */
    return (int64_t)max_id;
}

/* Caller supplies only its own resident allocations, never arbitrary
 * application pointers. Check arithmetic/layout before following each level. */
static int simple_xray_resident_range_v1(uint64_t address, uint64_t size) {
    return address != 0 && (address & 7u) == 0 && size != 0 &&
           size <= INT64_MAX && address <= (uint64_t)INT64_MAX - size;
}
static int simple_xray_resident_overlap_v1(uint64_t a, uint64_t as, uint64_t b, uint64_t bs) {
    return a <= b ? b - a < as : a - b < bs;
}
static int simple_xray_resident_descriptor_valid_v1(SimpleXrayResidentDescriptorV1 *d) {
    if (!simple_xray_resident_range_v1((uintptr_t)d, 80) || d->schema != 1 ||
        d->actual_bytes != 80 || d->generation == 0 || d->generation > INT64_MAX ||
        d->module_instance == 0 || d->module_instance > INT64_MAX ||
        d->reserved_zero != 0 || (d->event_mask & ~UINT64_C(7)) != 0 ||
        d->map_count == 0 || d->map_count > 4096 ||
        !simple_xray_resident_range_v1(d->map, d->map_count * 16) ||
        !simple_xray_resident_range_v1(d->pool, d->pool_bytes) || d->pool_bytes < 64)
        return 0;
    SimpleXrayThreadContextHeaderV1 *pool = (void *)(uintptr_t)d->pool;
    if (pool->magic != SIMPLE_XRAY_THREAD_CONTEXT_MAGIC_V1 || pool->schema != 1 ||
        pool->generation != d->generation || pool->actual_bytes != d->pool_bytes ||
        pool->max_slots == 0 || pool->max_slots > 128 || pool->slots_offset != 64 ||
        pool->reserved_zero != 0 || pool->unattached_lost != 0 ||
        d->pool_bytes != 64 + pool->max_slots * 32) return 0;
    if (simple_xray_resident_overlap_v1((uintptr_t)d, 80, d->pool, d->pool_bytes) ||
        simple_xray_resident_overlap_v1((uintptr_t)d, 80, d->map, d->map_count * 16) ||
        simple_xray_resident_overlap_v1(d->pool, d->pool_bytes, d->map, d->map_count * 16)) return 0;
    SimpleXrayThreadContextSlotV1 *slots = (void *)((uint8_t *)pool + 64);
    for (uint64_t i = 0; i < pool->max_slots; ++i) {
        SimpleXrayThreadContextSlotV1 *slot = &slots[i];
        if (!simple_xray_resident_range_v1(slot->arena, slot->bytes) || slot->bytes < 128 ||
            slot->context_id == 0 || slot->context_id > INT64_MAX || slot->state != 0) return 0;
        int64_t *arena = (void *)(uintptr_t)slot->arena;
        if (arena[CH_CAPACITY] < 1 || arena[CH_CAPACITY] > CH_MAX_RECORDS ||
            slot->bytes != (uint64_t)(128 + arena[CH_CAPACITY] * 96) ||
            arena[CH_ARENA_BYTES] != (int64_t)slot->bytes ||
            arena[CH_GENERATION] != (int64_t)d->generation ||
            arena[CH_CONTEXT] != (int64_t)slot->context_id ||
            __atomic_load_n(&arena[CH_GATE], __ATOMIC_ACQUIRE) != 0 ||
            arena[4] != 0 || arena[CH_WRITE] != 0 || arena[CH_READ] != 0 ||
            arena[CH_LOST] != 0 || arena[CH_LOSS_INEXACT] != 0) return 0;
        for (unsigned reserved = 10; reserved < CH_HEADER_WORDS; ++reserved)
            if (arena[reserved] != 0) return 0;
        if (simple_xray_resident_overlap_v1(slot->arena, slot->bytes, (uintptr_t)d, 80) ||
            simple_xray_resident_overlap_v1(slot->arena, slot->bytes, d->pool, d->pool_bytes) ||
            simple_xray_resident_overlap_v1(slot->arena, slot->bytes, d->map, d->map_count * 16)) return 0;
        for (uint64_t j = 0; j < i; ++j)
            if (slots[j].context_id == slot->context_id ||
                simple_xray_resident_overlap_v1(slot->arena, slot->bytes, slots[j].arena, slots[j].bytes)) return 0;
    }
    const SimpleXrayResidentBindingV1 *map = (void *)(uintptr_t)d->map;
    uint64_t previous = 0, maximum = (uint64_t)simple_xray_llvm_max_function_id();
    for (uint64_t i = 0; i < d->map_count; ++i) {
        uint32_t function = (uint32_t)map[i].function_site;
        uint32_t site = (uint32_t)(map[i].function_site >> 32);
        if (map[i].llvm_id <= previous || map[i].llvm_id > maximum || function == 0 || site == 0) return 0;
        previous = map[i].llvm_id;
        for (uint64_t j = 0; j < i; ++j)
            if ((uint32_t)map[j].function_site == function ||
                (uint32_t)(map[j].function_site >> 32) == site) return 0;
    }
    return 1;
}
int64_t simple_xray_llvm_resident_publish_v1(int64_t descriptor) {
    if (!g_xray_control_owned || !simple_xray_resident_runtime_is_ready_v1() ||
        !simple_xray_resident_drained_v1(&g_resident_admission)) return 0;
    SimpleXrayResidentDescriptorV1 *d = (void *)(intptr_t)descriptor;
    if (!simple_xray_resident_descriptor_valid_v1(d) ||
        d->generation <= g_xray_last_generation) return 0;
    uint64_t mode = __atomic_load_n(&g_xray_handler_mode, __ATOMIC_ACQUIRE);
    if (mode == 0) {
        uint64_t expected = 0;
        if (!__atomic_compare_exchange_n(&g_xray_handler_mode, &expected, 2, 0,
                                        __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) mode = expected;
        else mode = 2;
    }
    if (mode != 2 || __xray_set_handler(simple_xray_handler) != 1) return 0;
    if (!simple_xray_resident_publish_v1(&g_resident_admission, d)) return 0;
    g_xray_last_generation = d->generation;
    return 1;
}
int64_t simple_xray_llvm_resident_close_v1(void) {
    if (!g_xray_control_owned) return 0;
    simple_xray_resident_close_v1(&g_resident_admission);
    return 1;
}
int64_t simple_xray_llvm_resident_drained_v1(void) {
    return simple_xray_resident_drained_v1(&g_resident_admission);
}
int64_t simple_xray_llvm_resident_loss_inexact_v1(void) {
    return __atomic_load_n(&g_xray_admission_lost, __ATOMIC_RELAXED) == UINT64_MAX;
}
/* Only a runtime-owned task root may replace a stale session attachment;
 * no selected user frame may be active at this cold boundary. */
int64_t simple_xray_thread_task_root_v1(void) {
    return simple_xray_thread_attach_internal_v1(1);
}


/* Publish an initialized, open, resident channel arena (owned by the Simple
 * session owner until process exit), then register the handler. Returns 1 on
 * success, 0 when the arena does not describe the stated generation/context or
 * compiler-rt refused the handler; nothing stays published on failure. */
int64_t simple_xray_llvm_install(int64_t arena, int64_t generation, int64_t context,
                                 int64_t module_instance) {
    if (arena <= 0 || (arena % 8) != 0 || generation <= 0 || context <= 0 || module_instance <= 0)
        return 0;
    uint64_t previous_module = __atomic_load_n(&g_simple_xray_module_instance, __ATOMIC_RELAXED);
    if (previous_module != 0 && previous_module != (uint64_t)module_instance)
        return 0; /* stage 1 has exactly one instrumented image */
    int64_t *base = (int64_t *)(intptr_t)arena;
    int64_t capacity = base[CH_CAPACITY];
    if (capacity <= 0 || capacity > CH_MAX_RECORDS) return 0;
    if (base[CH_GENERATION] != generation || base[CH_CONTEXT] != context) return 0;
    if (base[CH_ARENA_BYTES] != (CH_HEADER_WORDS + capacity * CH_RECORD_WORDS) * 8) return 0;
    if (__atomic_load_n(&base[CH_GATE], __ATOMIC_SEQ_CST) != 0) return 0;
    uint64_t mode = __atomic_load_n(&g_xray_handler_mode, __ATOMIC_ACQUIRE);
    if (mode == 0) {
        uint64_t expected = 0;
        if (!__atomic_compare_exchange_n(&g_xray_handler_mode, &expected, 1, 0,
                                        __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) mode = expected;
        else mode = 1;
    }
    if (mode != 1) return 0;
    int64_t *previous = __atomic_load_n(&g_simple_xray_arena, __ATOMIC_ACQUIRE);
    __atomic_store_n(&g_simple_xray_module_instance, (uint64_t)module_instance, __ATOMIC_RELAXED);
    __atomic_store_n(&g_simple_xray_arena, base, __ATOMIC_RELEASE);
    if (__xray_set_handler(simple_xray_handler) != 1) {
        __atomic_store_n(&g_simple_xray_arena, previous, __ATOMIC_RELEASE);
        __atomic_store_n(&g_simple_xray_module_instance, previous_module, __ATOMIC_RELAXED);
        return 0;
    }
    return 1;
}

/* Unknown ids are rejected here, before compiler-rt is called. A failed
 * mprotect inside compiler-rt is reported as FAILED (3), never a crash. */
int64_t simple_xray_llvm_patch_function(int64_t id) {
    int64_t max_id = simple_xray_llvm_max_function_id();
    if (id < 1 || id > max_id) return SIMPLE_XRAY_STATUS_INVALID_ID;
    return (int64_t)__xray_patch_function((int32_t)id);
}

int64_t simple_xray_llvm_unpatch_function(int64_t id) {
    int64_t max_id = simple_xray_llvm_max_function_id();
    if (id < 1 || id > max_id) return SIMPLE_XRAY_STATUS_INVALID_ID;
    return (int64_t)__xray_unpatch_function((int32_t)id);
}

#else /* unsupported target: no sleds, nothing can be installed or patched */


int64_t simple_xray_llvm_max_function_id(void) { return 0; }
int64_t simple_xray_llvm_install(int64_t arena, int64_t generation, int64_t context,
                                 int64_t module_instance) {
    (void)arena;
    (void)generation;
    (void)context;
    (void)module_instance;
    return 0;
}
int64_t simple_xray_llvm_patch_function(int64_t id) {
    (void)id;
    return SIMPLE_XRAY_STATUS_INVALID_ID;
}
int64_t simple_xray_llvm_unpatch_function(int64_t id) {
    (void)id;
    return SIMPLE_XRAY_STATUS_INVALID_ID;
}

#endif
