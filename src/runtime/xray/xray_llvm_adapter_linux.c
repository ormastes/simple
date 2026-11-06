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
 * Simple twin of the hot path: the handler shim's producer is a word-for-word
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

#if defined(__linux__) && (defined(__x86_64__) || defined(__aarch64__))
#define SIMPLE_XRAY_LLVM_SUPPORTED 1
#endif

#define SIMPLE_XRAY_STATUS_INVALID_ID (-1)

#ifdef SIMPLE_XRAY_LLVM_SUPPORTED

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

/* observer_native_channel_v1 layout, in i64 words. */
#define CH_GATE 0          /* 0 open, 1 open+producer, 2 closed, 3 closed+producer */
#define CH_GENERATION 1
#define CH_CONTEXT 2
#define CH_CAPACITY 3
#define CH_WRITE 5         /* published write index */
#define CH_READ 6          /* released read index */
#define CH_LOST 7          /* saturating lost count */
#define CH_LOSS_INEXACT 8
#define CH_ARENA_BYTES 9
#define CH_HEADER_WORDS 16
#define CH_RECORD_WORDS 12
#define CH_MAX_RECORDS 4096
#define CH_RECORD_HEADER 6291457u /* schema 1 | record size 96 << 16 */
/* compiler-rt packs ids as 24-bit function | 8-bit object (XRayNFnBits=24);
 * object 0 is the main executable, the only stage-1 image. */
#define XRAY_MAIN_OBJECT_MAX_ID ((1 << 24) - 1)

static int64_t *g_simple_xray_arena;
static uint64_t g_simple_xray_module_instance;
static uint64_t g_simple_xray_sequence;

__attribute__((xray_never_instrument)) static inline int64_t simple_xray_cas(int64_t *cell,
                                                                            int64_t expected,
                                                                            int64_t value) {
    __atomic_compare_exchange_n(cell, &expected, value, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
    return expected; /* the observed old value, like rt_par_atomic_cmpxchg_i64 */
}

__attribute__((xray_never_instrument)) static void simple_xray_loss(int64_t *base) {
    int64_t current = __atomic_load_n(&base[CH_LOST], __ATOMIC_SEQ_CST);
    for (int attempt = 0; attempt < 8; attempt++) {
        if (current == INT64_MAX) break;
        int64_t seen = simple_xray_cas(&base[CH_LOST], current, current + 1);
        if (seen == current) return;
        current = seen;
    }
    __atomic_exchange_n(&base[CH_LOSS_INEXACT], 1, __ATOMIC_SEQ_CST);
}

__attribute__((xray_never_instrument)) static uint64_t simple_xray_timestamp(void) {
#if defined(__aarch64__)
    return (uint64_t)__builtin_arm_rsr64("cntvct_el0");
#else
    return (uint64_t)__builtin_ia32_rdtsc();
#endif
}

/* The handler registered with compiler-rt. One gate CAS admits and serializes
 * the producer; a concurrent producer or a full ring counts loss and returns.
 * Never blocks, spins without bound, allocates or calls out. */
__attribute__((xray_never_instrument, used)) static void simple_xray_handler(int32_t fid,
                                                                     enum XRayEntryType type) {
    int64_t *base = __atomic_load_n(&g_simple_xray_arena, __ATOMIC_ACQUIRE);
    if (base == NULL || fid <= 0 || fid > XRAY_MAIN_OBJECT_MAX_ID) return; /* DSO ids: not ours */
    uint64_t kind;
    if (type == ENTRY) kind = 1;
    else if (type == EXIT) kind = 2;
    else if (type == TAIL) kind = 3;
    else return;
    int64_t state = simple_xray_cas(&base[CH_GATE], 0, 1);
    if ((state & 2) != 0) return; /* closed: not loss, admission is over */
    if (state != 0) {
        simple_xray_loss(base);
        return;
    }
    int64_t write = __atomic_load_n(&base[CH_WRITE], __ATOMIC_SEQ_CST);
    int64_t read = __atomic_load_n(&base[CH_READ], __ATOMIC_SEQ_CST);
    int64_t capacity = base[CH_CAPACITY];
    if (capacity <= 0) {
        __atomic_add_fetch(&base[CH_GATE], -1, __ATOMIC_SEQ_CST);
        return;
    }
    if (write == INT64_MAX) {
        __atomic_exchange_n(&base[CH_GATE], 3, __ATOMIC_SEQ_CST);
        simple_xray_loss(base);
        __atomic_add_fetch(&base[CH_GATE], -1, __ATOMIC_SEQ_CST);
        return;
    }
    if (write - read >= capacity) {
        simple_xray_loss(base);
        __atomic_add_fetch(&base[CH_GATE], -1, __ATOMIC_SEQ_CST);
        return;
    }
    /* Taken only after admission, so drops leave no gaps. Process-wide and
     * monotonic across generations; per-context order is the V1 guarantee. */
    uint64_t sequence = __atomic_add_fetch(&g_simple_xray_sequence, 1, __ATOMIC_RELAXED);
    int64_t *slot = base + CH_HEADER_WORDS + (write % capacity) * CH_RECORD_WORDS;
    uint64_t id = (uint64_t)(uint32_t)fid;
    slot[0] = (int64_t)(CH_RECORD_HEADER | (kind << 32));
    slot[1] = base[CH_GENERATION];
    slot[2] = (int64_t)__atomic_load_n(&g_simple_xray_module_instance, __ATOMIC_RELAXED);
    /* Stage 1: dense site id == LLVM function id (one image). */
    slot[3] = (int64_t)(id | (id << 32));
    slot[4] = base[CH_CONTEXT];
    slot[5] = (int64_t)sequence;
    slot[6] = (int64_t)simple_xray_timestamp();
    slot[7] = 0; /* span token: raw edges */
    slot[8] = 0;
    slot[9] = 0;
    slot[10] = 0;
    slot[11] = 0;
    __atomic_exchange_n(&base[CH_WRITE], write + 1, __ATOMIC_SEQ_CST);
    __atomic_add_fetch(&base[CH_GATE], -1, __ATOMIC_SEQ_CST);
}

int64_t simple_xray_llvm_max_function_id(void) {
    size_t max_id = __xray_max_function_id();
    if (max_id > (size_t)XRAY_MAIN_OBJECT_MAX_ID) return 0; /* would alias a DSO object id */
    return (int64_t)max_id;
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
