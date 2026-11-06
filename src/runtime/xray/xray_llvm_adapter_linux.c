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

/* The handler registered with compiler-rt: map the compiler-rt id and entry
 * type, then the shared producer (xray_channel_producer_v1.h). */
__attribute__((xray_never_instrument, used)) static void simple_xray_handler(int32_t fid,
                                                                     enum XRayEntryType type) {
    int64_t *base = __atomic_load_n(&g_simple_xray_arena, __ATOMIC_ACQUIRE);
    if (base == NULL || fid <= 0 || fid > XRAY_MAIN_OBJECT_MAX_ID) return; /* DSO ids: not ours */
    uint64_t kind;
    if (type == ENTRY) kind = 1;
    else if (type == EXIT) kind = 2;
    else if (type == TAIL) kind = 3;
    else return;
    /* Stage 1: dense site id == LLVM function id (one image). */
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
