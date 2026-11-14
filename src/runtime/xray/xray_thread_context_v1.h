/*
 * xray_thread_context_v1.h -- bounded, preallocated thread attachment for
 * the LLVM XRay adapter.  This header is private to the XRay adapter TU; it
 * is not a runtime-wide TLS facility.
 *
 * The provider owns the descriptor and its shared close/pin admission word.
 * Attach and current-arena access run under a provider pin. Detach is
 * separately authorized after close because the current thread's pool, slots
 * and arenas are retained for the process lifetime in v1; detach clears this
 * thread's TLS and retires its slot without acquiring a descriptor or freeing
 * storage. Pools, slots and arenas are never reused in v1.
 */
#ifndef SIMPLE_XRAY_THREAD_CONTEXT_V1_H
#define SIMPLE_XRAY_THREAD_CONTEXT_V1_H

#include <stddef.h>
#include <stdint.h>

#if !defined(__linux__) || !(defined(__x86_64__) || defined(__aarch64__))
#error "XRay thread-context v1 currently supports Linux x86_64 and aarch64 only"
#endif

#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#error "XRay thread-context v1 schema 1 requires little-endian hosts"
#endif

#define SIMPLE_XRAY_THREAD_CONTEXT_MAGIC_V1 UINT64_C(0x0031565854435853)
#define SIMPLE_XRAY_THREAD_CONTEXT_SCHEMA_V1 UINT64_C(1)
#define SIMPLE_XRAY_THREAD_CONTEXT_HEADER_BYTES_V1 64u
#define SIMPLE_XRAY_THREAD_CONTEXT_SLOT_BYTES_V1 32u
#define SIMPLE_XRAY_THREAD_CONTEXT_UNUSED_V1 UINT64_C(0)
#define SIMPLE_XRAY_THREAD_CONTEXT_ATTACHED_V1 UINT64_C(1)
#define SIMPLE_XRAY_THREAD_CONTEXT_DETACHED_V1 UINT64_C(2)

/* Header offsets in bytes. The final word is reserved and must remain zero.
 * attach_closed is deliberately absent: the provider's packed admission
 * word is the sole authority for close and in-flight pins. */
enum {
    SIMPLE_XRAY_CTX_H_MAGIC = 0,
    SIMPLE_XRAY_CTX_H_SCHEMA = 8,
    SIMPLE_XRAY_CTX_H_ACTUAL_BYTES = 16,
    SIMPLE_XRAY_CTX_H_MAX_SLOTS = 24,
    SIMPLE_XRAY_CTX_H_GENERATION = 32,
    SIMPLE_XRAY_CTX_H_SLOTS_OFFSET = 40,
    SIMPLE_XRAY_CTX_H_UNATTACHED_LOST = 48,
    SIMPLE_XRAY_CTX_H_RESERVED_ZERO = 56,
};

enum {
    SIMPLE_XRAY_CTX_SLOT_ARENA = 0,
    SIMPLE_XRAY_CTX_SLOT_BYTES = 8,
    SIMPLE_XRAY_CTX_SLOT_CONTEXT_ID = 16,
    SIMPLE_XRAY_CTX_SLOT_STATE = 24,
};

typedef struct SimpleXrayThreadContextHeaderV1 {
    uint64_t magic;
    uint64_t schema;
    uint64_t actual_bytes;
    uint64_t max_slots;
    uint64_t generation;
    uint64_t slots_offset;
    uint64_t unattached_lost;
    uint64_t reserved_zero;
} SimpleXrayThreadContextHeaderV1;

typedef struct SimpleXrayThreadContextSlotV1 {
    uint64_t arena;
    uint64_t bytes;
    uint64_t context_id;
    uint64_t state;
} SimpleXrayThreadContextSlotV1;

_Static_assert(sizeof(SimpleXrayThreadContextHeaderV1) == SIMPLE_XRAY_THREAD_CONTEXT_HEADER_BYTES_V1,
               "XRay thread-context header must be 64 bytes");
_Static_assert(offsetof(SimpleXrayThreadContextHeaderV1, magic) == SIMPLE_XRAY_CTX_H_MAGIC,
               "XRay thread-context magic offset changed");
_Static_assert(offsetof(SimpleXrayThreadContextHeaderV1, schema) == SIMPLE_XRAY_CTX_H_SCHEMA,
               "XRay thread-context schema offset changed");
_Static_assert(offsetof(SimpleXrayThreadContextHeaderV1, actual_bytes) == SIMPLE_XRAY_CTX_H_ACTUAL_BYTES,
               "XRay thread-context actual_bytes offset changed");
_Static_assert(offsetof(SimpleXrayThreadContextHeaderV1, max_slots) == SIMPLE_XRAY_CTX_H_MAX_SLOTS,
               "XRay thread-context max_slots offset changed");
_Static_assert(offsetof(SimpleXrayThreadContextHeaderV1, generation) == SIMPLE_XRAY_CTX_H_GENERATION,
               "XRay thread-context generation offset changed");
_Static_assert(offsetof(SimpleXrayThreadContextHeaderV1, slots_offset) == SIMPLE_XRAY_CTX_H_SLOTS_OFFSET,
               "XRay thread-context slots_offset changed");
_Static_assert(offsetof(SimpleXrayThreadContextHeaderV1, unattached_lost) == SIMPLE_XRAY_CTX_H_UNATTACHED_LOST,
               "XRay thread-context loss offset changed");
_Static_assert(offsetof(SimpleXrayThreadContextHeaderV1, reserved_zero) == SIMPLE_XRAY_CTX_H_RESERVED_ZERO,
               "XRay thread-context reserved offset changed");
_Static_assert(sizeof(SimpleXrayThreadContextSlotV1) == SIMPLE_XRAY_THREAD_CONTEXT_SLOT_BYTES_V1,
               "XRay thread-context slot must be 32 bytes");
_Static_assert(offsetof(SimpleXrayThreadContextSlotV1, arena) == SIMPLE_XRAY_CTX_SLOT_ARENA,
               "XRay thread-context arena offset changed");
_Static_assert(offsetof(SimpleXrayThreadContextSlotV1, bytes) == SIMPLE_XRAY_CTX_SLOT_BYTES,
               "XRay thread-context bytes offset changed");
_Static_assert(offsetof(SimpleXrayThreadContextSlotV1, context_id) == SIMPLE_XRAY_CTX_SLOT_CONTEXT_ID,
               "XRay thread-context context_id offset changed");
_Static_assert(offsetof(SimpleXrayThreadContextSlotV1, state) == SIMPLE_XRAY_CTX_SLOT_STATE,
               "XRay thread-context state offset changed");
_Static_assert(sizeof(uint64_t) == 8 && _Alignof(uint64_t) >= 8,
               "XRay thread-context requires 8-byte 64-bit atomic cells");
_Static_assert(__atomic_always_lock_free(sizeof(uint64_t), 0),
               "XRay thread-context requires lock-free 64-bit atomics");

#if defined(__clang__) || defined(__GNUC__)
#define SIMPLE_XRAY_CONTEXT_TLS_V1 __thread __attribute__((tls_model("initial-exec")))
#else
#error "XRay thread-context v1 requires initial-exec TLS support"
#endif

/* This pair is control-plane state. The handler reads only current_slot and
 * must remain inside provider admission while using its arena. */
static SIMPLE_XRAY_CONTEXT_TLS_V1 const SimpleXrayThreadContextHeaderV1 *
    simple_xray_thread_current_pool_v1;
static SIMPLE_XRAY_CONTEXT_TLS_V1 SimpleXrayThreadContextSlotV1 *
    simple_xray_thread_current_slot_v1;

static inline uint64_t simple_xray_thread_context_load_u64_v1(const void *base,
                                                               size_t offset) {
    return __atomic_load_n((const uint64_t *)((const uint8_t *)base + offset),
                           __ATOMIC_ACQUIRE);
}

/* Called by the provider while it holds its shared attach-admission pin.
 * `supplied_bytes` is the actual writable descriptor extent. All arena
 * alignment, bounds, unique context IDs and disjointness are validated by the
 * provider before it publishes the descriptor. This helper revalidates the
 * table envelope and each slot before claiming one lifetime slot. */
static inline int64_t simple_xray_thread_attach_pool_v1(const void *pool,
                                                        uint64_t supplied_bytes) {
    if (pool == NULL || ((uintptr_t)pool & 7u) != 0 || supplied_bytes < 64u)
        return -3;

    const SimpleXrayThreadContextHeaderV1 *header =
        (const SimpleXrayThreadContextHeaderV1 *)pool;
    if (header->magic != SIMPLE_XRAY_THREAD_CONTEXT_MAGIC_V1 ||
        header->schema != SIMPLE_XRAY_THREAD_CONTEXT_SCHEMA_V1 ||
        header->generation == 0 || header->actual_bytes < 64u ||
        header->actual_bytes > supplied_bytes || header->slots_offset != 64u ||
        header->max_slots == 0 || header->reserved_zero != 0 ||
        header->max_slots > (header->actual_bytes - 64u) / 32u)
        return -3;

    if (simple_xray_thread_current_slot_v1 != NULL) {
        return simple_xray_thread_current_pool_v1 == header ? 1 : -4;
    }

    SimpleXrayThreadContextSlotV1 *slots =
        (SimpleXrayThreadContextSlotV1 *)((uint8_t *)pool + 64u);
    for (uint64_t i = 0; i < header->max_slots; ++i) {
        SimpleXrayThreadContextSlotV1 *slot = &slots[i];
        if (slot->arena == 0 || slot->bytes == 0 || slot->context_id == 0 ||
            (slot->arena & 7u) != 0 || slot->bytes > INT64_MAX ||
            slot->arena > (uint64_t)INT64_MAX - slot->bytes)
            return -3;
        uint64_t expected = SIMPLE_XRAY_THREAD_CONTEXT_UNUSED_V1;
        if (__atomic_compare_exchange_n(&slot->state, &expected,
                                        SIMPLE_XRAY_THREAD_CONTEXT_ATTACHED_V1,
                                        0, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
            simple_xray_thread_current_pool_v1 = header;
            simple_xray_thread_current_slot_v1 = slot;
            return 1;
        }
        if (expected != SIMPLE_XRAY_THREAD_CONTEXT_DETACHED_V1 &&
            expected != SIMPLE_XRAY_THREAD_CONTEXT_ATTACHED_V1)
            return -3;
    }
    return -2;
}

/* Idempotent only within the same immutable pool. A new pool/generation
 * requires explicit detach at a controlled boundary. This operation is
 * authorized after close: the TLS pool pointer remains process-lifetime
 * resident, and no descriptor is loaded or storage reclaimed here. */
static inline int64_t simple_xray_thread_detach_pool_v1(void) {
    SimpleXrayThreadContextSlotV1 *slot = simple_xray_thread_current_slot_v1;
    if (slot == NULL) {
        simple_xray_thread_current_pool_v1 = NULL;
        return 1;
    }
    simple_xray_thread_current_slot_v1 = NULL;
    simple_xray_thread_current_pool_v1 = NULL;
    __atomic_store_n(&slot->state, SIMPLE_XRAY_THREAD_CONTEXT_DETACHED_V1,
                     __ATOMIC_RELEASE);
    return 1;
}

/* The caller must hold provider writer admission until it is finished using
 * the returned arena. Null means unattached; no implicit attach is attempted. */
static inline int64_t simple_xray_thread_current_arena_v1(const void *pinned_pool) {
    if (pinned_pool == NULL ||
        simple_xray_thread_current_pool_v1 !=
            (const SimpleXrayThreadContextHeaderV1 *)pinned_pool)
        return 0;
    SimpleXrayThreadContextSlotV1 *slot = simple_xray_thread_current_slot_v1;
    if (slot == NULL) return 0;
    return (int64_t)slot->arena;
}

/* Bounded best-effort accounting for callbacks on an unattached thread.
 * Values 0..UINT64_MAX-1 are exact; UINT64_MAX is a sticky "count inexact;
 * numeric total unavailable" sentinel. Readers must not treat it as a
 * numeric lower bound or as evidence that capture was lossless. */
static inline void simple_xray_thread_note_unattached_v1(
    const SimpleXrayThreadContextHeaderV1 *header) {
    if (header == NULL) return;
    uint64_t *cell = (uint64_t *)((uint8_t *)header + SIMPLE_XRAY_CTX_H_UNATTACHED_LOST);
    uint64_t current = __atomic_load_n(cell, __ATOMIC_RELAXED);
    for (int attempt = 0; attempt < 8; ++attempt) {
        if (current == UINT64_MAX) return;
        uint64_t seen = current;
        if (__atomic_compare_exchange_n(cell, &seen, current + 1u, 0,
                                        __ATOMIC_RELAXED, __ATOMIC_RELAXED))
            return;
        current = seen;
    }
    __atomic_exchange_n(cell, UINT64_MAX, __ATOMIC_RELAXED);
}

#undef SIMPLE_XRAY_CONTEXT_TLS_V1

#endif /* SIMPLE_XRAY_THREAD_CONTEXT_V1_H */
