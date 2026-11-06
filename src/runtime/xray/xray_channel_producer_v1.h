/*
 * xray_channel_producer_v1.h -- the one C producer of the V1 observer channel,
 * shared by the stage-1 LLVM handler (xray_llvm_adapter_linux.c, PR4) and the
 * stage-2 native trampoline handler (xray_native_registry_v1.h, PR5b/PR6).
 *
 * Simple twin: trace_native_channel_record_words_v1 in
 * src/lib/nogc_sync_mut/trace/observer_native_channel_v1.spl (same arena
 * layout, same gate CAS, same bounded loss counter, same record words). The
 * consumer stays Simple (trace_native_channel_poll_into_v1). Keep the two in
 * lockstep.
 *
 * Hot-path rules (plan section 7): no lock, no allocation, no libc call, no
 * syscall, no FP/vector use. Every function here is static inline so each
 * handler compiles to one leaf with no call out; the including TU is built
 * with -mgeneral-regs-only (+ -mno-outline-atomics on aarch64).
 */
#ifndef SIMPLE_XRAY_CHANNEL_PRODUCER_V1_H
#define SIMPLE_XRAY_CHANNEL_PRODUCER_V1_H

#include <stdint.h>

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

#if defined(__clang__)
#define SIMPLE_XRAY_NEVER_INSTRUMENT __attribute__((xray_never_instrument))
#else
#define SIMPLE_XRAY_NEVER_INSTRUMENT
#endif

SIMPLE_XRAY_NEVER_INSTRUMENT static inline int64_t simple_xray_cas(int64_t *cell, int64_t expected,
                                                                  int64_t value) {
    __atomic_compare_exchange_n(cell, &expected, value, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
    return expected; /* the observed old value, like rt_par_atomic_cmpxchg_i64 */
}

SIMPLE_XRAY_NEVER_INSTRUMENT static inline void simple_xray_loss(int64_t *base) {
    int64_t current = __atomic_load_n(&base[CH_LOST], __ATOMIC_SEQ_CST);
    for (int attempt = 0; attempt < 8; attempt++) {
        if (current == INT64_MAX) break;
        int64_t seen = simple_xray_cas(&base[CH_LOST], current, current + 1);
        if (seen == current) return;
        current = seen;
    }
    __atomic_exchange_n(&base[CH_LOSS_INEXACT], 1, __ATOMIC_SEQ_CST);
}

SIMPLE_XRAY_NEVER_INSTRUMENT static inline uint64_t simple_xray_timestamp(void) {
#if defined(__aarch64__)
    return (uint64_t)__builtin_arm_rsr64("cntvct_el0");
#elif defined(__x86_64__)
    return (uint64_t)__builtin_ia32_rdtsc();
#else
    return 0;
#endif
}

/* One record into a published, open arena. One gate CAS admits and
 * serializes the producer; a concurrent producer or a full ring counts loss
 * and returns. Never blocks, spins without bound, allocates or calls out.
 * `kind` is the TraceEventKindV1 code (1 entry, 2 exit, 3 tail exit);
 * `function_site` is function_id | site_id << 32. */
SIMPLE_XRAY_NEVER_INSTRUMENT static inline void simple_xray_channel_produce_v1(
    int64_t *base, uint64_t kind, uint64_t module_instance, uint64_t function_site,
    uint64_t *sequence_cell) {
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
    /* Taken only after admission, so drops leave no gaps. Monotonic per
     * sequence cell across generations (the stage-1 handler: one per process;
     * stage 2: one per --xray module runtime); per-context order is the V1
     * guarantee. */
    uint64_t sequence = __atomic_add_fetch(sequence_cell, 1, __ATOMIC_RELAXED);
    int64_t *slot = base + CH_HEADER_WORDS + (write % capacity) * CH_RECORD_WORDS;
    slot[0] = (int64_t)(CH_RECORD_HEADER | (kind << 32));
    slot[1] = base[CH_GENERATION];
    slot[2] = (int64_t)module_instance;
    slot[3] = (int64_t)function_site;
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

#endif /* SIMPLE_XRAY_CHANNEL_PRODUCER_V1_H */
