/* Freestanding SimpleOS owner for atomic cells on x86_64, AArch64, and RV64.
 * The including runtime defines spl_i64 and spl_u64. No heap or libc is used.
 *
 * Handles encode (generation, slot). Admission pins a slot before touching its
 * value. Free closes admission; a slot is reused only after all admitted uses
 * drain. The generation check after admission rejects a stale handle that
 * raced through close and reuse, without dereferencing an external pointer. */
#ifndef SIMPLEOS_ATOMIC_SLOT_OWNER_INC_C
#define SIMPLEOS_ATOMIC_SLOT_OWNER_INC_C

#define SIMPLEOS_ATOMIC_SLOT_BITS 12ULL
#define SIMPLEOS_ATOMIC_SLOT_CAPACITY (1ULL << SIMPLEOS_ATOMIC_SLOT_BITS)
#define SIMPLEOS_ATOMIC_SLOT_MASK (SIMPLEOS_ATOMIC_SLOT_CAPACITY - 1ULL)
#define SIMPLEOS_ATOMIC_MAX_GENERATION \
    (0x7fffffffffffffffULL >> SIMPLEOS_ATOMIC_SLOT_BITS)

typedef struct {
    spl_i64 value;
    spl_u64 generation;
    /* Odd = open, even = closed. Each admitted use adds two. Two alone is a
     * reservation during construction; zero is available for reuse. */
    spl_u64 lease_state;
} SimpleOSAtomicSlot;

static SimpleOSAtomicSlot simpleos_atomic_slots[SIMPLEOS_ATOMIC_SLOT_CAPACITY];
static spl_u64 simpleos_atomic_next_hint;

static void simpleos_atomic_core_release(SimpleOSAtomicSlot *slot) {
    __atomic_fetch_sub(&slot->lease_state, 2ULL, __ATOMIC_SEQ_CST);
}

static SimpleOSAtomicSlot *simpleos_atomic_core_slot(
    spl_i64 handle, spl_u64 *generation
) {
    if (handle <= 0) return (SimpleOSAtomicSlot *)0;
    spl_u64 raw = (spl_u64)handle;
    spl_u64 actual_generation = raw >> SIMPLEOS_ATOMIC_SLOT_BITS;
    if (actual_generation == 0 ||
        actual_generation > SIMPLEOS_ATOMIC_MAX_GENERATION)
        return (SimpleOSAtomicSlot *)0;
    *generation = actual_generation;
    return &simpleos_atomic_slots[raw & SIMPLEOS_ATOMIC_SLOT_MASK];
}

static SimpleOSAtomicSlot *simpleos_atomic_core_acquire(spl_i64 handle) {
    spl_u64 generation = 0;
    SimpleOSAtomicSlot *slot = simpleos_atomic_core_slot(handle, &generation);
    if (!slot || __atomic_load_n(&slot->generation, __ATOMIC_SEQ_CST) != generation)
        return (SimpleOSAtomicSlot *)0;
    spl_u64 state = __atomic_load_n(&slot->lease_state, __ATOMIC_SEQ_CST);
    while (state & 1ULL) {
        if (state > (~(spl_u64)0) - 2ULL)
            return (SimpleOSAtomicSlot *)0;
        if (__atomic_compare_exchange_n(&slot->lease_state, &state,
                                        state + 2ULL, 0,
                                        __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST)) {
            if (__atomic_load_n(&slot->generation, __ATOMIC_SEQ_CST) == generation)
                return slot;
            simpleos_atomic_core_release(slot);
            return (SimpleOSAtomicSlot *)0;
        }
    }
    return (SimpleOSAtomicSlot *)0;
}

static spl_i64 simpleos_atomic_core_new(spl_i64 initial) {
    spl_u64 start = __atomic_fetch_add(&simpleos_atomic_next_hint, 1ULL,
                                      __ATOMIC_SEQ_CST);
    spl_u64 step = 0;
    while (step < SIMPLEOS_ATOMIC_SLOT_CAPACITY) {
        spl_u64 index = (start + step) & SIMPLEOS_ATOMIC_SLOT_MASK;
        SimpleOSAtomicSlot *slot = &simpleos_atomic_slots[index];
        spl_u64 expected = 0;
        if (__atomic_compare_exchange_n(&slot->lease_state, &expected, 2ULL, 0,
                                        __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST)) {
            spl_u64 old_generation = __atomic_load_n(&slot->generation,
                                                     __ATOMIC_SEQ_CST);
            if (old_generation < SIMPLEOS_ATOMIC_MAX_GENERATION) {
                spl_u64 generation = old_generation + 1ULL;
                __atomic_store_n(&slot->value, initial, __ATOMIC_SEQ_CST);
                __atomic_store_n(&slot->generation, generation, __ATOMIC_SEQ_CST);
                __atomic_store_n(&slot->lease_state, 1ULL, __ATOMIC_SEQ_CST);
                return (spl_i64)((generation << SIMPLEOS_ATOMIC_SLOT_BITS) | index);
            }
            __atomic_store_n(&slot->lease_state, 0ULL, __ATOMIC_SEQ_CST);
        }
        step++;
    }
    return 0;
}

static spl_i64 simpleos_atomic_core_load(spl_i64 handle) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_core_acquire(handle);
    if (!slot) return 0;
    spl_i64 result = __atomic_load_n(&slot->value, __ATOMIC_SEQ_CST);
    simpleos_atomic_core_release(slot);
    return result;
}

static void simpleos_atomic_core_store(spl_i64 handle, spl_i64 value) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_core_acquire(handle);
    if (!slot) return;
    __atomic_store_n(&slot->value, value, __ATOMIC_SEQ_CST);
    simpleos_atomic_core_release(slot);
}

static spl_i64 simpleos_atomic_core_swap(spl_i64 handle, spl_i64 value) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_core_acquire(handle);
    if (!slot) return 0;
    spl_i64 result = __atomic_exchange_n(&slot->value, value, __ATOMIC_SEQ_CST);
    simpleos_atomic_core_release(slot);
    return result;
}

static spl_i64 simpleos_atomic_core_compare_exchange(
    spl_i64 handle, spl_i64 current, spl_i64 new_value
) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_core_acquire(handle);
    if (!slot) return 0;
    spl_i64 result = __atomic_compare_exchange_n(&slot->value, &current,
        new_value, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST) ? 1 : 0;
    simpleos_atomic_core_release(slot);
    return result;
}

static spl_i64 simpleos_atomic_core_fetch_add(spl_i64 handle, spl_i64 value) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_core_acquire(handle);
    if (!slot) return 0;
    spl_i64 result = __atomic_fetch_add(&slot->value, value, __ATOMIC_SEQ_CST);
    simpleos_atomic_core_release(slot);
    return result;
}

static spl_i64 simpleos_atomic_core_fetch_sub(spl_i64 handle, spl_i64 value) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_core_acquire(handle);
    if (!slot) return 0;
    spl_i64 result = __atomic_fetch_sub(&slot->value, value, __ATOMIC_SEQ_CST);
    simpleos_atomic_core_release(slot);
    return result;
}

static spl_i64 simpleos_atomic_core_fetch_and(spl_i64 handle, spl_i64 value) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_core_acquire(handle);
    if (!slot) return 0;
    spl_i64 result = __atomic_fetch_and(&slot->value, value, __ATOMIC_SEQ_CST);
    simpleos_atomic_core_release(slot);
    return result;
}

static spl_i64 simpleos_atomic_core_fetch_or(spl_i64 handle, spl_i64 value) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_core_acquire(handle);
    if (!slot) return 0;
    spl_i64 result = __atomic_fetch_or(&slot->value, value, __ATOMIC_SEQ_CST);
    simpleos_atomic_core_release(slot);
    return result;
}

static spl_i64 simpleos_atomic_core_fetch_xor(spl_i64 handle, spl_i64 value) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_core_acquire(handle);
    if (!slot) return 0;
    spl_i64 result = __atomic_fetch_xor(&slot->value, value, __ATOMIC_SEQ_CST);
    simpleos_atomic_core_release(slot);
    return result;
}

static void simpleos_atomic_core_free(spl_i64 handle) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_core_acquire(handle);
    if (!slot) return;
    spl_u64 state = __atomic_load_n(&slot->lease_state, __ATOMIC_SEQ_CST);
    while (state & 1ULL) {
        if (__atomic_compare_exchange_n(&slot->lease_state, &state,
                                        state - 1ULL, 0,
                                        __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST))
            break;
    }
    simpleos_atomic_core_release(slot);
}

#endif
