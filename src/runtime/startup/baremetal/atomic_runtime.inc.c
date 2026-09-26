/* Shared AArch64/RV64 SimpleOS atomic SFFI. Include after spl_i64, spl_u64,
 * rt_special, and RT_VALUE_SPECIAL_{TRUE,FALSE} are defined.
 *
 * The typed Simple extern ABI carries integer arguments as raw i64 values.
 * Only bool accepts the two tagged RuntimeValue literals in addition to raw
 * 0/1; decoding an integer by its low tag bits would corrupt values like 8.
 * All operations use the compiler's freestanding sequentially consistent
 * hardware atomics. This module owns a bounded, static cell table. A handle
 * is a one-based slot id, never a pointer; slots are not reused during boot.
 * Free revokes admission, while already admitted operations finish safely
 * against their retained slot. Invalid/stale loads and fetches return zero,
 * CAS returns false, and stores/frees are no-ops. */
#ifndef SIMPLEOS_BAREMETAL_ATOMIC_RUNTIME_INC_C
#define SIMPLEOS_BAREMETAL_ATOMIC_RUNTIME_INC_C

#define SIMPLEOS_ATOMIC_SLOT_CAPACITY 4096ULL

typedef struct {
    spl_i64 value;
    /* Odd means open; each admitted use adds two. Free clears the low bit. */
    spl_u64 lease_state;
} SimpleOSAtomicSlot;

static SimpleOSAtomicSlot simpleos_atomic_slots[SIMPLEOS_ATOMIC_SLOT_CAPACITY];
static spl_u64 simpleos_atomic_next_slot;

static SimpleOSAtomicSlot *simpleos_atomic_slot(spl_i64 handle) {
    if (handle <= 0 || (spl_u64)handle > SIMPLEOS_ATOMIC_SLOT_CAPACITY)
        return (SimpleOSAtomicSlot *)0;
    return &simpleos_atomic_slots[(spl_u64)handle - 1ULL];
}

static SimpleOSAtomicSlot *simpleos_atomic_acquire(spl_i64 handle) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_slot(handle);
    if (!slot) return (SimpleOSAtomicSlot *)0;
    spl_u64 state = __atomic_load_n(&slot->lease_state, __ATOMIC_SEQ_CST);
    while (state & 1ULL) {
        if (state > (~(spl_u64)0) - 2ULL)
            return (SimpleOSAtomicSlot *)0;
        if (__atomic_compare_exchange_n(&slot->lease_state, &state, state + 2ULL,
                                        0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST))
            return slot;
    }
    return (SimpleOSAtomicSlot *)0;
}

static void simpleos_atomic_release(SimpleOSAtomicSlot *slot) {
    __atomic_fetch_sub(&slot->lease_state, 2ULL, __ATOMIC_SEQ_CST);
}

static spl_i64 simpleos_atomic_bool_arg(spl_i64 value) {
    if (value == rt_special(RT_VALUE_SPECIAL_FALSE)) return 0;
    if (value == rt_special(RT_VALUE_SPECIAL_TRUE)) return 1;
    return value != 0 ? 1 : 0;
}

spl_i64 rt_atomic_int_new(spl_i64 initial) {
    spl_u64 index = __atomic_load_n(&simpleos_atomic_next_slot, __ATOMIC_SEQ_CST);
    for (;;) {
        if (index >= SIMPLEOS_ATOMIC_SLOT_CAPACITY) return 0;
        if (__atomic_compare_exchange_n(&simpleos_atomic_next_slot, &index,
                                        index + 1ULL, 0,
                                        __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST))
            break;
    }
    SimpleOSAtomicSlot *slot = &simpleos_atomic_slots[index];
    __atomic_store_n(&slot->value, initial, __ATOMIC_SEQ_CST);
    __atomic_store_n(&slot->lease_state, 1ULL, __ATOMIC_SEQ_CST);
    return (spl_i64)(index + 1ULL);
}

spl_i64 rt_atomic_int_load(spl_i64 handle) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_acquire(handle);
    if (!slot) return 0;
    spl_i64 result = __atomic_load_n(&slot->value, __ATOMIC_SEQ_CST);
    simpleos_atomic_release(slot);
    return result;
}

void rt_atomic_int_store(spl_i64 handle, spl_i64 value) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_acquire(handle);
    if (!slot) return;
    __atomic_store_n(&slot->value, value, __ATOMIC_SEQ_CST);
    simpleos_atomic_release(slot);
}

spl_i64 rt_atomic_int_swap(spl_i64 handle, spl_i64 value) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_acquire(handle);
    if (!slot) return 0;
    spl_i64 result = __atomic_exchange_n(&slot->value, value, __ATOMIC_SEQ_CST);
    simpleos_atomic_release(slot);
    return result;
}

spl_i64 rt_atomic_int_compare_exchange(spl_i64 handle, spl_i64 current,
                                       spl_i64 new_value) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_acquire(handle);
    if (!slot) return 0;
    spl_i64 result = __atomic_compare_exchange_n(&slot->value, &current,
        new_value, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST) ? 1 : 0;
    simpleos_atomic_release(slot);
    return result;
}

spl_i64 rt_atomic_int_fetch_add(spl_i64 handle, spl_i64 value) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_acquire(handle);
    if (!slot) return 0;
    spl_i64 result = __atomic_fetch_add(&slot->value, value, __ATOMIC_SEQ_CST);
    simpleos_atomic_release(slot);
    return result;
}

spl_i64 rt_atomic_int_fetch_sub(spl_i64 handle, spl_i64 value) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_acquire(handle);
    if (!slot) return 0;
    spl_i64 result = __atomic_fetch_sub(&slot->value, value, __ATOMIC_SEQ_CST);
    simpleos_atomic_release(slot);
    return result;
}

spl_i64 rt_atomic_int_fetch_and(spl_i64 handle, spl_i64 value) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_acquire(handle);
    if (!slot) return 0;
    spl_i64 result = __atomic_fetch_and(&slot->value, value, __ATOMIC_SEQ_CST);
    simpleos_atomic_release(slot);
    return result;
}

spl_i64 rt_atomic_int_fetch_or(spl_i64 handle, spl_i64 value) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_acquire(handle);
    if (!slot) return 0;
    spl_i64 result = __atomic_fetch_or(&slot->value, value, __ATOMIC_SEQ_CST);
    simpleos_atomic_release(slot);
    return result;
}

spl_i64 rt_atomic_int_fetch_xor(spl_i64 handle, spl_i64 value) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_acquire(handle);
    if (!slot) return 0;
    spl_i64 result = __atomic_fetch_xor(&slot->value, value, __ATOMIC_SEQ_CST);
    simpleos_atomic_release(slot);
    return result;
}

void rt_atomic_int_free(spl_i64 handle) {
    SimpleOSAtomicSlot *slot = simpleos_atomic_slot(handle);
    if (!slot) return;
    spl_u64 state = __atomic_load_n(&slot->lease_state, __ATOMIC_SEQ_CST);
    while (state & 1ULL) {
        if (__atomic_compare_exchange_n(&slot->lease_state, &state,
                                        state - 1ULL, 0,
                                        __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST))
            return;
    }
}

spl_i64 rt_atomic_bool_new(spl_i64 initial) {
    return rt_atomic_int_new(simpleos_atomic_bool_arg(initial));
}

spl_i64 rt_atomic_bool_load(spl_i64 handle) {
    return rt_atomic_int_load(handle) != 0 ? 1 : 0;
}

void rt_atomic_bool_store(spl_i64 handle, spl_i64 value) {
    rt_atomic_int_store(handle, simpleos_atomic_bool_arg(value));
}

spl_i64 rt_atomic_bool_swap(spl_i64 handle, spl_i64 value) {
    return rt_atomic_int_swap(handle, simpleos_atomic_bool_arg(value)) != 0 ? 1 : 0;
}

spl_i64 rt_atomic_bool_compare_exchange(spl_i64 handle, spl_i64 current,
                                        spl_i64 new_value) {
    return rt_atomic_int_compare_exchange(handle,
        simpleos_atomic_bool_arg(current), simpleos_atomic_bool_arg(new_value));
}

spl_i64 rt_atomic_bool_fetch_and(spl_i64 handle, spl_i64 value) {
    return rt_atomic_int_fetch_and(handle, simpleos_atomic_bool_arg(value)) != 0 ? 1 : 0;
}

spl_i64 rt_atomic_bool_fetch_or(spl_i64 handle, spl_i64 value) {
    return rt_atomic_int_fetch_or(handle, simpleos_atomic_bool_arg(value)) != 0 ? 1 : 0;
}

spl_i64 rt_atomic_bool_fetch_not(spl_i64 handle) {
    return rt_atomic_int_fetch_xor(handle, 1) != 0 ? 1 : 0;
}

void rt_atomic_bool_free(spl_i64 handle) {
    rt_atomic_int_free(handle);
}

#endif
