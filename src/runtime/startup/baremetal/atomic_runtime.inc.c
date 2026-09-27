/* Shared AArch64/RV64 SimpleOS atomic SFFI. Include after spl_i64, spl_u64,
 * rt_special, and RT_VALUE_SPECIAL_{TRUE,FALSE} are defined.
 *
 * Typed Simple integer arguments are raw i64. Bool also accepts codegen's
 * tagged literals. The platform-neutral slot owner below owns lifetime and
 * hardware atomics; these wrappers preserve the public freestanding ABI. */
#ifndef SIMPLEOS_BAREMETAL_ATOMIC_RUNTIME_INC_C
#define SIMPLEOS_BAREMETAL_ATOMIC_RUNTIME_INC_C

#include "atomic_slot_owner.inc.c"

static spl_i64 simpleos_atomic_bool_arg(spl_i64 value) {
    if (value == rt_special(RT_VALUE_SPECIAL_FALSE)) return 0;
    if (value == rt_special(RT_VALUE_SPECIAL_TRUE)) return 1;
    return value != 0 ? 1 : 0;
}

spl_i64 rt_atomic_int_new(spl_i64 initial) {
    return simpleos_atomic_core_new(initial);
}

spl_i64 rt_atomic_int_load(spl_i64 handle) {
    return simpleos_atomic_core_load(handle);
}

void rt_atomic_int_store(spl_i64 handle, spl_i64 value) {
    simpleos_atomic_core_store(handle, value);
}

spl_i64 rt_atomic_int_swap(spl_i64 handle, spl_i64 value) {
    return simpleos_atomic_core_swap(handle, value);
}

spl_i64 rt_atomic_int_compare_exchange(spl_i64 handle, spl_i64 current,
                                       spl_i64 new_value) {
    return simpleos_atomic_core_compare_exchange(handle, current, new_value);
}

spl_i64 rt_atomic_int_fetch_add(spl_i64 handle, spl_i64 value) {
    return simpleos_atomic_core_fetch_add(handle, value);
}

spl_i64 rt_atomic_int_fetch_sub(spl_i64 handle, spl_i64 value) {
    return simpleos_atomic_core_fetch_sub(handle, value);
}

spl_i64 rt_atomic_int_fetch_and(spl_i64 handle, spl_i64 value) {
    return simpleos_atomic_core_fetch_and(handle, value);
}

spl_i64 rt_atomic_int_fetch_or(spl_i64 handle, spl_i64 value) {
    return simpleos_atomic_core_fetch_or(handle, value);
}

spl_i64 rt_atomic_int_fetch_xor(spl_i64 handle, spl_i64 value) {
    return simpleos_atomic_core_fetch_xor(handle, value);
}

void rt_atomic_int_free(spl_i64 handle) {
    simpleos_atomic_core_free(handle);
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
