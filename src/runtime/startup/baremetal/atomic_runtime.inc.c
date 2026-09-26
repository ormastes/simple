/* Shared AArch64/RV64 SimpleOS atomic SFFI. Include after spl_i64, spl_u64,
 * rt_alloc, rt_special, and RT_VALUE_SPECIAL_{TRUE,FALSE} are defined.
 *
 * The typed Simple extern ABI carries integer arguments as raw i64 values.
 * Only bool accepts the two tagged RuntimeValue literals in addition to raw
 * 0/1; decoding an integer by its low tag bits would corrupt values like 8.
 * All operations use the compiler's freestanding sequentially consistent
 * hardware atomics. Handles are raw, aligned bump-allocation pointers. */
#ifndef SIMPLEOS_BAREMETAL_ATOMIC_RUNTIME_INC_C
#define SIMPLEOS_BAREMETAL_ATOMIC_RUNTIME_INC_C

static spl_i64 *simpleos_atomic_cell(spl_i64 handle) {
    return (spl_i64 *)(spl_u64)handle;
}

static spl_i64 simpleos_atomic_bool_arg(spl_i64 value) {
    if (value == rt_special(RT_VALUE_SPECIAL_FALSE)) return 0;
    if (value == rt_special(RT_VALUE_SPECIAL_TRUE)) return 1;
    return value != 0 ? 1 : 0;
}

spl_i64 rt_atomic_int_new(spl_i64 initial) {
    spl_i64 *cell = (spl_i64 *)rt_alloc((spl_i64)sizeof(spl_i64));
    if (!cell) return 0;
    __atomic_store_n(cell, initial, __ATOMIC_SEQ_CST);
    return (spl_i64)(spl_u64)cell;
}

spl_i64 rt_atomic_int_load(spl_i64 handle) {
    spl_i64 *cell = simpleos_atomic_cell(handle);
    return cell ? __atomic_load_n(cell, __ATOMIC_SEQ_CST) : 0;
}

void rt_atomic_int_store(spl_i64 handle, spl_i64 value) {
    spl_i64 *cell = simpleos_atomic_cell(handle);
    if (cell) __atomic_store_n(cell, value, __ATOMIC_SEQ_CST);
}

spl_i64 rt_atomic_int_swap(spl_i64 handle, spl_i64 value) {
    spl_i64 *cell = simpleos_atomic_cell(handle);
    return cell ? __atomic_exchange_n(cell, value, __ATOMIC_SEQ_CST) : 0;
}

spl_i64 rt_atomic_int_compare_exchange(spl_i64 handle, spl_i64 current,
                                       spl_i64 new_value) {
    spl_i64 *cell = simpleos_atomic_cell(handle);
    if (!cell) return 0;
    return __atomic_compare_exchange_n(cell, &current, new_value, 0,
                                        __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST) ? 1 : 0;
}

spl_i64 rt_atomic_int_fetch_add(spl_i64 handle, spl_i64 value) {
    spl_i64 *cell = simpleos_atomic_cell(handle);
    return cell ? __atomic_fetch_add(cell, value, __ATOMIC_SEQ_CST) : 0;
}

spl_i64 rt_atomic_int_fetch_sub(spl_i64 handle, spl_i64 value) {
    spl_i64 *cell = simpleos_atomic_cell(handle);
    return cell ? __atomic_fetch_sub(cell, value, __ATOMIC_SEQ_CST) : 0;
}

spl_i64 rt_atomic_int_fetch_and(spl_i64 handle, spl_i64 value) {
    spl_i64 *cell = simpleos_atomic_cell(handle);
    return cell ? __atomic_fetch_and(cell, value, __ATOMIC_SEQ_CST) : 0;
}

spl_i64 rt_atomic_int_fetch_or(spl_i64 handle, spl_i64 value) {
    spl_i64 *cell = simpleos_atomic_cell(handle);
    return cell ? __atomic_fetch_or(cell, value, __ATOMIC_SEQ_CST) : 0;
}

spl_i64 rt_atomic_int_fetch_xor(spl_i64 handle, spl_i64 value) {
    spl_i64 *cell = simpleos_atomic_cell(handle);
    return cell ? __atomic_fetch_xor(cell, value, __ATOMIC_SEQ_CST) : 0;
}

void rt_atomic_int_free(spl_i64 handle) {
    (void)handle; /* boot bump allocation is reclaimed with the image */
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
