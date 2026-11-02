/* Self-check for rt_heap_aux_live_bytes / rt_heap_array_capacity_bytes in
 * runtime_native.c: container backing-buffer accounting (array element
 * buffers + dict entry tables). Allocating aux memory must raise the counter,
 * growing must raise it further, and freeing must return it to the baseline.
 *
 * Build + run (clang + lld only; Windows = llvm-mingw UCRT):
 *   clang -std=gnu11 -O1 -fuse-ld=lld -o build/rt_aux \
 *      src/runtime/test/rt_heap_aux_live_bytes_selfcheck.c \
 *      <core-C runtime archive: runtime_core_c_sources_v1 objects> && build/rt_aux
 */
#include <stdint.h>
#include <stdio.h>

#include "../runtime.h"

extern int64_t rt_heap_aux_live_bytes(void);
extern int64_t rt_heap_array_capacity_bytes(void);
extern int64_t rt_dict_new(int64_t cap_hint);
extern int8_t rt_dict_set(int64_t dict, int64_t key, int64_t value);
extern int64_t rt_dict_free_deep(int64_t dict);

static int failures = 0;

static void check(int cond, const char* what) {
    printf("  %s %s\n", cond ? "ok  " : "FAIL", what);
    if (!cond) failures++;
}

int main(void) {
    printf("rt_heap_aux_live_bytes selfcheck\n");
    int64_t base_aux = rt_heap_aux_live_bytes();
    int64_t base_cap = rt_heap_array_capacity_bytes();
    check(base_aux >= 0, "baseline aux bytes non-negative");
    check(base_cap >= 0 && base_cap <= base_aux, "array capacity is a subset of aux");

    /* 1. A fresh array allocates a backing buffer (min cap 4 x i64). */
    SplArray* a = rt_array_new(0);
    check(a != NULL, "array allocated");
    int64_t after_new = rt_heap_aux_live_bytes();
    check(after_new >= base_aux + 4 * (int64_t)sizeof(int64_t), "array create raises aux by >= 32 bytes");
    check(rt_heap_array_capacity_bytes() - base_cap == after_new - base_aux,
          "array create raises capacity bytes by the same amount");

    /* 2. Growth (realloc) raises it further. */
    for (int64_t i = 0; i < 1000; i++) rt_array_push(a, i);
    int64_t after_grow = rt_heap_aux_live_bytes();
    check(after_grow >= base_aux + 1000 * (int64_t)sizeof(int64_t), "push x1000 raises aux to >= 8000 bytes");
    check(after_grow > after_new, "growth strictly increases aux");

    /* 3. Free returns array bytes to the baseline. */
    rt_array_free(a);
    check(rt_heap_aux_live_bytes() == base_aux, "array free restores aux baseline");
    check(rt_heap_array_capacity_bytes() == base_cap, "array free restores capacity baseline");

    /* 4. Dict entry tables are aux bytes but not array capacity. */
    int64_t d = rt_dict_new(0);
    check(d != 0, "dict allocated");
    int64_t after_dict = rt_heap_aux_live_bytes();
    check(after_dict > base_aux, "dict create raises aux");
    check(rt_heap_array_capacity_bytes() == base_cap, "dict create leaves array capacity alone");
    for (int64_t i = 0; i < 200; i++) rt_dict_set(d, (i + 1) << 3, i << 3); /* tagged ints */
    check(rt_heap_aux_live_bytes() > after_dict, "dict resize raises aux");
    rt_dict_free_deep(d);
    check(rt_heap_aux_live_bytes() == base_aux, "dict free restores aux baseline");

    printf("%s (%d failures)\n", failures ? "FAIL" : "PASS", failures);
    return failures ? 1 : 0;
}
