/* Real core-C provider regression for Draw IR allocation evidence.
 * Link against the canonical core-C runtime sources/defines, with no stubs. */
#include "runtime.h"
#include <stdint.h>
#include <stdio.h>

#define CHECK(expr) do { \
    checks++; \
    if (!(expr)) { \
        fprintf(stderr, "FAIL heap collection counters line=%d check=%d\n", __LINE__, checks); \
        return 1; \
    } \
} while (0)

int main(void) {
    int checks = 0;
    const int64_t before = rt_heap_alloc_count();
    const int64_t capacity = rt_heap_array_capacity_bytes();
    CHECK(before >= 0);
    CHECK(capacity >= 0);
    SplArray *array = rt_array_new(8);
    CHECK(array != NULL);
    CHECK(rt_heap_alloc_count() == before + 1);
    CHECK(rt_heap_array_capacity_bytes() == capacity + 8 * (int64_t)sizeof(int64_t));
    for (int64_t i = 0; i < 8; i++) CHECK(rt_array_push(array, rt_value_int(i + 11)));
    CHECK(rt_heap_alloc_count() == before + 1);
    CHECK(rt_heap_array_capacity_bytes() == capacity + 8 * (int64_t)sizeof(int64_t));
    CHECK(rt_array_push(array, rt_value_int(99)));
    CHECK(rt_heap_alloc_count() == before + 1);
    CHECK(rt_heap_array_capacity_bytes() == capacity + 16 * (int64_t)sizeof(int64_t));
    CHECK(rt_array_len(array) == 9);
    rt_array_free(array);
    CHECK(rt_heap_alloc_count() == before + 1); /* Cannot alias the live count. */
    CHECK(rt_heap_array_capacity_bytes() == capacity);

    SplArray *bytes = rt_byte_array_new(8);
    CHECK(bytes != NULL);
    CHECK(rt_heap_alloc_count() == before + 2);
    CHECK(rt_heap_array_capacity_bytes() == capacity + 8); /* Byte capacity, not slots. */
    rt_array_free(bytes);
    CHECK(rt_heap_alloc_count() == before + 2);
    CHECK(rt_heap_array_capacity_bytes() == capacity);

    SplArray *many[512];
    for (int i = 0; i < 512; i++) {
        many[i] = rt_array_new(4);
        CHECK(many[i] != NULL);
    }
    CHECK(rt_heap_alloc_count() == before + 514); /* Registry rehash is not an object. */
    CHECK(rt_heap_array_capacity_bytes() == capacity + 512 * 4 * (int64_t)sizeof(int64_t));
    for (int i = 0; i < 100; i++) {
        CHECK(rt_heap_alloc_count() == before + 514); /* Observation cannot allocate. */
        CHECK(rt_heap_array_capacity_bytes() == capacity + 512 * 4 * (int64_t)sizeof(int64_t));
    }
    for (int i = 0; i < 512; i++) rt_array_free(many[i]);
    CHECK(rt_heap_alloc_count() == before + 514);
    CHECK(rt_heap_array_capacity_bytes() == capacity);
    CHECK(rt_array_new(INT64_MAX) == NULL); /* Invalid capacity is rejected before allocation. */
    CHECK(rt_heap_alloc_count() == before + 514);
    CHECK(rt_heap_array_capacity_bytes() == capacity);
    if (checks != 745) {
        fprintf(stderr, "FAIL unexpected counter check count %d\n", checks);
        return 1;
    }
    printf("PASS heap_collection_counters checks=%d\n", checks);
    return 0;
}
