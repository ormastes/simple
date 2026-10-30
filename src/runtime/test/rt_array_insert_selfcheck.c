/* Self-check for rt_array_insert (C lane twin of the Rust runtime's
 * value/collections.rs rt_array_insert).
 *
 * Contract: insert BEFORE index in place; index == len appends; a negative
 * index or index > len is a no-op returning 0 (matches the interpreter's
 * `insert` arm, which leaves the array unchanged for idx > len).
 *
 * Build + run (clang only):
 *   clang -std=gnu11 -O1 -w -Wl,-z,muldefs -o /tmp/rtai \
 *     src/runtime/test/rt_array_insert_selfcheck.c \
 *     $(ls src/runtime/[a-z]*.c | grep -vE \
 *       'hosted_cocoa|hosted_win32|directx|openssl|wasm|audio|font|image|sdl2|runtime_time') \
 *     -lm -lpthread -ldl && /tmp/rtai
 */
#include <stdio.h>
#include <stdint.h>

typedef struct SplArray SplArray;

extern SplArray* rt_array_new(int64_t cap);
extern int8_t rt_array_push(SplArray* a, int64_t val);
extern int64_t rt_array_len(SplArray* a);
extern int64_t rt_array_get(SplArray* a, int64_t idx);
extern int64_t rt_value_int(int64_t v);
extern int8_t rt_array_insert(int64_t array_value, int64_t index, int64_t value);

static int failures = 0;
#define CHECK(c, m) do { if (!(c)) { printf("FAIL: %s\n", m); failures++; } } while (0)

static int expect(SplArray* a, const int64_t* xs, int64_t n) {
    if (rt_array_len(a) != n) return 0;
    for (int64_t i = 0; i < n; i++)
        if (rt_array_get(a, i) != rt_value_int(xs[i])) return 0;
    return 1;
}

int main(void) {
    SplArray* a = rt_array_new(0);
    int64_t h = (int64_t)(uintptr_t)a;
    rt_array_push(a, rt_value_int(1));
    rt_array_push(a, rt_value_int(3));

    CHECK(rt_array_insert(h, 1, rt_value_int(2)) == 1, "middle insert returns 1");
    { int64_t e[] = {1, 2, 3}; CHECK(expect(a, e, 3), "middle insert order"); }
    CHECK(rt_array_insert(h, 0, rt_value_int(0)) == 1, "front insert returns 1");
    CHECK(rt_array_insert(h, 4, rt_value_int(4)) == 1, "index == len appends");
    { int64_t e[] = {0, 1, 2, 3, 4}; CHECK(expect(a, e, 5), "front + append order"); }
    CHECK(rt_array_insert(h, 6, rt_value_int(9)) == 0, "index > len is a no-op");
    CHECK(rt_array_insert(h, -1, rt_value_int(9)) == 0, "negative index is a no-op");
    CHECK(rt_array_len(a) == 5, "no-ops leave length unchanged");
    CHECK(rt_array_insert(0, 0, rt_value_int(9)) == 0, "non-array receiver refused");

    if (failures == 0) printf("PASS rt_array_insert_selfcheck\n");
    return failures == 0 ? 0 : 1;
}
