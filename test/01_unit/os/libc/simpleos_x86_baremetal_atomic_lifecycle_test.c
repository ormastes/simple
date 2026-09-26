/* x86 wrapper parity for the shared freestanding atomic slot owner. */
#include <stdint.h>

typedef int64_t RuntimeValue;
extern RuntimeValue rt_atomic_int_new(RuntimeValue initial);
extern RuntimeValue rt_atomic_int_load(RuntimeValue handle);
extern RuntimeValue rt_atomic_int_store(RuntimeValue handle, RuntimeValue value);
extern RuntimeValue rt_atomic_int_compare_exchange(RuntimeValue handle,
                                                    RuntimeValue expected,
                                                    RuntimeValue desired);
extern RuntimeValue rt_atomic_int_free(RuntimeValue handle);
extern RuntimeValue rt_atomic_bool_new(RuntimeValue initial);
extern RuntimeValue rt_atomic_bool_load(RuntimeValue handle);
extern RuntimeValue rt_atomic_bool_fetch_not(RuntimeValue handle);
extern RuntimeValue rt_atomic_bool_free(RuntimeValue handle);

enum { SLOT_CAPACITY = 4096, TAGGED_FALSE = 19 };

int main(void) {
    RuntimeValue first = rt_atomic_int_new(8);
    if (!first || rt_atomic_int_load(first) != 8) return 1;
    if (rt_atomic_int_load(-1) != 0 ||
        rt_atomic_int_load(INT64_MAX) != 0) return 2;
    rt_atomic_int_free(first);
    rt_atomic_int_store(first, 99);
    if (rt_atomic_int_load(first) != 0 ||
        rt_atomic_int_compare_exchange(first, 8, 99) != 0) return 3;

    RuntimeValue flag = rt_atomic_bool_new(TAGGED_FALSE);
    if (!flag || rt_atomic_bool_load(flag) != 0) return 4;
    rt_atomic_bool_free(flag);
    if (rt_atomic_bool_load(flag) != 0 ||
        rt_atomic_bool_fetch_not(flag) != 0) return 5;

    RuntimeValue live = rt_atomic_int_new(33);
    if (!live || rt_atomic_int_load(live) != 33) return 6;
    int created = 0;
    while (created <= SLOT_CAPACITY) {
        if (!rt_atomic_int_new(0)) break;
        created++;
    }
    if (created > SLOT_CAPACITY || rt_atomic_int_new(0) != 0) return 7;
    rt_atomic_int_free(live);
    RuntimeValue reused = rt_atomic_int_new(44);
    if (!reused || reused == live || rt_atomic_int_load(live) != 0 ||
        rt_atomic_int_load(reused) != 44) return 8;
    if (rt_atomic_int_new(0) != 0) return 9;
    return 0;
}
