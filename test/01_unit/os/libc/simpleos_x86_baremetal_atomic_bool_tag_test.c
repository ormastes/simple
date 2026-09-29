/* The x86 bare-metal bool SFFI accepts raw 0/1 and codegen's tagged literals. */
#include <stdint.h>

typedef int64_t RuntimeValue;
extern RuntimeValue rt_atomic_bool_new(RuntimeValue initial);
extern RuntimeValue rt_atomic_bool_load(RuntimeValue handle);
extern RuntimeValue rt_atomic_bool_store(RuntimeValue handle, RuntimeValue value);
extern RuntimeValue rt_atomic_bool_swap(RuntimeValue handle, RuntimeValue value);
extern RuntimeValue rt_atomic_bool_compare_exchange(RuntimeValue handle,
                                                    RuntimeValue current,
                                                    RuntimeValue new_value);
extern RuntimeValue rt_atomic_bool_fetch_and(RuntimeValue handle, RuntimeValue value);
extern RuntimeValue rt_atomic_bool_fetch_or(RuntimeValue handle, RuntimeValue value);
extern RuntimeValue rt_atomic_bool_fetch_not(RuntimeValue handle);

enum { TAGGED_TRUE = 11, TAGGED_FALSE = 19 };

int main(void) {
    RuntimeValue flag = rt_atomic_bool_new(TAGGED_FALSE);
    if (!flag || rt_atomic_bool_load(flag)) return 1;
    rt_atomic_bool_store(flag, TAGGED_TRUE);
    if (!rt_atomic_bool_load(flag)) return 2;
    if (!rt_atomic_bool_swap(flag, TAGGED_FALSE) || rt_atomic_bool_load(flag)) return 3;
    if (!rt_atomic_bool_compare_exchange(flag, TAGGED_FALSE, TAGGED_TRUE)) return 4;
    if (!rt_atomic_bool_fetch_and(flag, TAGGED_FALSE) || rt_atomic_bool_load(flag)) return 5;
    if (rt_atomic_bool_fetch_or(flag, 1) || !rt_atomic_bool_load(flag)) return 6;
    if (!rt_atomic_bool_fetch_not(flag) || rt_atomic_bool_load(flag)) return 7;
    return 0;
}
