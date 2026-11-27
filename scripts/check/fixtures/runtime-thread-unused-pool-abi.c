/* Unrelated exported pool ABI dependencies must never run in this fixture. */
#include <stdint.h>
#include <stdlib.h>
int64_t spl_thread_cpu_count(void) { abort(); }
int64_t rt_closure_func_ptr(int64_t value) { (void)value; abort(); }
int64_t rt_closure_retain(int64_t value) { (void)value; abort(); }
int64_t rt_closure_release(int64_t value) { (void)value; abort(); }
int64_t rt_value_int(int64_t value) { (void)value; abort(); }
int64_t rt_value_unbox_int(int64_t value) { (void)value; abort(); }
