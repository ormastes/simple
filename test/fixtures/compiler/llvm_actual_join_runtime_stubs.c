#include <stdint.h>

static uintptr_t tls_value;

int64_t rt_current_task_id(void) { return 41; }
int64_t rt_thread_local_new(void) { return 1; }
uintptr_t rt_thread_local_get(int64_t tls) { (void)tls; return tls_value; }
void rt_thread_local_set(int64_t tls, uintptr_t value) { (void)tls; tls_value = value; }
int64_t rt_hal_unavailable_spawn(void) { return -1; }
int64_t rt_hal_unavailable_join(void) { return 0; }
int64_t rt_hal_unavailable_cancel(void) { return 0; }
int64_t rt_hal_unavailable_effect(void) { return 0; }
