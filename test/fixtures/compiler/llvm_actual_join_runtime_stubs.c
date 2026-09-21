#include <stdint.h>

static uintptr_t tls_value;
static int64_t close_call_count;
static int64_t close_last_handle = -1;

int64_t rt_current_task_id(void) { return 41; }
int64_t rt_thread_local_new(void) { return 1; }
uintptr_t rt_thread_local_get(int64_t tls) { (void)tls; return tls_value; }
void rt_thread_local_set(int64_t tls, uintptr_t value) { (void)tls; tls_value = value; }
int64_t rt_hal_unavailable_spawn(void) { return -1; }
int64_t rt_hal_unavailable_join(void) { return 0; }
int64_t rt_hal_unavailable_cancel(void) { return 0; }
int64_t rt_hal_unavailable_effect(void) { return 0; }

int64_t fixture_close_probe(int64_t handle) {
    close_call_count += 1;
    close_last_handle = handle;
    return 0;
}

int64_t fixture_close_probe_count(void) { return close_call_count; }
int64_t fixture_close_probe_last_handle(void) { return close_last_handle; }
