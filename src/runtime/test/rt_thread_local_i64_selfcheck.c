/* rt_thread_local_{get,set}_i64 must round-trip full 64-bit values on every
 * target, including 32-bit ones (i686 Windows), where the TLS slot is 4 bytes. */
#include <stdint.h>
#include <stdio.h>

int64_t rt_thread_local_new(void);
int64_t rt_thread_local_get_i64(int64_t handle);
void rt_thread_local_set_i64(int64_t handle, int64_t value);

/* Link stubs: runtime_thread.c references these, but the scalar TLS path
 * exercised here never calls them. */
int g_memtrack_enabled = 0;
int64_t rt_closure_func_ptr(int64_t c) { (void)c; return 0; }
void rt_closure_release(int64_t c) { (void)c; }
void rt_closure_retain(int64_t c) { (void)c; }
int64_t rt_value_int(int64_t v) { return v; }
int64_t rt_value_unbox_int(int64_t v) { return v; }
void spl_memtrack_record(void) {}
void spl_memtrack_unrecord(void) {}
int64_t spl_thread_cpu_count(void) { return 1; }

int main(void) {
    int64_t h = rt_thread_local_new();
    if (h <= 0) { puts("FAIL new"); return 1; }
    if (rt_thread_local_get_i64(h) != 0) { puts("FAIL default"); return 1; }
    const int64_t vals[] = {0x123456789abcdef0LL, -1, INT64_MIN, 42};
    for (int i = 0; i < 4; i++) {
        rt_thread_local_set_i64(h, vals[i]);
        if (rt_thread_local_get_i64(h) != vals[i]) { printf("FAIL value %d\n", i); return 1; }
    }
    puts("PASS rt_thread_local_i64");
    return 0;
}
