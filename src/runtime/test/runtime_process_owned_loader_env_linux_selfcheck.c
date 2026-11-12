/* Linux owned launch: the pinned image may be in the system-loader dynamic
 * class (runtime_process.c rt_hal_pinnable_elf_fd), whose only library-path
 * guarantee is that resolution follows the system loader paths. An LD_*
 * variable in the launch environment moves that resolution, so pov4_start_exact
 * refuses such an environment before any slot or child exists.
 * Run from the repository root:
 *   cc -std=c11 -O0 -Wall -Wextra -pthread \
 *     src/runtime/test/runtime_process_owned_loader_env_linux_selfcheck.c \
 *     src/runtime/runtime_process_tree.c -o /tmp/pov4-loader-env && /tmp/pov4-loader-env
 * The predicate is exercised directly (same translation unit); its wiring is
 * the first statement of the Linux branch of pov4_start_exact. */
#if !defined(__linux__)
#include <stdio.h>
int main(void) { puts("runtime_process_owned_loader_env_linux_selfcheck: SKIP (requires Linux)"); return 77; }
#else
#define _GNU_SOURCE
#include "../runtime.h"
#include <assert.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

SplArray* rt_array_new(int64_t capacity) {
    SplArray* a = calloc(1, sizeof(*a)); assert(a);
    a->cap = capacity > 0 ? capacity : 1;
    a->items = calloc((size_t)a->cap, sizeof(*a->items)); assert(a->items);
    return a;
}
int64_t rt_array_len(SplArray* a) { return a ? a->len : -1; }
int64_t rt_array_get(SplArray* a, int64_t i) {
    return a && i >= 0 && i < a->len ? a->items[i].as_int : 0;
}
int8_t rt_array_push(SplArray* a, int64_t value) {
    if (!a || a->len >= a->cap) return 0;
    a->items[a->len++].as_int = value; return 1;
}
int8_t rt_array_set(SplArray* a, int64_t i, int64_t value) {
    if (!a || i < 0 || i >= a->len) return 0;
    a->items[i].as_int = value; return 1;
}
int64_t rt_value_int(int64_t value) { return value; }
int64_t rt_value_as_int(int64_t value) { return value; }
int8_t rt_value_is_int(int64_t value) { (void)value; return 1; }
void* rt_alloc(int64_t size) { return size > 0 ? calloc(1, (size_t)size) : NULL; }
void rt_free(void* value) { free(value); }
int64_t rt_string_len(int64_t value) { (void)value; return -1; }
const uint8_t* rt_string_data(int64_t value) { (void)value; return NULL; }
int64_t rt_string_new(const uint8_t* bytes, uint64_t length) { (void)bytes; (void)length; return 1; }
void rt_array_free(SplArray* a) { if (a) { free(a->items); free(a); } }
int64_t rt_tuple_new(int64_t len) {
    SplArray* a = rt_array_new(len);
    for (int64_t i = 0; i < len; i++) assert(rt_array_push(a, 0));
    return (int64_t)(uintptr_t)a;
}
int8_t rt_tuple_set(int64_t tuple, int64_t index, int64_t value) {
    return rt_array_set((SplArray*)(uintptr_t)tuple, index, value);
}
int64_t rt_free_deep(int64_t value) { (void)value; return 1; }
int64_t rt_array_bytes_validate(int64_t value) {
    SplArray* a = (SplArray*)(uintptr_t)value;
    if (!a) return -1;
    for (int64_t i = 0; i < a->len; i++)
        if (rt_array_get(a, i) < 0 || rt_array_get(a, i) > 255) return -1;
    return a->len;
}
int64_t rt_array_bytes_copy_checked(int64_t value, uint8_t* out, int64_t cap) {
    int64_t n = rt_array_bytes_validate(value); if (n < 0 || n > cap) return -1;
    SplArray* a = (SplArray*)(uintptr_t)value;
    for (int64_t i = 0; i < n; i++) out[i] = (uint8_t)rt_array_get(a, i);
    return n;
}
int64_t rt_process_acquire_pinned_executable(int64_t token) { (void)token; errno = ESTALE; return -1; }
int rt_process_close_pinned_executable_owned_value(int64_t token) { (void)token; return 0; }
SplArray* rt_process_pinned_executable_sha256_value(int64_t token) { (void)token; return NULL; }
int rt_process_stream_claim_launch_v2(int64_t a, const char* b, int64_t c, const char* d, int64_t e, int* f, int* g, int* h) {
    (void)a; (void)b; (void)c; (void)d; (void)e; (void)f; (void)g; (void)h; return ENOTSUP; }
int rt_process_stream_launch_not_started_v2(int64_t a, const char* b, int64_t c, const char* d, int64_t e) {
    (void)a; (void)b; (void)c; (void)d; (void)e; return ENOTSUP; }
int rt_process_stream_publish_broker_v2(int64_t a, const char* b, int64_t c, const char* d, int64_t e, int64_t f) {
    (void)a; (void)b; (void)c; (void)d; (void)e; (void)f; return ENOTSUP; }
int simple_local_unix_origin_v1(void) { return 0; }

#include "../runtime_process_owned.c"

static int failures = 0, checks = 0;
#define CHECK(cond, what) do { checks++; if (!(cond)) { fprintf(stderr, "FAIL: %s\n", what); failures++; } } while (0)

int main(void) {
    char* const clean[] = {(char*)"PATH=/usr/bin:/bin", (char*)"HOME=/nonexistent",
                           (char*)"LDFLAGS=-L/x", (char*)"XLD_PRELOAD=1", (char*)"SIMPLE_HIR_WORKER_PROFILE_V1=1", NULL};
    char* const preload[] = {(char*)"PATH=/usr/bin:/bin", (char*)"LD_PRELOAD=/tmp/evil.so", NULL};
    char* const libpath[] = {(char*)"LD_LIBRARY_PATH=/tmp", (char*)"PATH=/usr/bin", NULL};
    char* const audit[] = {(char*)"PATH=/usr/bin", (char*)"LD_AUDIT=/tmp/audit.so", NULL};
    char* const empty_value[] = {(char*)"LD_LIBRARY_PATH=", NULL};
    char* const none[] = {NULL};
    CHECK(!pov4_environment_steers_loader(clean), "an environment without LD_* keys is admitted");
    CHECK(!pov4_environment_steers_loader(none), "an empty environment is admitted");
    CHECK(!pov4_environment_steers_loader(NULL), "a NULL environment is admitted");
    CHECK(pov4_environment_steers_loader(preload), "LD_PRELOAD is refused");
    CHECK(pov4_environment_steers_loader(libpath), "LD_LIBRARY_PATH (first entry) is refused");
    CHECK(pov4_environment_steers_loader(audit), "LD_AUDIT (last entry) is refused");
    CHECK(pov4_environment_steers_loader(empty_value), "an empty-valued LD_* key is still refused");
    if (failures) { fprintf(stderr, "runtime_process_owned_loader_env_linux_selfcheck: FAIL (%d of %d)\n", failures, checks); return 1; }
    printf("runtime_process_owned_loader_env_linux_selfcheck: PASS (%d checks)\n", checks);
    return 0;
}
#endif
