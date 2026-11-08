/* Linux compatibility witness against actual production capture owners.
 * A genuine seccomp filter denies close_range before any tested launch.
 * Legacy text/raw/unbounded capture must execute; new strong capture must
 * positively reject before workload entry. No copied runtime model or stubs. */
#define _GNU_SOURCE
#include "runtime.h"
#include <assert.h>
#include <errno.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/wait.h>
#if defined(__linux__)
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#endif

static int checks;
#define CHECK(value) do { checks++; if (!(value)) { fprintf(stderr, "FAIL line %d: %s\n", __LINE__, #value); abort(); } } while (0)

static int64_t text(const char* value) { return rt_string_new((const uint8_t*)value, strlen(value)); }
static int text_equals(int64_t value, const char* expected) {
    return rt_string_len(value) == (int64_t)strlen(expected) &&
        memcmp(rt_string_data(value), expected, strlen(expected)) == 0;
}
static int64_t now_ms(void) {
    struct timespec sampled; CHECK(clock_gettime(CLOCK_REALTIME, &sampled) == 0);
    return (int64_t)sampled.tv_sec * 1000 + sampled.tv_nsec / 1000000;
}

int main(int argc, char** argv) {
    if (argc == 3 && strcmp(argv[1], "--marker") == 0) {
        FILE* marker = fopen(argv[2], "w"); if (!marker) return 91;
        fputs("actual-workload-entered", marker); fclose(marker);
        fputs("legacy-entered", stdout); return 17;
    }
#if defined(__linux__) && defined(SYS_close_range)
    CHECK(argc == 1); CHECK(argv[0][0] == '/');
    char marker[] = "/tmp/simple-capture-legacy-XXXXXX";
    int fd = mkstemp(marker); CHECK(fd >= 0); close(fd); CHECK(unlink(marker) == 0);
    SplArray* args = rt_array_new(2); CHECK(args != NULL);
    CHECK(rt_array_push(args, text("--marker"))); CHECK(rt_array_push(args, text(marker)));
    struct sock_filter instructions[] = {
        BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, nr)),
        BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, SYS_close_range, 0, 1),
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM),
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW)
    };
    struct sock_fprog filter = {(unsigned short)(sizeof(instructions) / sizeof(instructions[0])), instructions};
    CHECK(prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) == 0);
    CHECK(prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &filter) == 0);
    errno = 0; CHECK(syscall(SYS_close_range, ~0U, ~0U, 0U) == -1 && errno == EPERM);

    SplArray* legacy = rt_process_run_bounded(argv[0], strlen(argv[0]), args, 2000, 1024);
    CHECK(legacy != NULL); CHECK(rt_value_as_int(rt_array_get(legacy, 2)) == 17);
    CHECK(text_equals(rt_array_get(legacy, 0), "legacy-entered")); CHECK(access(marker, F_OK) == 0);
    CHECK(unlink(marker) == 0); rt_array_free(legacy);

    int64_t unbounded = rt_process_run_timeout(argv[0], strlen(argv[0]), args, 2000);
    legacy = (SplArray*)(uintptr_t)unbounded;
    CHECK(legacy != NULL); CHECK(rt_value_as_int(rt_array_get(legacy, 2)) == 17);
    CHECK(text_equals(rt_array_get(legacy, 0), "legacy-entered")); CHECK(access(marker, F_OK) == 0);
    CHECK(unlink(marker) == 0); rt_array_free(legacy);

    int64_t raw = rt_process_run_bounded_bytes(argv[0], strlen(argv[0]), args, 2000, 1024);
    CHECK(raw != 0); CHECK(rt_value_as_int(rt_tuple_get(raw, 2)) == 17);
    SplArray* bytes = (SplArray*)(uintptr_t)rt_tuple_get(raw, 0);
    CHECK(rt_array_len(bytes) == 14); CHECK(rt_value_as_int(rt_array_get(bytes, 0)) == 'l');
    CHECK(access(marker, F_OK) == 0); CHECK(unlink(marker) == 0);

    int64_t* observed = rt_process_run_bounded_observed_tuple_v1(argv[0], strlen(argv[0]), args, 2000, 1024);
    CHECK(observed != NULL); CHECK(observed[2] == -1); CHECK(observed[3] == (8 | 64));
    CHECK(access(marker, F_OK) != 0);
    int64_t* admitted = rt_process_run_bounded_admitted_tuple_v1(argv[0], strlen(argv[0]), args,
        NULL, 2, 2000, 1024, now_ms() + 5000);
    CHECK(admitted != NULL); CHECK(admitted[2] == -1); CHECK(admitted[3] == (8 | 64));
    CHECK(access(marker, F_OK) != 0);
    int status; errno = 0; CHECK(waitpid(-1, &status, WNOHANG) == -1 && errno == ECHILD);
    printf("PASS legacy close_range denial: %d checks; actual seccomp EPERM, legacy bounded/unbounded/raw execute, observed/admitted confirmed no-entry, exact reap\n", checks);
    return 0;
#else
    fputs("UNSUPPORTED: Linux close_range seccomp witness unavailable\n", stderr);
    return 77;
#endif
}
