/* Focused Linux/POSIX regression against the ACTUAL capture/fork owners.
 * The child-delay atfork seam delays real native child setup; it does not
 * replace the admission implementation, clock, wait, pipe or capture model.
 * Windows is outside this witness. Link with production runtime_native.c,
 * runtime_process.c, runtime_fork.c and their normal core-C dependencies. */
#define _POSIX_C_SOURCE 200809L
#include "runtime.h"
#include "runtime_fork.h"
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static _Thread_local int delay_child;
static int delay_witness_fd = -1;
static int checks;
#define CHECK(value) do { checks++; if (!(value)) { fprintf(stderr, "FAIL line %d: %s\n", __LINE__, #value); abort(); } } while (0)

static int64_t now_ms(void) {
    struct timespec sampled;
    assert(clock_gettime(CLOCK_REALTIME, &sampled) == 0);
    return (int64_t)sampled.tv_sec * 1000 + sampled.tv_nsec / 1000000;
}
static void child_delay(void) {
    if (delay_child) {
        if (delay_witness_fd >= 0) {
            const char forked = 'F'; (void)write(delay_witness_fd, &forked, 1);
            close(delay_witness_fd);
        }
        struct timespec duration = {1, 500000000};
        while (nanosleep(&duration, &duration) < 0 && errno == EINTR) {}
    }
}
static int64_t text(const char* value) {
    return rt_string_new((const uint8_t*)value, strlen(value));
}
static int text_equals(int64_t value, const char* expected) {
    size_t length = strlen(expected);
    return rt_string_len(value) == (int64_t)length &&
        (length == 0 || memcmp(rt_string_data(value), expected, length) == 0);
}
static SplArray* arguments(const char* mode, const char* value) {
    SplArray* args = rt_array_new(2);
    rt_array_push(args, text(mode));
    rt_array_push(args, text(value));
    return args;
}

struct Gate { pthread_mutex_t lock; pthread_cond_t changed; int count; int phase; };
static void gate(struct Gate* shared) {
    assert(pthread_mutex_lock(&shared->lock) == 0);
    int phase = shared->phase;
    if (++shared->count == 2) {
        shared->count = 0; shared->phase++;
        assert(pthread_cond_broadcast(&shared->changed) == 0);
    } else {
        struct timespec limit;
        assert(clock_gettime(CLOCK_REALTIME, &limit) == 0); limit.tv_sec += 10;
        while (shared->phase == phase) assert(pthread_cond_timedwait(&shared->changed, &shared->lock, &limit) == 0);
    }
    assert(pthread_mutex_unlock(&shared->lock) == 0);
}
struct RawCase { struct Gate* shared; struct RawCase* other; int id; int64_t pid; int failed; };
static void* raw_worker(void* opaque) {
    struct RawCase* test = (struct RawCase*)opaque;
    const char* out = test->id == 0 ? "ordinary-owner\n" : "admitted-owner\n";
    const char* err = test->id == 0 ? "ordinary-error\n" : "admitted-error\n";
    int64_t pid = test->id == 0 ? rt_fork_child_setup() : simple_fork_child_setup_admitted_v1(now_ms() + 5000);
    if (pid == 0) {
        (void)write(STDOUT_FILENO, out, strlen(out));
        (void)write(STDERR_FILENO, err, strlen(err));
        rt_fork_child_exit(31 + test->id);
    }
    assert(pid > 0); test->pid = pid;
    gate(test->shared); /* BOTH real children/pipe owners exist before either wait. */
    if (rt_fork_parent_wait_bounded(test->other->pid, 1000, 128) != -1) test->failed = 1;
    if (rt_fork_parent_wait_bounded(pid, 5000, 128) != 31 + test->id) test->failed = 2;
    gate(test->shared); /* Retain both results across the other owner's wait. */
    if (strcmp(rt_fork_parent_stdout(), out) || strcmp(rt_fork_parent_stderr(), err) ||
            simple_fork_parent_capture_flags_v1() != 0) test->failed = 3;
    int64_t peak_before_release = rt_fork_parent_peak_rss_bytes();
    if (test->id == 0) simple_fork_parent_capture_release_v1();
    gate(test->shared); /* Releasing ordinary output cannot free admitted output. */
    if (test->id == 1 && strcmp(rt_fork_parent_stdout(), out)) test->failed = 4;
    simple_fork_parent_capture_release_v1();
    if (strcmp(rt_fork_parent_stdout(), "") || peak_before_release < 0 ||
            rt_fork_parent_peak_rss_bytes() != peak_before_release) test->failed = 5;
    return NULL;
}

struct CaptureCase { struct Gate* shared; const char* executable; SplArray* args; int admitted; int failed; };
static void* capture_worker(void* opaque) {
    struct CaptureCase* test = (struct CaptureCase*)opaque;
    gate(test->shared);
    int64_t out, err, status, flags = 0;
    if (test->admitted) {
        int64_t* receipt = rt_process_run_bounded_admitted_tuple_v1(test->executable, strlen(test->executable),
            test->args, NULL, 2, 5000, 1024, now_ms() + 5000);
        out = receipt[0]; err = receipt[1]; status = receipt[2]; flags = receipt[3];
    } else {
        SplArray* receipt = rt_process_run_bounded(test->executable, strlen(test->executable), test->args, 5000, 1024);
        out = rt_array_get(receipt, 0); err = rt_array_get(receipt, 1); status = rt_value_as_int(rt_array_get(receipt, 2));
        rt_array_free(receipt);
    }
    const char* expected = test->admitted ? "captured-admitted" : "captured-ordinary";
    if (!text_equals(out, expected) || !text_equals(err, "") || status != 23 || flags != 0) test->failed = 1;
    if (strcmp(rt_fork_parent_stdout(), "") || rt_fork_parent_peak_rss_bytes() <= 0) test->failed = 2;
    return NULL;
}

static void concurrent_owners(const char* executable) {
    struct Gate shared = {PTHREAD_MUTEX_INITIALIZER, PTHREAD_COND_INITIALIZER, 0, 0};
    struct RawCase raw[2] = {{&shared, NULL, 0, 0, 0}, {&shared, NULL, 1, 0, 0}};
    raw[0].other = &raw[1]; raw[1].other = &raw[0];
    pthread_t threads[2];
    CHECK(pthread_create(&threads[0], NULL, raw_worker, &raw[0]) == 0);
    CHECK(pthread_create(&threads[1], NULL, raw_worker, &raw[1]) == 0);
    CHECK(pthread_join(threads[0], NULL) == 0); CHECK(pthread_join(threads[1], NULL) == 0);
    CHECK(raw[0].failed == 0); CHECK(raw[1].failed == 0);
    struct CaptureCase capture[2] = {
        {&shared, executable, arguments("--interleave", "captured-ordinary"), 0, 0},
        {&shared, executable, arguments("--interleave", "captured-admitted"), 1, 0}
    };
    CHECK(pthread_create(&threads[0], NULL, capture_worker, &capture[0]) == 0);
    CHECK(pthread_create(&threads[1], NULL, capture_worker, &capture[1]) == 0);
    CHECK(pthread_join(threads[0], NULL) == 0); CHECK(pthread_join(threads[1], NULL) == 0);
    CHECK(capture[0].failed == 0); CHECK(capture[1].failed == 0);
    rt_array_free(capture[0].args); rt_array_free(capture[1].args);
    CHECK(pthread_cond_destroy(&shared.changed) == 0); CHECK(pthread_mutex_destroy(&shared.lock) == 0);
}

#include "process_capture_cloexec_overlap_private.h"

int main(int argc, char** argv) {
    if (argc == 3) {
        if (!strcmp(argv[1], "--interleave")) {
            struct timespec pause = {0, 50000000}; nanosleep(&pause, NULL);
            (void)write(STDOUT_FILENO, argv[2], strlen(argv[2])); return 23;
        }
        if (!strcmp(argv[1], "--marker")) {
            FILE* marker = fopen(argv[2], "w"); if (!marker) return 99;
            fputs("workload-entered", marker); fclose(marker); return 0;
        }
        if (!strcmp(argv[1], "--spoof")) {
            fputs("launch-deadline-expired-before-effect", stderr); return 125;
        }
        if (!strcmp(argv[1], "--env")) {
            const char* inherited = getenv("SIMPLE_CAPTURE_ADMISSION_WITNESS");
            if (inherited) fputs(inherited, stdout); return 0;
        }
        if (!strcmp(argv[1], "--limit")) { for (int i = 0; i < 1024; i++) fputc('x', stdout); return 0; }
        if (!strcmp(argv[1], "--exec-holder")) {
            const char output[] = "exec-holder";
            (void)write(STDOUT_FILENO, output, sizeof(output) - 1);
            struct timespec duration = {2, 0}; nanosleep(&duration, NULL); return 29;
        }
        if (!strcmp(argv[1], "--timeout")) { for (;;) pause(); }
        return 98;
    }
    CHECK(argc == 1); CHECK(argv[0][0] == '/'); CHECK(pthread_atfork(overlap_atfork_prepare_v1, NULL, child_delay) == 0);
    char marker[] = "/tmp/simple-admission-owner-XXXXXX";
    int marker_fd = mkstemp(marker); CHECK(marker_fd >= 0); close(marker_fd); CHECK(unlink(marker) == 0);
    SplArray* args = arguments("--marker", marker);
    int64_t* receipt = rt_process_run_bounded_admitted_tuple_v1(argv[0], strlen(argv[0]), args, NULL, 2, 2000, 1024, now_ms() - 1);
    CHECK(receipt[3] == 32); CHECK(access(marker, F_OK) != 0);
    int witnessed[2]; CHECK(pipe(witnessed) == 0);
    CHECK(fcntl(witnessed[0], F_SETFL, O_NONBLOCK) == 0);
    delay_witness_fd = witnessed[1]; delay_child = 1;
    receipt = rt_process_run_bounded_admitted_tuple_v1(argv[0], strlen(argv[0]), args, NULL, 2, 3000, 1024, now_ms() + 1000);
    delay_child = 0;
    close(witnessed[1]); delay_witness_fd = -1;
    char forked = 0; CHECK(read(witnessed[0], &forked, 1) == 1 && forked == 'F'); close(witnessed[0]);
    CHECK(receipt[3] == 32); CHECK(access(marker, F_OK) != 0); /* actual status-pipe/pre-exec rejection */
    receipt = rt_process_run_bounded_admitted_tuple_v1(argv[0], strlen(argv[0]), args, NULL, 2, 2000, 1024, now_ms() + 5000);
    CHECK(receipt[3] == 0); CHECK(receipt[2] == 0); CHECK(access(marker, F_OK) == 0); CHECK(unlink(marker) == 0);
    rt_array_free(args);
    args = arguments("--spoof", "");
    receipt = rt_process_run_bounded_admitted_tuple_v1(argv[0], strlen(argv[0]), args, NULL, 2, 2000, 1024, now_ms() + 5000);
    CHECK(receipt[2] == 125); CHECK(receipt[3] == 0); CHECK(text_equals(receipt[1], "launch-deadline-expired-before-effect"));
    rt_array_free(args);
    CHECK(setenv("SIMPLE_CAPTURE_ADMISSION_WITNESS", "trusted-inherited", 1) == 0);
    args = arguments("--env", "");
    receipt = rt_process_run_bounded_admitted_tuple_v1(argv[0], strlen(argv[0]), args, NULL, 2, 2000, 1024, now_ms() + 5000);
    CHECK(receipt[3] == 0); CHECK(text_equals(receipt[0], "trusted-inherited")); rt_array_free(args);
    args = arguments("--limit", "");
    receipt = rt_process_run_bounded_admitted_tuple_v1(argv[0], strlen(argv[0]), args, NULL, 2, 2000, 16, now_ms() + 5000);
    CHECK((receipt[3] & 2) != 0); CHECK((receipt[3] & (32 | 64)) == 0); rt_array_free(args);
    args = arguments("--limit", "");
    receipt = rt_process_run_bounded_observed_tuple_v1(argv[0], strlen(argv[0]), args, 2000, 16);
    CHECK(receipt[2] == 0); CHECK((receipt[3] & 2) != 0); rt_array_free(args);
    args = arguments("--timeout", "");
    receipt = rt_process_run_bounded_admitted_tuple_v1(argv[0], strlen(argv[0]), args, NULL, 2, 50, 1024, now_ms() + 5000);
    CHECK((receipt[3] & 1) != 0); CHECK((receipt[3] & (32 | 64)) == 0); rt_array_free(args);
    concurrent_owners(argv[0]);
    forced_descriptor_overlap_v1(argv[0], 0);
    forced_descriptor_overlap_v1(argv[0], 1);
    forced_descriptor_overlap_v1(argv[0], 2);
    int status; errno = 0; CHECK(waitpid(-1, &status, WNOHANG) == -1 && errno == ECHILD);
    printf("PASS capture admission/concurrency: %d checks; actual POSIX owners, atomic CLOEXEC, forced overlap, delayed preexec, EOF while other child live, status pipe, no-entry, inherited env, limits, timeout/reap\n", checks);
    return 0;
}
