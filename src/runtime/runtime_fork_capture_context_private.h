/* POSIX synchronous capture owner. Each calling thread owns exactly one
 * outstanding raw child and one retained result; there is no wait mutex or
 * process registry. Call setup/wait/getters on the same thread. */
#ifndef SIMPLE_FORK_CAPTURE_CONTEXT_PRIVATE_H
#define SIMPLE_FORK_CAPTURE_CONTEXT_PRIVATE_H
#include <pthread.h>

typedef struct {
    int stdout_read_fd;
    int stderr_read_fd;
    pid_t active_child;
    char* result_stdout;
    char* result_stderr;
    uint64_t result_stdout_length;
    uint64_t result_stderr_length;
    bool result_timed_out;
    bool result_signaled;
    int64_t result_capture_flags;
    struct rusage result_rusage;
} ForkCaptureContextV1;

static pthread_key_t fork_capture_key_v1;
static pthread_once_t fork_capture_once_v1 = PTHREAD_ONCE_INIT;
static int fork_capture_key_ready_v1;
/* Established before fork. The child pre-exec path reads this inherited
 * pointer without pthread-key lookup, allocation, or destructor registration. */
static _Thread_local ForkCaptureContextV1* fork_capture_current_v1;

static void fork_capture_clear_output_v1(ForkCaptureContextV1* context) {
    if (!context) return;
    if (context->result_stdout) SPL_FREE(context->result_stdout);
    if (context->result_stderr) SPL_FREE(context->result_stderr);
    context->result_stdout = context->result_stderr = NULL;
    context->result_stdout_length = context->result_stderr_length = 0;
}

static void fork_capture_context_destroy_v1(void* opaque) {
    ForkCaptureContextV1* context = (ForkCaptureContextV1*)opaque;
    if (!context) return;
    if (context->stdout_read_fd >= 0) close(context->stdout_read_fd);
    if (context->stderr_read_fd >= 0) close(context->stderr_read_fd);
    fork_capture_clear_output_v1(context);
    /* A raw caller must wait its child before exiting the owner thread. This
     * destructor does not turn an abandoned raw PID into cleanup authority. */
    fork_capture_current_v1 = NULL;
    free(context);
}

static void fork_capture_key_initialize_v1(void) {
    fork_capture_key_ready_v1 = pthread_key_create(&fork_capture_key_v1,
        fork_capture_context_destroy_v1) == 0;
}

static ForkCaptureContextV1* fork_capture_context_v1(void) {
    if (fork_capture_current_v1) return fork_capture_current_v1;
    if (pthread_once(&fork_capture_once_v1, fork_capture_key_initialize_v1) != 0 ||
            !fork_capture_key_ready_v1) return NULL;
    ForkCaptureContextV1* context = (ForkCaptureContextV1*)calloc(1, sizeof(*context));
    if (!context) return NULL;
    context->stdout_read_fd = context->stderr_read_fd = -1;
    context->result_capture_flags = 8;
    if (pthread_setspecific(fork_capture_key_v1, context) != 0) {
        free(context);
        return NULL;
    }
    fork_capture_current_v1 = context;
    return context;
}

/* Keep the established capture algorithm's local names, with thread-owned
 * storage. Public entrypoints check allocation before dereferencing them. */
#define s_stdout_read_fd (fork_capture_current_v1->stdout_read_fd)
#define s_stderr_read_fd (fork_capture_current_v1->stderr_read_fd)
#define s_result_stdout (fork_capture_current_v1->result_stdout)
#define s_result_stderr (fork_capture_current_v1->result_stderr)
#define s_result_stdout_length (fork_capture_current_v1->result_stdout_length)
#define s_result_stderr_length (fork_capture_current_v1->result_stderr_length)
#define s_result_timed_out (fork_capture_current_v1->result_timed_out)
#define s_result_signaled (fork_capture_current_v1->result_signaled)
#define s_result_capture_flags_v1 (fork_capture_current_v1->result_capture_flags)
#define s_result_rusage (fork_capture_current_v1->result_rusage)

/* Drop copied output promptly while preserving metrics and outcome scalars
 * until the next wait. Legacy callers may retain until release/thread exit. */
void simple_fork_parent_capture_release_v1(void) {
    fork_capture_clear_output_v1(fork_capture_current_v1);
}

int64_t simple_fork_parent_capture_flags_v1(void) {
    return fork_capture_current_v1 ? s_result_capture_flags_v1 : 8;
}
bool rt_fork_parent_timed_out(void) {
    return fork_capture_current_v1 ? s_result_timed_out : false;
}
bool rt_fork_parent_signaled(void) {
    return fork_capture_current_v1 ? s_result_signaled : false;
}
int64_t rt_fork_parent_user_cpu_micros(void) {
    if (!fork_capture_current_v1) return 0;
    return (int64_t)s_result_rusage.ru_utime.tv_sec * 1000000LL +
        (int64_t)s_result_rusage.ru_utime.tv_usec;
}
int64_t rt_fork_parent_system_cpu_micros(void) {
    if (!fork_capture_current_v1) return 0;
    return (int64_t)s_result_rusage.ru_stime.tv_sec * 1000000LL +
        (int64_t)s_result_rusage.ru_stime.tv_usec;
}
int64_t rt_fork_parent_peak_rss_bytes(void) {
    if (!fork_capture_current_v1) return 0;
#if defined(__APPLE__)
    return (int64_t)s_result_rusage.ru_maxrss;
#else
    return (int64_t)s_result_rusage.ru_maxrss * 1024LL;
#endif
}
const char* rt_fork_parent_stdout(void) {
    return fork_capture_current_v1 && s_result_stdout ? s_result_stdout : "";
}
const char* rt_fork_parent_stderr(void) {
    return fork_capture_current_v1 && s_result_stderr ? s_result_stderr : "";
}
void simple_fork_parent_capture_lengths(uint64_t* out, uint64_t* err) {
    *out = fork_capture_current_v1 ? s_result_stdout_length : 0;
    *err = fork_capture_current_v1 ? s_result_stderr_length : 0;
}
#endif
