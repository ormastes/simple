/* Actual registry/reader boundary, including deterministic same-PID coexistence.
 * Include the production owner only in this test translation unit; no syscall
 * mocks or replacement registry. Link the normal CoreC value/runtime providers.
 * AWAITING_VERIFICATION: not compiled/run. Outer timeout required (30 seconds).
 */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#ifndef _WIN32
#include <signal.h>
#include <sys/types.h>
#include <sys/wait.h>
static int observed_wait_calls;
static pid_t ref_test_waitpid(pid_t pid, int* status, int options);
#define waitpid ref_test_waitpid
static int observed_signal_calls;
static int ref_test_kill(pid_t pid, int number);
#define kill ref_test_kill
#endif
#include "../runtime_process.c"
#ifndef _WIN32
#undef kill
#undef waitpid
static pid_t ref_test_waitpid(pid_t pid, int* status, int options) {
    observed_wait_calls++;
    return waitpid(pid, status, options);
}
/* Observe and forward the actual mechanism, never fake signal success. */
static int ref_test_kill(pid_t pid, int number) {
    observed_signal_calls++;
    return kill(pid, number);
}
#endif
#include <assert.h>

static void pause_one_ms(void) {
#ifdef _WIN32
    Sleep(1);
#else
    struct timespec delay = {0, 1000000}; nanosleep(&delay, NULL);
#endif
}
#ifdef _WIN32
typedef struct WinPipedSlot TestSlot;
static TestSlot* retained_slot(const char* bytes, int64_t pid) {
    TestSlot* slot = win_piped_reserve_spawn(); assert(slot);
    HANDLE read_end = NULL, write_end = NULL;
    assert(CreatePipe(&read_end, &write_end, NULL, 0));
    DWORD written = 0;
    assert(WriteFile(write_end, bytes, (DWORD)strlen(bytes), &written, NULL));
    assert(written == strlen(bytes)); CloseHandle(write_end);
    AcquireSRWLockExclusive(&win_piped_lock);
    slot->pid = (DWORD)pid; slot->stdout_read = read_end;
    slot->process = CreateEventA(NULL, TRUE, TRUE, NULL); assert(slot->process);
    slot->closing = false;
    ReleaseSRWLockExclusive(&win_piped_lock);
    return slot;
}
static void set_pid(TestSlot* slot, int64_t pid) {
    AcquireSRWLockExclusive(&win_piped_lock); slot->pid = (DWORD)pid;
    ReleaseSRWLockExclusive(&win_piped_lock);
}
static void counter_limit(void) {
    AcquireSRWLockExclusive(&win_piped_lock);
    uint64_t saved = win_piped_generation; win_piped_generation = INT64_MAX;
    ReleaseSRWLockExclusive(&win_piped_lock);
    assert(!win_piped_reserve_spawn());
    AcquireSRWLockExclusive(&win_piped_lock); win_piped_generation = saved;
    ReleaseSRWLockExclusive(&win_piped_lock);
}
#else
typedef struct RtProcSlot TestSlot;
static TestSlot* retained_slot(const char* bytes, int64_t pid) {
    TestSlot* slot = proc_alloc(false); assert(slot);
    int endpoints[2]; assert(pipe(endpoints) == 0);
    assert(write(endpoints[1], bytes, strlen(bytes)) == (ssize_t)strlen(bytes));
    close(endpoints[1]);
    assert(fcntl(endpoints[0], F_SETFL, O_NONBLOCK) == 0);
    assert(pthread_mutex_lock(&s_proc_lock) == 0);
    slot->pid = (pid_t)pid; slot->stdout_fd = endpoints[0];
    slot->leader_reaped = true; slot->tree_stopped = false;
    assert(pthread_mutex_unlock(&s_proc_lock) == 0);
    return slot;
}
static void set_pid(TestSlot* slot, int64_t pid) {
    assert(pthread_mutex_lock(&s_proc_lock) == 0); slot->pid = (pid_t)pid;
    assert(pthread_mutex_unlock(&s_proc_lock) == 0);
}
static void counter_limit(void) {
    assert(pthread_mutex_lock(&s_proc_lock) == 0);
    uint64_t saved = s_proc_generation; s_proc_generation = INT64_MAX;
    assert(pthread_mutex_unlock(&s_proc_lock) == 0);
    assert(!proc_alloc(false));
    assert(pthread_mutex_lock(&s_proc_lock) == 0); s_proc_generation = saved;
    assert(pthread_mutex_unlock(&s_proc_lock) == 0);
}
#endif
static void stale_all(int64_t pid, int64_t generation) {
    assert(rt_process_validate_piped_ref_v1(pid, generation) == -2);
    assert(strcmp(rt_process_read_stdout_ref_v1(pid, generation), "") == 0);
    assert(rt_process_stdout_state_ref_v1(pid, generation) == -2);
    assert(rt_process_write_stdin_some_ref_v1(pid, generation, "BAD", 3, 0, 3) == -2);
    assert(rt_process_is_piped_alive_ref_v1(pid, generation) == -2);
    assert(rt_process_close_piped_ref_v1(pid, generation) == -2);
}
static int child_mode(void) {
    assert(fwrite("new", 1, 3, stdout) == 3); fflush(stdout);
    for (int i = 0; i < 3; i++) {
        int byte = getchar(); if (byte == EOF) return 9;
        assert(putchar(byte) != EOF); fflush(stdout);
    }
    /* Incomplete UTF-8 must flush replacement only when actual EOF is seen. */
    assert(putchar(0xe2) != EOF); fflush(stdout);
    return 0;
}
static void invalid_write_bounds(int64_t pid, int64_t generation) {
    assert(rt_process_write_stdin_some_ref_v1(pid, generation, "x", 1, -1, 1) == -1);
    assert(rt_process_write_stdin_some_ref_v1(pid, generation, "x", 1, 2, 1) == -1);
    assert(rt_process_write_stdin_some_ref_v1(pid, generation, "x", 1, 0, 0) == -1);
    assert(rt_process_write_stdin_some_ref_v1(pid, generation, "x", 1, 0, -1) == -1);
}
static int legacy_child_mode(void) {
    assert(fwrite("legacy", 1, 6, stdout) == 6); fflush(stdout);
    int byte = getchar(); if (byte == EOF) return 9;
    assert(putchar(byte) != EOF); fflush(stdout);
    for (int i = 0; i < 5000; i++) pause_one_ms();
    return 0;
}
static void legacy_smoke(const char* executable) {
    SplArray* args = rt_array_new(1); assert(args);
    const char* mode = "--legacy-piped-child";
    rt_array_push(args, rt_string_new((const uint8_t*)mode, strlen(mode)));
    /* This child belongs only to the old PID API, never a Ref fallback. */
    int64_t pid = rt_process_spawn_piped(executable, args); assert(pid > 0);
    assert(rt_process_is_alive(pid));
    char output[32] = {0}; size_t used = 0;
    for (int i = 0; i < 1000 && used < 6; i++) {
        const char* chunk = rt_process_read_stdout(pid); size_t count = strlen(chunk);
        assert(used + count < sizeof(output)); memcpy(output + used, chunk, count + 1); used += count;
        if (used < 6) pause_one_ms();
    }
    assert(strcmp(output, "legacy") == 0);
    int64_t written = 0;
    for (int i = 0; i < 1000 && !written; i++) {
        written = rt_process_write_stdin_some(pid, "L", 1, 0, 1);
        assert(written >= 0 && written <= 1); if (!written) pause_one_ms();
    }
    assert(written == 1);
    for (int i = 0; i < 1000 && used < 7; i++) {
        const char* chunk = rt_process_read_stdout(pid); size_t count = strlen(chunk);
        assert(used + count < sizeof(output)); memcpy(output + used, chunk, count + 1); used += count;
        if (used < 7) pause_one_ms();
    }
    assert(strcmp(output, "legacyL") == 0);
    assert(rt_process_is_alive(pid));
    assert(rt_process_close_piped(pid));
    assert(!rt_process_is_alive(pid));
    assert(!rt_process_close_piped(pid));
    rt_array_free(args);
}
static void saturation_case(const char* executable) {
#ifndef _WIN32
    (void)executable;
    TestSlot* slot = proc_alloc(false); assert(slot);
    int endpoints[2]; assert(pipe(endpoints) == 0);
    int flags = fcntl(endpoints[1], F_GETFL); assert(flags >= 0);
    assert(fcntl(endpoints[1], F_SETFL, flags | O_NONBLOCK) == 0);
    char bytes[4096]; memset(bytes, 'f', sizeof(bytes));
    ssize_t count;
    do { count = write(endpoints[1], bytes, sizeof(bytes)); } while (count > 0);
    assert(count < 0 && (errno == EAGAIN || errno == EWOULDBLOCK));
    assert(pthread_mutex_lock(&s_proc_lock) == 0);
    slot->pid = INT32_MAX; slot->stdin_fd = endpoints[1];
    assert(pthread_mutex_unlock(&s_proc_lock) == 0);
    int64_t generation = (int64_t)slot->generation;
    invalid_write_bounds(INT32_MAX, generation);
    /* Not offset==length: the real nonblocking pipe is known to be full. */
    assert(rt_process_write_stdin_some_ref_v1(INT32_MAX, generation, "x", 1, 0, 1) == 0);
    assert(read(endpoints[0], bytes, sizeof(bytes)) > 0);
    assert(rt_process_write_stdin_some_ref_v1(INT32_MAX, generation, "x", 1, 0, 1) == 1);
    close(endpoints[0]);
    proc_free(slot); /* test-only real-FD fixture; there is no child to signal */
#else
    SplArray* args = rt_array_new(1); assert(args);
    const char* mode = "--piped-ref-blocked";
    rt_array_push(args, rt_string_new((const uint8_t*)mode, strlen(mode)));
    int64_t generation = rt_process_spawn_piped_generation_v1(executable, strlen(executable), args);
    assert(generation > 0);
    int64_t pid = rt_process_piped_pid_for_generation_v1(generation); assert(pid > 0);
    invalid_write_bounds(pid, generation);
    const int64_t size = 4 * 1024 * 1024;
    char* bytes = (char*)malloc((size_t)size); assert(bytes); memset(bytes, 'f', (size_t)size);
    int64_t offset = 0; int deferred = 0;
    for (int i = 0; i < 2000 && deferred < 16 && offset < size; i++) {
        int64_t progress = rt_process_write_stdin_some_ref_v1(pid, generation, bytes, size, offset, 4096);
        assert(progress >= 0 && progress <= 4096);
        offset += progress;
        if (!progress) { deferred++; pause_one_ms(); } else deferred = 0;
    }
    /* The child never reads; repeated pending writes exercise actual named-pipe
     * backpressure rather than accepting a first transient asynchronous zero. */
    assert(deferred == 16 && offset < size);
    assert(rt_process_close_piped_ref_v1(pid, generation) == 0);
    free(bytes); rt_array_free(args);
#endif
}
int main(int argc, char** argv) {
    if (argc == 2 && strcmp(argv[1], "--piped-ref-child") == 0) return child_mode();
    if (argc == 2 && strcmp(argv[1], "--legacy-piped-child") == 0) return legacy_child_mode();
    if (argc == 2 && strcmp(argv[1], "--piped-ref-blocked") == 0) {
        for (int i = 0; i < 5000; i++) pause_one_ms();
        return 0;
    }
#ifndef _WIN32
    alarm(30);
#endif
    TestSlot* old = retained_slot("old", INT32_MAX);
    int64_t old_generation = (int64_t)old->generation;
    char executable[4096];
#ifdef _WIN32
    DWORD length = GetModuleFileNameA(NULL, executable, sizeof(executable));
    assert(length > 0 && length < sizeof(executable));
#else
    if (argv[0][0] == '/') { assert(strlen(argv[0]) < sizeof(executable)); strcpy(executable, argv[0]); }
    else {
        assert(getcwd(executable, sizeof(executable)));
        assert(strlen(executable) + strlen(argv[0]) + 2 < sizeof(executable));
        strcat(executable, "/"); strcat(executable, argv[0]);
    }
#endif
    SplArray* args = rt_array_new(1); assert(args);
    rt_array_push(args, rt_string_new((const uint8_t*)"--piped-ref-child", 17));
    int64_t generation = rt_process_spawn_piped_generation_v1(executable, strlen(executable), args);
    assert(generation > old_generation);
    int64_t pid = rt_process_piped_pid_for_generation_v1(generation); assert(pid > 0);
    set_pid(old, pid); /* old retained slot is earlier than the live new slot */
    assert(rt_process_validate_piped_ref_v1(pid, generation) == 0);
    assert(rt_process_validate_piped_ref_v1(pid, old_generation) == 0);
#ifdef _WIN32
    assert(rt_process_is_piped_alive_ref_v1(pid, generation) == 1);
    assert(rt_process_is_piped_alive_ref_v1(pid, old_generation) == 0);
#else
    int signals_before = observed_signal_calls;
    int waits_before = observed_wait_calls;
    assert(pthread_mutex_lock(&s_proc_lock) == 0);
    old->leader_reaped = false; /* stale flag after an external canonical reap */
    assert(pthread_mutex_unlock(&s_proc_lock) == 0);
    assert(rt_process_is_piped_alive_ref_v1(pid, old_generation) == -3);
    assert(rt_process_is_piped_alive_ref_v1(pid, generation) == -3);
    assert(observed_wait_calls == waits_before);
    assert(rt_process_close_piped_ref_v1(pid, old_generation) == -3);
    assert(rt_process_close_piped_ref_v1(pid, generation) == -3);
    assert(observed_signal_calls == signals_before);
    assert(rt_process_is_piped_alive_ref_v1(pid, generation) == -3);
    assert(observed_wait_calls == waits_before); /* no reap of the reused target */
#endif
    stale_all(pid, 0); stale_all(0, generation); stale_all(pid, generation + 100);

    char received[128] = {0}; size_t used = 0;
    for (int i = 0; i < 1000 && used < 3; i++) {
        const char* chunk = rt_process_read_stdout_ref_v1(pid, generation);
        size_t count = strlen(chunk); assert(used + count < sizeof(received));
        memcpy(received + used, chunk, count + 1); used += count;
        if (used < 3) pause_one_ms();
    }
    assert(strcmp(received, "new") == 0); /* not earlier old-slot bytes */
    assert(rt_process_stdout_state_ref_v1(pid, generation) == 0);
    const char payload[] = "\xc3\xa9Z";
    int64_t offset = 0;
    for (int i = 0; i < 1000 && offset < 3; i++) {
        int64_t progress = rt_process_write_stdin_some_ref_v1(pid, generation, payload, 3, offset, 1);
        assert(progress >= 0 && progress <= 1); offset += progress;
        if (!progress) pause_one_ms();
    }
    assert(offset == 3);
#ifdef _WIN32
    bool exited = false;
    for (int i = 0; i < 1000; i++) {
        int64_t alive = rt_process_is_piped_alive_ref_v1(pid, generation);
        assert(alive >= 0);
        if (!alive) { exited = true; break; } pause_one_ms();
    }
    assert(exited); /* liveness must not consume the remaining stdout */
#else
    assert(rt_process_is_piped_alive_ref_v1(pid, generation) == -3);
    assert(observed_wait_calls == waits_before);
#endif
    bool eof = false;
    for (int i = 0; i < 1000; i++) {
        const char* chunk = rt_process_read_stdout_ref_v1(pid, generation);
        size_t count = strlen(chunk); assert(used + count < sizeof(received));
        memcpy(received + used, chunk, count + 1); used += count;
        int64_t state = rt_process_stdout_state_ref_v1(pid, generation);
        assert(state >= 0);
        if (state == 1) { eof = true; break; } pause_one_ms();
    }
    assert(eof && strcmp(received, "new\xc3\xa9Z\xef\xbf\xbd") == 0);
    assert(rt_process_validate_piped_ref_v1(pid, generation) == 0);
#ifndef _WIN32
    assert(observed_wait_calls == waits_before);
    int child_status = 0; pid_t waited = 0;
    for (int i = 0; i < 1000 && waited == 0; i++) {
        waited = waitpid((pid_t)pid, &child_status, WNOHANG);
        assert(waited >= 0); if (!waited) pause_one_ms();
    }
    /* Explicit TEST-owner reap after real EOF; no production Ref fallback. */
    assert(waited == pid && WIFEXITED(child_status) && WEXITSTATUS(child_status) == 0);
#endif
#ifdef _WIN32
    assert(rt_process_close_piped_ref_v1(pid, generation) == 0);
#else
    assert(rt_process_close_piped_ref_v1(pid, generation) == -3);
    assert(rt_process_close_piped_ref_v1(pid, generation) == -3);
    assert(observed_signal_calls == signals_before);
    /* Test-only retirement of the reaped fixture, NOT a supported Ref close.
     * It closes descriptors only, permitting deterministic slot-reuse testing. */
    proc_free(proc_ref_v1(pid, generation));
#endif
    stale_all(pid, generation); /* duplicate close cannot consume the old slot */
    assert(strcmp(rt_process_read_stdout_ref_v1(pid, old_generation), "old") == 0);
#ifdef _WIN32
    assert(rt_process_close_piped_ref_v1(pid, old_generation) == 0);
#else
    assert(rt_process_close_piped_ref_v1(pid, old_generation) == -3);
    proc_free(old); /* test-only descriptor retirement; no signal */
#endif
    TestSlot* replacement = retained_slot("replacement", pid);
    int64_t replacement_generation = (int64_t)replacement->generation;
    stale_all(pid, generation); /* deterministic actual same-PID generation reuse */
    assert(strcmp(rt_process_read_stdout_ref_v1(pid, replacement_generation), "replacement") == 0);
#ifdef _WIN32
    assert(rt_process_close_piped_ref_v1(pid, replacement_generation) == 0);
#else
    assert(rt_process_close_piped_ref_v1(pid, replacement_generation) == -3);
    assert(observed_signal_calls == signals_before);
    proc_free(replacement); /* synthetic retained-pipe fixture cleanup */
#endif
    assert(rt_process_piped_pid_for_generation_v1(generation) == -2);
    counter_limit();

    const char nul_command[] = "absolute\0truncated";
    assert(rt_process_spawn_piped_generation_v1(nul_command, sizeof(nul_command)-1, args) == -1);
    SplArray* bad_args = rt_array_new(65); assert(bad_args);
    for (int i = 0; i < 65; i++) rt_array_push(bad_args, rt_string_new((const uint8_t*)"x", 1));
    assert(rt_process_spawn_piped_generation_v1(executable, strlen(executable), bad_args) == -1);
    SplArray* nul_args = rt_array_new(1); assert(nul_args);
    rt_array_push(nul_args, rt_string_new((const uint8_t*)"a\0b", 3));
    assert(rt_process_spawn_piped_generation_v1(executable, strlen(executable), nul_args) == -1);
    rt_array_free(args); rt_array_free(bad_args); rt_array_free(nul_args);
    saturation_case(executable);
    legacy_smoke(executable);
    puts("piped process Ref V1 registry/reader boundary: PASS");
    return 0;
}
