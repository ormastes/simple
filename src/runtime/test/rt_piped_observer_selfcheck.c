/* Link unchanged against both complete C and selected Rust core capsules. */
#include "runtime.h"
#include "runtime_process_observer_private.h"
#include <stdio.h>
#include <string.h>
#ifdef _WIN32
#include <windows.h>
#else
#include <time.h>
#include <pthread.h>
#include <stdatomic.h>
#endif

static int failures;
static void check(int value, const char* label) {
    if (!value) { ++failures; fprintf(stderr, "FAIL %s\n", label); }
}
static void pause_poll(void) {
#ifdef _WIN32
    Sleep(5);
#else
    struct timespec interval = {0, 5000000}; nanosleep(&interval, NULL);
#endif
}
static int64_t text(const char* value) {
    return rt_string_new((const uint8_t*)value, strlen(value));
}
static int64_t spawn_script(const char* script) {
    SplArray* args = rt_array_new(2);
#ifdef _WIN32
    int64_t flag = text("/C");
    const char* shell = "C:\\Windows\\System32\\cmd.exe";
#else
    int64_t flag = text("-c");
    const char* shell = "/bin/sh";
#endif
    int64_t body = text(script);
    if (!args || !rt_array_push(args, flag) || !rt_array_push(args, body)) return -1;
    int64_t pid = rt_process_spawn_piped(shell, args);
    rt_array_free(args); rt_string_free(flag); rt_string_free(body);
    return pid;
}
static int receipt(int64_t pid, int64_t state, int64_t code) {
    SplArray* out = rt_process_piped_exit_status_value(pid);
    int match = out && rt_array_len(out) == 4 &&
        rt_value_as_int(rt_array_get(out, 0)) == 1 &&
        rt_value_as_int(rt_array_get(out, 1)) == state &&
        rt_value_as_int(rt_array_get(out, 2)) == code &&
        ((state == -1) == (rt_value_as_int(rt_array_get(out, 3)) != 0));
    if (out) rt_array_free(out);
    return match;
}
static int release_eof_peer(int64_t pid) {
    /* The child cannot exit7 before it receives this exact acknowledgement.
     * Retain byte offsets on pending partial writes; no blocking writer call. */
    const char* acknowledgement = "go\n";
    int64_t delivered = 0;
    for (int tick = 0; tick < 1000 && delivered < 3; ++tick) {
        int64_t n = rt_process_write_stdin_some(pid, acknowledgement, 3, delivered, 3);
        if (n < 0 || n > 3 - delivered) return 0;
        delivered += n;
        if (n == 0) pause_poll();
    }
    return delivered == 3;
}
static void script_control(const char* script, int code, int eof_before_exit) {
    int64_t pid = spawn_script(script);
    check(pid > 0, "real child spawned"); if (pid <= 0) return;
    check(rt_process_stdout_state(pid) == 0 && receipt(pid, 0, 0), "pending before stdout read");
    char output[256] = {0}; size_t used = 0;
    int64_t start = rt_time_now_monotonic_ms();
    int64_t current = start;
    check(start >= 0, "monotonic clock available");
    int polls = 0;
    while (polls++ < 1000 && start >= 0 && current >= start && current - start < 5000 && rt_process_stdout_state(pid) == 0) {
        const char* chunk = rt_process_read_stdout(pid);
        size_t n = chunk ? strlen(chunk) : 0;
        if (n > 0 && used + n < sizeof(output)) { memcpy(output + used, chunk, n); used += n; output[used] = 0; }
        pause_poll(); current = rt_time_now_monotonic_ms();
    }
    check(strstr(output, "observed-marker") != NULL, "genuine stdout captured");
    check(rt_process_stdout_state(pid) == 1, "observed EOF state");
    if (eof_before_exit) {
        check(receipt(pid, 0, 0), "EOF alone is not observed exit");
        check(release_eof_peer(pid), "release EOF-blocked real child");
    }
    while (polls++ < 1000 && start >= 0 && current >= start && current - start < 5000 && !receipt(pid, 1, code)) {
        pause_poll(); current = rt_time_now_monotonic_ms();
    }
    for (int repeat = 0; repeat < 3; ++repeat) {
        check(receipt(pid, 1, code), "real completed status retained");
        check(strcmp(rt_process_read_stdout(pid), "") == 0 && rt_process_stdout_state(pid) == 1, "repeated EOF read");
    }
    check(rt_process_close_piped(pid), "owner closed");
    check(rt_process_stdout_state(pid) == -1 && receipt(pid, -1, 0), "closed owner rejected");
}
static void normal_control(int code) {
    char script[128];
#ifdef _WIN32
    snprintf(script, sizeof(script), "echo observed-marker& exit /b %d", code);
#else
    snprintf(script, sizeof(script), "printf observed-marker; exit %d", code);
#endif
    script_control(script, code, 0);
}
static void async_owner_separation_control(void) {
#ifdef _WIN32
    const char* args[] = {"/C", "exit /b 7"};
    const char* executable = "C:\\Windows\\System32\\cmd.exe";
#else
    const char* args[] = {"-c", "exit 7"};
    const char* executable = "/bin/sh";
#endif
    int64_t async_owner = rt_process_spawn_async(executable, args, 2);
    check(async_owner > 0, "genuine separate async owner spawned");
    if (async_owner <= 0) return;
    check(rt_process_stdout_state(async_owner) == -1 && receipt(async_owner, -1, 0),
        "piped observer does not adopt async owner");
    check(rt_process_wait(async_owner, 5000) == 7, "async wait still owns actual exit7");
}

#ifndef _WIN32
struct ConcurrentControl { int64_t pid; atomic_int started, done, invalid; };
static void* observe_while_closing(void* data) {
    struct ConcurrentControl* test = data;
    atomic_store(&test->started, 1);
    for (int count = 0; count < 1000 && !atomic_load(&test->done); ++count) {
        struct SimplePipedObservationV1 out;
        simple_piped_owner_observe_v1(test->pid, 1, &out, sizeof(out));
        if (out.version != 1 || (out.owner_error == 0 &&
            (out.stdout_state < -1 || out.stdout_state > 1))) atomic_store(&test->invalid, 1);
        pause_poll();
    }
    return NULL;
}
static void error_and_close_controls(void) {
    int64_t pid = spawn_script("printf '\\377'; exit 0");
    check(pid > 0, "invalidUTF8 real child");
    if (pid > 0) {
        for (int tick = 0; tick < 1000 && rt_process_stdout_state(pid) == 0; ++tick) {
            (void)rt_process_read_stdout(pid); pause_poll();
        }
        check(rt_process_stdout_state(pid) == -1 && receipt(pid, -1, 0), "real malformedUTF8 fails");
        check(rt_process_close_piped(pid), "malformed peer closed");
    }
    pid = spawn_script("read line; exit 0");
    check(pid > 0, "close race real child"); if (pid <= 0) return;
    struct ConcurrentControl race = { .pid = pid, .started = 0, .done = 0, .invalid = 0 };
    pthread_t observer;
    int created = pthread_create(&observer, NULL, observe_while_closing, &race);
    check(created == 0, "observer thread created");
    if (created != 0) { rt_process_close_piped(pid); return; }
    for (int tick = 0; tick < 1000 && !atomic_load(&race.started); ++tick) pause_poll();
    check(atomic_load(&race.started), "concurrent observation started");
    check(rt_process_close_piped(pid), "close while observing");
    atomic_store(&race.done, 1); pthread_join(observer, NULL);
    check(!atomic_load(&race.invalid), "race snapshots preserve owner contract");
    check(rt_process_stdout_state(pid) == -1 && receipt(pid, -1, 0), "retired slot not adopted");
    normal_control(0); /* Reuse the vacated owner slot through actual spawn. */
    check(receipt(pid, -1, 0), "old PID remains invalid after slot reuse");
}
#endif
#ifdef _WIN32
static int64_t spawn_self_peer(const char* mode) {
    wchar_t wide[32768]; char executable[32768];
    DWORD n = GetModuleFileNameW(NULL, wide, 32768);
    if (!n || n >= 32768 || !WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS,
        wide, -1, executable, sizeof(executable), NULL, NULL)) return -1;
    SplArray* args = rt_array_new(1); int64_t flag = text(mode);
    if (!args || !rt_array_push(args, flag)) return -1;
    int64_t pid = rt_process_spawn_piped(executable, args);
    rt_array_free(args); rt_string_free(flag); return pid;
}
static void windows_error_and_pending_controls(void) {
    int64_t pid = spawn_self_peer("--invalid-utf8-peer");
    check(pid > 0, "real Windows malformed peer");
    if (pid > 0) {
        for (int tick = 0; tick < 1000 && rt_process_stdout_state(pid) == 0; ++tick) {
            (void)rt_process_read_stdout(pid); pause_poll();
        }
        check(rt_process_stdout_state(pid) == -1 && receipt(pid, -1, 0), "Windows malformed stream fails");
        check(rt_process_close_piped(pid), "Windows malformed peer closes");
    }
    pid = spawn_self_peer("--eof-before-exit-peer");
    check(pid > 0, "real Windows EOF-before-exit peer");
    if (pid > 0) {
        for (int tick = 0; tick < 1000 && rt_process_stdout_state(pid) == 0; ++tick) {
            (void)rt_process_read_stdout(pid); pause_poll();
        }
        check(rt_process_stdout_state(pid) == 1 && receipt(pid, 0, 0), "Windows EOF alone remains pending");
        check(release_eof_peer(pid), "release Windows EOF-blocked child");
        for (int tick = 0; tick < 1000 && !receipt(pid, 1, 7); ++tick) pause_poll();
        check(receipt(pid, 1, 7), "Windows delayed nonzero exit observed");
        check(rt_process_close_piped(pid), "Windows delayed peer closes");
    }
}
#endif
int main(int argc, char** argv) {
#ifdef _WIN32
    if (argc == 2 && strcmp(argv[1], "--invalid-utf8-peer") == 0) {
        unsigned char invalid = 255; DWORD written;
        return WriteFile(GetStdHandle(STD_OUTPUT_HANDLE), &invalid, 1, &written, NULL) && written == 1 ? 0 : 97;
    }
    if (argc == 2 && strcmp(argv[1], "--eof-before-exit-peer") == 0) {
        HANDLE output = GetStdHandle(STD_OUTPUT_HANDLE);
        HANDLE error = GetStdHandle(STD_ERROR_HANDLE);
        CloseHandle(output);
        if (error != output) CloseHandle(error);
        char acknowledgement[3]; DWORD total = 0;
        while (total < 3) {
            DWORD n = 0;
            if (!ReadFile(GetStdHandle(STD_INPUT_HANDLE), acknowledgement + total,
                3 - total, &n, NULL) || n == 0) return 98;
            total += n;
        }
        return memcmp(acknowledgement, "go\n", 3) == 0 ? 7 : 99;
    }
#else
    (void)argc; (void)argv;
#endif
    check(rt_process_stdout_state(-1) == -1 && receipt(-1, -1, 0), "invalid owner rejected");
    check(rt_process_stdout_state(2147483647) == -1 && receipt(2147483647, -1, 0), "unknown owner rejected");
    normal_control(0); normal_control(7);
    async_owner_separation_control();
#ifdef _WIN32
    normal_control(259);
    windows_error_and_pending_controls();
#else
    script_control("printf observed-marker; kill -TERM $$", 143, 0);
    script_control("printf observed-marker; exec 1>&- 2>&-; IFS= read -r ack; [ \"$ack\" = go ] || exit 99; exit 7", 7, 1);
    error_and_close_controls();
#endif
    printf("SELFCHECK %s (%d failures)\n", failures ? "FAILED" : "PASSED", failures);
    return failures ? 1 : 0;
}
