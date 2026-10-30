/* Windows-native V2 owner contract. Non-Windows execution is SKIP (77), never
 * Windows evidence. Build with RT_PROCESS_OWNED_CORE_ONLY and runtime_process_owned.c. */
#include "runtime.h"
#include <stdio.h>
#if defined(_WIN32)
#include <windows.h>
#ifdef NDEBUG
#error "The Windows owner selfcheck requires active assertions"
#endif
#include <assert.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>

static char self[MAX_PATH];
#include "runtime_process_owned_sha256_private.h"
static RtOwnedProcessTokenV2 start(const char* mode, int64_t timeout, uint64_t cap) {
    const char* args[] = {self, mode, NULL};
    RtOwnedProcessTokenV2 token;
    RtOwnedProcessStartReceiptV2 receipt;
    assert(rt_process_owned_start_v2(self, args, timeout, 20, cap, &token, &receipt));
    assert(receipt.accepted && receipt.runtime_error == 0);
    assert(token.high || token.low);
    return token;
}
static RtOwnedProcessPollReceiptV2 finish(RtOwnedProcessTokenV2 token) {
    RtOwnedProcessPollReceiptV2 receipt = {0};
    ULONGLONG deadline = GetTickCount64() + 5000;
    while (!receipt.terminal && GetTickCount64() < deadline)
        assert(rt_process_owned_poll_v2(token, 20, NULL, 0, NULL, 0, &receipt));
    assert(receipt.terminal && receipt.reaped);
    assert(receipt.stdout_bytes_delivered == 0 && receipt.stderr_bytes_delivered == 0);
    return receipt;
}
static void discard_collect(RtOwnedProcessTokenV2 token) {
    char out[1024], err[1024];
    RtOwnedProcessPollReceiptV2 poll;
    do {
        assert(rt_process_owned_poll_v2(token, 0, out, sizeof(out), err, sizeof(err), &poll));
    } while (poll.stdout_bytes_delivered || poll.stderr_bytes_delivered);
    RtOwnedProcessResultV2 result;
    assert(rt_process_owned_collect_v2(token, &result));
    assert(!rt_process_owned_result_v2(token, &result) && result.runtime_error == RT_OWNED_PROCESS_WINDOWS_STALE_ERROR);
}
static int child_mode(int argc, char** argv) {
    if (argc == 2) {
        if (!strcmp(argv[1], "--stdin-echo")) {
            unsigned char bytes[4096]; DWORD got, written;
            for (;;) {
                if (!ReadFile(GetStdHandle(STD_INPUT_HANDLE), bytes, sizeof(bytes), &got, NULL)) {
                    assert(GetLastError() == ERROR_BROKEN_PIPE); break;
                }
                if (!got) break;
                assert(WriteFile(GetStdHandle(STD_OUTPUT_HANDLE), bytes, got, &written, NULL));
                assert(written == got);
            }
            return 0;
        }
        if (!strcmp(argv[1], "--sleep")) { Sleep(600); return 0; }
        if (!strcmp(argv[1], "--hold")) { Sleep(60000); return 0; }
        if (!strcmp(argv[1], "--exit259")) return 259;
        if (!strcmp(argv[1], "--capture")) {
            DWORD written;
            const char bytes[] = {'a', 0, 'b', 'c', 'd'};
            assert(WriteFile(GetStdHandle(STD_OUTPUT_HANDLE), bytes, sizeof(bytes), &written, NULL));
            assert(WriteFile(GetStdHandle(STD_ERROR_HANDLE), "err", 3, &written, NULL));
            return 3;
        }
        if (!strcmp(argv[1], "--descendant")) {
            char path[MAX_PATH], command[2 * MAX_PATH];
            assert(GetModuleFileNameA(NULL, path, sizeof(path)));
            snprintf(command, sizeof(command), "\"%s\" --hold", path);
            STARTUPINFOA si = {0}; PROCESS_INFORMATION pi = {0};
            si.cb = sizeof(si); si.dwFlags = STARTF_USESTDHANDLES;
            si.hStdInput = GetStdHandle(STD_INPUT_HANDLE);
            si.hStdOutput = GetStdHandle(STD_OUTPUT_HANDLE);
            si.hStdError = GetStdHandle(STD_ERROR_HANDLE);
            assert(CreateProcessA(path, command, NULL, NULL, TRUE, CREATE_NO_WINDOW, NULL, NULL, &si, &pi));
            printf("%lu\n", (unsigned long)pi.dwProcessId); fflush(stdout);
            /* Allow the observer to acquire a HANDLE before leader exit. */
            Sleep(1000);
            CloseHandle(pi.hThread); CloseHandle(pi.hProcess);
            return 0;
        }
    }
    return -1;
}
static void capture_checks(void) {
    RtOwnedProcessTokenV2 token = start("--capture", 2000, 8);
    RtOwnedProcessPollReceiptV2 poll = finish(token);
    assert(poll.stdout_bytes_kept == 5 && poll.stderr_bytes_kept == 3);
    RtOwnedProcessResultV2 result;
    assert(rt_process_owned_result_v2(token, &result) && result.exit_code == 3);
    assert(!rt_process_owned_collect_v2(token, &result) && result.runtime_error == EBUSY);
    char out[4], err[8];
    assert(rt_process_owned_poll_v2(token, 0, out, sizeof(out), err, sizeof(err), &poll));
    assert(poll.stdout_bytes_delivered == 3 && !memcmp(out, "a\0b", 3));
    assert(poll.stderr_bytes_delivered == 3 && !strcmp(err, "err"));
    assert(!rt_process_owned_collect_v2(token, &result) && result.runtime_error == EBUSY);
    assert(rt_process_owned_poll_v2(token, 0, out, sizeof(out), NULL, 0, &poll));
    assert(poll.stdout_bytes_delivered == 2 && !memcmp(out, "cd", 2));
    assert(rt_process_owned_collect_v2(token, &result));
    assert(!rt_process_owned_result_v2(token, &result) && result.runtime_error == RT_OWNED_PROCESS_WINDOWS_STALE_ERROR);

    token = start("--capture", 2000, 4);
    poll = finish(token);
    assert(poll.stdout_bytes_kept + poll.stderr_bytes_kept == 4);
    assert(poll.stdout_truncated || poll.stderr_truncated);
    discard_collect(token);
    puts("PASS: capture binary-prefix retention partial-delivery collect-busy stale-token shared-cap");
}

static void lifecycle_checks(void) {
    RtOwnedProcessTokenV2 token = start("--sleep", 0, 0);
    RtOwnedProcessPollReceiptV2 poll;
    RtOwnedProcessResultV2 result;
    ULONGLONG began = GetTickCount64();
    finish(token);
    assert(GetTickCount64() - began >= 400);
    assert(rt_process_owned_result_v2(token, &result) && !result.timed_out);
    discard_collect(token);

    token = start("--hold", 50, 0);
    poll = finish(token);
    assert(poll.timed_out && poll.kill_sent);
    discard_collect(token);

    token = start("--hold", 0, 0);
    RtOwnedProcessCancelReceipt cancel;
    assert(rt_process_owned_cancel_v2(token, &cancel) && cancel.accepted && cancel.term_sent);
    assert(rt_process_owned_result_v2(token, &result) && result.cancel_requested && result.reaped);
    discard_collect(token);

    token = start("--exit259", 2000, 0);
    finish(token);
    assert(rt_process_owned_result_v2(token, &result) && result.exit_code == 259);
    discard_collect(token);

    token = start("--descendant", 0, 64);
    char witness[64];
    do {
        assert(rt_process_owned_poll_v2(token, 100, witness, sizeof(witness), NULL, 0, &poll));
    } while (!poll.stdout_bytes_delivered && !poll.terminal);
    assert(poll.stdout_bytes_delivered > 0);
    DWORD descendant_pid = (DWORD)strtoul(witness, NULL, 10);
    assert(descendant_pid > 0);
    HANDLE descendant = OpenProcess(SYNCHRONIZE, FALSE, descendant_pid);
    assert(descendant);
    finish(token);
    assert(rt_process_owned_result_v2(token, &result) && result.kill_sent && !result.timed_out);
    assert(WaitForSingleObject(descendant, 0) == WAIT_OBJECT_0);
    CloseHandle(descendant);
    discard_collect(token);
    puts("PASS: lifecycle unlimited-work deadline cancellation exit259 descendant-handle-wait");
}

typedef struct CleanupBatch { RtOwnedProcessTokenV2* tokens; int count; } CleanupBatch;
static DWORD WINAPI cleanup_worker(LPVOID opaque) {
    CleanupBatch* batch = (CleanupBatch*)opaque;
    for (int i = 0; i < batch->count; i++) {
        RtOwnedProcessCancelReceipt cancel;
        assert(rt_process_owned_cancel_v2(batch->tokens[i], &cancel));
        discard_collect(batch->tokens[i]);
    }
    return 0;
}

static void concurrency_checks(void) {
    /* More than the automatic 64-process governor: leases must coexist. */
    RtOwnedProcessTokenV2 leases[80];
    for (int i = 0; i < 80; i++) {
        leases[i] = start("--hold", 0, 0);
        for (int j = 0; j < i; j++)
            assert(leases[i].high != leases[j].high || leases[i].low != leases[j].low);
    }
    for (int i = 0; i < 80; i++) {
        RtOwnedProcessPollReceiptV2 poll;
        assert(rt_process_owned_poll_v2(leases[i], 0, NULL, 0, NULL, 0, &poll));
        assert(poll.live && !poll.reaped);
    }
    CleanupBatch batches[] = {{leases, 40}, {leases + 40, 40}};
    HANDLE threads[2];
    threads[0] = CreateThread(NULL, 0, cleanup_worker, &batches[0], 0, NULL);
    threads[1] = CreateThread(NULL, 0, cleanup_worker, &batches[1], 0, NULL);
    assert(threads[0] && threads[1]);
    assert(WaitForMultipleObjects(2, threads, TRUE, 15000) == WAIT_OBJECT_0);
    CloseHandle(threads[0]); CloseHandle(threads[1]);
    puts("PASS: concurrency 80-unique-live-leases threaded-cancel-poll-collect");
}

static void admission_checks(void) {
    RtOwnedProcessTokenV2 token;
    RtOwnedProcessStartReceiptV2 receipt;
    const char* args[] = {self, "--hold", NULL};
    assert(!rt_process_owned_start_v2(self, args, -1, 0, 0, &token, &receipt));
    assert(!receipt.accepted && receipt.runtime_error == EINVAL && !token.high && !token.low);
    const char* absent = "C:\\simple-runtime-nonexistent-directory\\missing-owned-child.exe";
    assert(!rt_process_owned_start_v2(absent, args, 1000, 0, 0, &token, &receipt));
    DWORD before, after;
    assert(GetProcessHandleCount(GetCurrentProcess(), &before));
    for (int i = 0; i < 16; i++) {
        assert(!rt_process_owned_start_v2(absent, args, 1000, 0, 0, &token, &receipt));
        assert(!receipt.accepted && receipt.runtime_error == ENOENT && !token.high && !token.low);
    }
    assert(GetProcessHandleCount(GetCurrentProcess(), &after) && before == after);
    RtOwnedProcessPollReceiptV2 poll;
    token.high = 0; token.low = 0;
    assert(!rt_process_owned_poll_v2(token, 0, NULL, 0, NULL, 0, &poll));
    assert(poll.runtime_error == RT_OWNED_PROCESS_WINDOWS_STALE_ERROR);
    puts("PASS: admission invalid-budget missing-executable zero-authority no-handle-leak");
}

static void input_checks(void) {
    enum { LENGTH = 131073 };
    unsigned char* input = malloc(LENGTH);
    unsigned char* echoed = malloc(LENGTH + 1);
    assert(input && echoed);
    for (size_t i = 0; i < LENGTH; i++) input[i] = (unsigned char)(i % 251);
    unsigned char digest[32]; owned_sha256(input, LENGTH, digest);
    const char* args[] = {self, "--stdin-echo", NULL};
    RtOwnedProcessTokenV2 token;
    RtOwnedProcessStartReceiptV2 start_receipt;
    assert(rt_process_owned_start_v3(self, args, input, LENGTH, 5000, 20, LENGTH,
        &token, &start_receipt));
    assert(start_receipt.accepted && start_receipt.version == RT_OWNED_PROCESS_INPUT_VERSION);
    memset(input, 0xcc, LENGTH); /* The caller no longer owns the accepted bytes. */
    RtOwnedProcessInputReceiptV3 receipt;
    assert(rt_process_owned_input_receipt_v3(token, &receipt));
    assert(receipt.input_bytes_accepted == LENGTH && !memcmp(receipt.input_sha256, digest, 32));
    RtOwnedProcessPollReceiptV2 poll = {0}; size_t kept = 0;
    ULONGLONG deadline = GetTickCount64() + 6000;
    while ((!poll.terminal || kept < LENGTH) && GetTickCount64() < deadline) {
        char out[4097];
        assert(rt_process_owned_poll_v2(token, 20, out, sizeof(out), NULL, 0, &poll));
        assert(kept + poll.stdout_bytes_delivered <= LENGTH);
        memcpy(echoed + kept, out, (size_t)poll.stdout_bytes_delivered);
        kept += (size_t)poll.stdout_bytes_delivered;
    }
    assert(poll.terminal && kept == LENGTH);
    for (size_t i = 0; i < LENGTH; i++) assert(echoed[i] == (unsigned char)(i % 251));
    assert(rt_process_owned_input_receipt_v3(token, &receipt));
    assert(receipt.stdin_closed && receipt.terminal && receipt.reaped);
    assert(receipt.input_bytes_written == LENGTH && !memcmp(receipt.input_sha256, digest, 32));
    discard_collect(token);
    assert(!rt_process_owned_input_receipt_v3(token, &receipt));
    assert(receipt.runtime_error == RT_OWNED_PROCESS_WINDOWS_STALE_ERROR);

    assert(rt_process_owned_start_v3(self, args, NULL, 0, 2000, 20, 0, &token, &start_receipt));
    finish(token);
    assert(rt_process_owned_input_receipt_v3(token, &receipt));
    owned_sha256(NULL, 0, digest);
    assert(receipt.stdin_closed && receipt.input_bytes_accepted == 0 && receipt.input_bytes_written == 0);
    assert(!memcmp(receipt.input_sha256, digest, 32));
    discard_collect(token);

    token = start("--sleep", 0, 0);
    assert(!rt_process_owned_input_receipt_v3(token, &receipt) && receipt.runtime_error == EINVAL);
    finish(token); discard_collect(token);
    assert(!rt_process_owned_start_v3(self, args, NULL, 1, 0, 0, 0, &token, &start_receipt));
    assert(!start_receipt.accepted && !token.high && !token.low && start_receipt.runtime_error == EINVAL);
    assert(!rt_process_owned_start_v3(self, args, input, RT_OWNED_PROCESS_MAX_INPUT_BYTES + 1ULL,
        0, 0, 0, &token, &start_receipt));
    assert(!token.high && !token.low && start_receipt.runtime_error == EINVAL);
    free(input); free(echoed);
    puts("PASS: input immutable-binary-snapshot sha256 partial-writes empty-eof stale-version admission");
}

static void input_backpressure_checks(void) {
    unsigned char* input = malloc(RT_OWNED_PROCESS_MAX_INPUT_BYTES);
    assert(input); memset(input, 0x41, RT_OWNED_PROCESS_MAX_INPUT_BYTES);
    const char* args[] = {self, "--hold", NULL};
    RtOwnedProcessTokenV2 token;
    RtOwnedProcessStartReceiptV2 start_receipt;
    assert(rt_process_owned_start_v3(self, args, input, RT_OWNED_PROCESS_MAX_INPUT_BYTES,
        0, 20, 0, &token, &start_receipt));
    RtOwnedProcessPollReceiptV2 poll;
    ULONGLONG began = GetTickCount64();
    for (int i = 0; i < 4; i++)
        assert(rt_process_owned_poll_v2(token, 0, NULL, 0, NULL, 0, &poll));
    assert(poll.live && GetTickCount64() - began < 1000);
    /* A blocked stdin reader must not hold up an independent lease. */
    RtOwnedProcessTokenV2 other = start("--exit259", 2000, 0);
    finish(other); discard_collect(other);
    RtOwnedProcessCancelReceipt cancelled;
    assert(rt_process_owned_cancel_v2(token, &cancelled));
    RtOwnedProcessInputReceiptV3 receipt;
    assert(rt_process_owned_input_receipt_v3(token, &receipt));
    assert(receipt.stdin_closed && receipt.terminal && receipt.reaped);
    assert(receipt.input_bytes_accepted == RT_OWNED_PROCESS_MAX_INPUT_BYTES);
    assert(receipt.input_bytes_written < receipt.input_bytes_accepted);
    discard_collect(token);
    free(input);
    puts("PASS: input-backpressure nonblocking-poll independent-lease cancel-completion partial-receipt");
}

int main(int argc, char** argv) {
    int child = child_mode(argc, argv);
    if (child >= 0) return child;
    assert(GetModuleFileNameA(NULL, self, sizeof(self)));
    if (argc > 2 || (argc == 2 && strcmp(argv[1], "--suite-capture") &&
        strcmp(argv[1], "--suite-lifecycle") && strcmp(argv[1], "--suite-concurrency") &&
        strcmp(argv[1], "--suite-admission") && strcmp(argv[1], "--suite-input") &&
        strcmp(argv[1], "--suite-input-backpressure"))) return 2;
    if (argc == 1 || !strcmp(argv[1], "--suite-capture")) capture_checks();
    if (argc == 1 || !strcmp(argv[1], "--suite-lifecycle")) lifecycle_checks();
    if (argc == 1 || !strcmp(argv[1], "--suite-concurrency")) concurrency_checks();
    if (argc == 1 || !strcmp(argv[1], "--suite-admission")) admission_checks();
    if (argc == 1 || !strcmp(argv[1], "--suite-input")) input_checks();
    if (argc == 1 || !strcmp(argv[1], "--suite-input-backpressure")) input_backpressure_checks();
    return 0;
}
#else
int main(void) { puts("SKIP: requires a Windows-native producer"); return 77; }
#endif
