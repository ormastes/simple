#include "runtime.h"

#include <assert.h>
#include <errno.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define SLOT_COUNT 16

void rt_process_owned_test_force_collision(RtOwnedProcessTokenV2 token, int count);
void rt_process_owned_test_force_signal_failure(int count);
void rt_process_owned_test_force_read_failure(int count);
bool rt_process_owned_test_legacy_cancel_v2(RtOwnedProcessTokenV2 token);

typedef struct RunThread {
    const char* script;
    int ok;
    RtOwnedProcessReceipt receipt;
} RunThread;

static int64_t now_ms(void) {
    struct timespec ts;
    assert(clock_gettime(CLOCK_MONOTONIC, &ts) == 0);
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

static void* run_script(void* opaque) {
    RunThread* run = (RunThread*)opaque;
    const char* argv[] = {"/bin/sh", "-c", run->script, NULL};
    char out[8], err[8];
    run->ok = rt_process_run_owned_bounded(argv[0], argv, 2000, 7,
                                            out, sizeof(out), err, sizeof(err),
                                            &run->receipt);
    return NULL;
}

int main(void) {
    char out[32], err[32];
    RtOwnedProcessReceipt receipt;

    /* V2 returns a live, non-derived capability before the child exits. */
    const char* async_argv[] = {"/bin/sh", "-c", "printf ready; sleep 0.2; printf done", NULL};
    RtOwnedProcessTokenV2 async_token;
    RtOwnedProcessStartReceiptV2 async_start;
    int64_t async_started = now_ms();
    assert(rt_process_owned_start_v2(async_argv[0], async_argv, 2000, 50, 31,
                                     &async_token, &async_start));
    assert(now_ms() - async_started < 150);
    assert(async_start.accepted && (async_token.high != 0 || async_token.low != 0));
    assert(!rt_process_owned_test_legacy_cancel_v2(async_token));
    RtOwnedProcessPollReceiptV2 async_poll;
    char async_out[32], async_err[8];
    assert(rt_process_owned_poll_v2(async_token, 50, async_out, sizeof(async_out),
                                    async_err, sizeof(async_err), &async_poll));
    assert(async_poll.live && strstr(async_out, "ready") != NULL);
    for (int i = 0; i < 100 && !async_poll.terminal; i++) {
        assert(rt_process_owned_poll_v2(async_token, 20, async_out, sizeof(async_out),
                                        async_err, sizeof(async_err), &async_poll));
    }
    assert(async_poll.terminal && async_poll.reaped);
    RtOwnedProcessResultV2 async_result;
    assert(rt_process_owned_result_v2(async_token, &async_result));
    assert(async_result.exit_code == 0 && async_result.reaped);
    RtOwnedProcessTokenV2 stale_token = async_token;
    assert(rt_process_owned_collect_v2(async_token, &async_result));
    assert(!rt_process_owned_result_v2(stale_token, &async_result));
    assert(async_result.runtime_error == ESTALE);

    /* Capture is globally bounded across both streams and a zero-buffer poll
     * drains only into lease-owned storage.  A terminal result remains valid
     * before the owner consumes those bytes; collect does not. */
    const char* retained_argv[] = {"/bin/sh", "-c", "printf ab; printf cd >&2", NULL};
    RtOwnedProcessTokenV2 retained_token;
    assert(rt_process_owned_start_v2(retained_argv[0], retained_argv, 2000, 20, 4,
                                     &retained_token, &async_start));
    memset(&async_poll, 0, sizeof(async_poll));
    for (int i = 0; i < 100 && !async_poll.terminal; i++)
        assert(rt_process_owned_poll_v2(retained_token, 20, NULL, 0, NULL, 0, &async_poll));
    assert(async_poll.terminal && async_poll.stdout_bytes_kept + async_poll.stderr_bytes_kept == 4);
    assert(rt_process_owned_result_v2(retained_token, &async_result));
    assert(!rt_process_owned_collect_v2(retained_token, &async_result));
    assert(async_result.runtime_error == EBUSY);
    assert(rt_process_owned_poll_v2(retained_token, 0, async_out, sizeof(async_out),
                                    async_err, sizeof(async_err), &async_poll));
    assert(strcmp(async_out, "ab") == 0 && strcmp(async_err, "cd") == 0);
    assert(rt_process_owned_collect_v2(retained_token, &async_result));

    /* Cancellation synchronously terminates/reaps, while lease-owned capture
     * preserves bytes for a later draining poll. */
    const char* cancel_v2_argv[] = {"/bin/sh", "-c", "trap '' TERM; printf x; sleep 5", NULL};
    RtOwnedProcessTokenV2 cancel_v2_token;
    assert(rt_process_owned_start_v2(cancel_v2_argv[0], cancel_v2_argv, 2000, 20, 1,
                                     &cancel_v2_token, &async_start));
    usleep(20000);
    RtOwnedProcessCancelReceipt cancel_v2_receipt;
    assert(rt_process_owned_cancel_v2(cancel_v2_token, &cancel_v2_receipt));
    assert(cancel_v2_receipt.accepted && cancel_v2_receipt.term_sent &&
           cancel_v2_receipt.runtime_error == 0);
    assert(rt_process_owned_result_v2(cancel_v2_token, &async_result));
    assert(async_result.reaped && async_result.stdout_bytes_kept == 1);
    assert(!rt_process_owned_collect_v2(cancel_v2_token, &async_result));
    assert(async_result.runtime_error == EBUSY);
    assert(rt_process_owned_poll_v2(cancel_v2_token, 0, async_out, sizeof(async_out),
                                    async_err, sizeof(async_err), &async_poll));
    assert(strstr(async_out, "x") != NULL);
    assert(async_poll.terminal && async_poll.term_sent && async_poll.reaped &&
           async_poll.stdout_bytes_kept == 1);
    assert(rt_process_owned_collect_v2(cancel_v2_token, &async_result));
    assert(async_result.cancel_requested);

    /* A capture failure must not make synchronous cancellation abandon a
     * live TERM-resistant child.  The API reports EIO, but still reaches a
     * reaped terminal lease that can be collected. */
    RtOwnedProcessTokenV2 cancel_error_token;
    assert(rt_process_owned_start_v2(cancel_v2_argv[0], cancel_v2_argv, 2000, 20, 8,
                                     &cancel_error_token, &async_start));
    usleep(20000);
    rt_process_owned_test_force_read_failure(1);
    assert(!rt_process_owned_cancel_v2(cancel_error_token, &cancel_v2_receipt));
    assert(cancel_v2_receipt.accepted && cancel_v2_receipt.term_sent &&
           cancel_v2_receipt.runtime_error == EIO);
    assert(!rt_process_owned_result_v2(cancel_error_token, &async_result));
    assert(async_result.reaped && async_result.cancel_requested &&
           async_result.runtime_error == EIO);
    assert(!rt_process_owned_collect_v2(cancel_error_token, &async_result));
    assert(async_result.reaped && async_result.runtime_error == EIO);

    /* A delayed owner poll must drain both streams beyond two combined drain
     * quanta without silently losing pipe bytes. */
    const char* burst_v2_argv[] = {"/bin/sh", "-c",
        "(yes o | head -c 131073) & (yes e | head -c 131073 >&2) & wait; sleep 5", NULL};
    RtOwnedProcessTokenV2 burst_token;
    assert(rt_process_owned_start_v2(burst_v2_argv[0], burst_v2_argv, 4000, 20, 300000,
                                     &burst_token, &async_start));
    usleep(50000); /* Intentionally do not poll while both pipes fill. */
    static char burst_out[140000], burst_err[140000];
    size_t burst_out_len = 0, burst_err_len = 0;
    char burst_out_piece[8192], burst_err_piece[8192];
    memset(&async_poll, 0, sizeof(async_poll));
    for (int i = 0; i < 200 && (!async_poll.terminal ||
                                burst_out_len < 131073 || burst_err_len < 131073); i++) {
        assert(rt_process_owned_poll_v2(burst_token, 20, burst_out_piece, sizeof(burst_out_piece),
                                        burst_err_piece, sizeof(burst_err_piece), &async_poll));
        size_t out_piece_len = strlen(burst_out_piece), err_piece_len = strlen(burst_err_piece);
        assert(burst_out_len + out_piece_len < sizeof(burst_out));
        assert(burst_err_len + err_piece_len < sizeof(burst_err));
        memcpy(burst_out + burst_out_len, burst_out_piece, out_piece_len); burst_out_len += out_piece_len;
        memcpy(burst_err + burst_err_len, burst_err_piece, err_piece_len); burst_err_len += err_piece_len;
    }
    assert(burst_out_len == 131073 && burst_err_len == 131073);
    /* The same delayed lease then cancels without caller buffers.  Its
     * already-delivered bytes stay exact, while cancel owns TERM/KILL/reap. */
    assert(rt_process_owned_cancel_v2(burst_token, &cancel_v2_receipt));
    assert(cancel_v2_receipt.accepted && cancel_v2_receipt.term_sent);
    assert(rt_process_owned_result_v2(burst_token, &async_result));
    assert(async_result.reaped && async_result.cancel_requested);
    assert(!async_result.stdout_truncated && !async_result.stderr_truncated);
    assert(async_result.stdout_bytes_kept == 131073 && async_result.stderr_bytes_kept == 131073);
    assert(burst_out[0] == 'o' && burst_out[131072] == 'o');
    assert(burst_err[0] == 'e' && burst_err[131072] == 'e');
    assert(rt_process_owned_collect_v2(burst_token, &async_result));

    /* Natural exit immediately before cancellation is reconciled as terminal,
     * not misclassified as stale identity. */
    const char* quick_v2_argv[] = {"/bin/sh", "-c", "exit 0", NULL};
    RtOwnedProcessTokenV2 quick_token;
    assert(rt_process_owned_start_v2(quick_v2_argv[0], quick_v2_argv, 2000, 20, 0,
                                     &quick_token, &async_start));
    usleep(20000);
    assert(rt_process_owned_cancel_v2(quick_token, &cancel_v2_receipt));
    assert(cancel_v2_receipt.accepted && cancel_v2_receipt.runtime_error == 0);
    assert(rt_process_owned_result_v2(quick_token, &async_result));
    assert(async_result.reaped && async_result.exit_code == 0);
    assert(rt_process_owned_collect_v2(quick_token, &async_result));

    /* Concurrent live leases receive distinct opaque tokens. */
    const char* pair_argv[] = {"/bin/sh", "-c", "sleep 0.1", NULL};
    RtOwnedProcessTokenV2 pair_a, pair_b;
    assert(rt_process_owned_start_v2(pair_argv[0], pair_argv, 2000, 20, 0, &pair_a, &async_start));
    rt_process_owned_test_force_collision(pair_a, 1);
    assert(rt_process_owned_start_v2(pair_argv[0], pair_argv, 2000, 20, 0, &pair_b, &async_start));
    assert(pair_a.high != pair_b.high || pair_a.low != pair_b.low);
    assert(rt_process_owned_cancel_v2(pair_a, &cancel_v2_receipt));
    assert(rt_process_owned_collect_v2(pair_a, &async_result));
    assert(rt_process_owned_cancel_v2(pair_b, &cancel_v2_receipt));
    assert(rt_process_owned_collect_v2(pair_b, &async_result));

    /* Forced signal failure after an observed natural exit reconciles to reap. */
    assert(rt_process_owned_start_v2(quick_v2_argv[0], quick_v2_argv, 2000, 20, 0,
                                     &quick_token, &async_start));
    usleep(20000);
    rt_process_owned_test_force_signal_failure(1);
    assert(rt_process_owned_cancel_v2(quick_token, &cancel_v2_receipt));
    assert(cancel_v2_receipt.accepted && cancel_v2_receipt.runtime_error == 0);
    assert(rt_process_owned_collect_v2(quick_token, &async_result));

    /* Repeated collect/start turnover exercises pidfd close-before-unpublish. */
    for (int i = 0; i < 32; i++) {
        assert(rt_process_owned_start_v2(quick_v2_argv[0], quick_v2_argv, 2000, 20, 0,
                                         &quick_token, &async_start));
        assert(rt_process_owned_cancel_v2(quick_token, &cancel_v2_receipt));
        assert(rt_process_owned_collect_v2(quick_token, &async_result));
    }

    const char* distinct[] = {"/bin/sh", "-c", "printf stdout; printf stderr >&2", NULL};
    assert(rt_process_run_owned_bounded(distinct[0], distinct, 2000, 31,
                                        out, sizeof(out), err, sizeof(err), &receipt));
    assert(strcmp(out, "stdout") == 0 && strcmp(err, "stderr") == 0);
    assert(receipt.reaped && receipt.exit_code == 0 && receipt.start_identity > 0);
    assert(receipt.process_group_id == receipt.pid);
    assert(!rt_process_owned_terminate(getpid(), receipt.start_identity));
    assert(!rt_process_owned_terminate(receipt.pid, receipt.start_identity));

    const char* zero[] = {"/bin/sh", "-c", "printf abc; printf def >&2", NULL};
    assert(rt_process_run_owned_bounded(zero[0], zero, 2000, 0,
                                        NULL, 0, NULL, 0, &receipt));
    assert(receipt.stdout_bytes_seen == 3 && receipt.stderr_bytes_seen == 3);
    assert(receipt.stdout_bytes_kept == 0 && receipt.stderr_bytes_kept == 0);
    assert(receipt.stdout_truncated && receipt.stderr_truncated);

    char cap1_out[1], cap1_err[1];
    assert(rt_process_run_owned_bounded(zero[0], zero, 2000, 1,
                                        cap1_out, 1, cap1_err, 1, &receipt));
    assert(cap1_out[0] == '\0' && cap1_err[0] == '\0');
    assert(receipt.stdout_bytes_seen == 3 && receipt.stdout_bytes_kept == 0);

    const char* continuous[] = {"/bin/sh", "-c", "yes x | head -c 200000", NULL};
    assert(rt_process_run_owned_bounded(continuous[0], continuous, 2000, 7,
                                        out, sizeof(out), err, sizeof(err), &receipt));
    assert(receipt.reaped && receipt.stdout_bytes_seen == 200000);
    assert(receipt.stdout_bytes_kept == 7 && receipt.stdout_truncated);

    const char* held_pipe[] = {"/bin/sh", "-c", "sleep 5 & printf done", NULL};
    int64_t held_started = now_ms();
    assert(rt_process_run_owned_bounded(held_pipe[0], held_pipe, 2000, 31,
                                        out, sizeof(out), err, sizeof(err), &receipt));
    int64_t held_elapsed = now_ms() - held_started;
    assert(receipt.reaped && strcmp(out, "done") == 0);
    assert(held_elapsed < 1000);

    const char* timeout[] = {"/bin/sh", "-c", "trap '' TERM; printf before; printf error >&2; sleep 5", NULL};
    assert(rt_process_run_owned_bounded(timeout[0], timeout, 50, 4,
                                        out, sizeof(out), err, sizeof(err), &receipt));
    assert(receipt.timed_out && receipt.term_sent && receipt.kill_sent && receipt.reaped);
    assert(receipt.identity_revalidated && receipt.stdout_truncated && receipt.stderr_truncated);
    assert(strcmp(out, "befo") == 0 && strcmp(err, "erro") == 0);

    const char* missing[] = {"/definitely/not/a/program", NULL};
    assert(rt_process_run_owned_bounded(missing[0], missing, 2000, 31,
                                        out, sizeof(out), err, sizeof(err), &receipt));
    assert(receipt.reaped && receipt.exit_code == 127 && receipt.runtime_error == 0);

    pthread_t threads[SLOT_COUNT];
    RunThread runs[SLOT_COUNT];
    for (int i = 0; i < SLOT_COUNT; i++) {
        runs[i] = (RunThread){"sleep 0.4", 0, {0}};
        assert(pthread_create(&threads[i], NULL, run_script, &runs[i]) == 0);
    }
    usleep(100000);
    const char* exhausted[] = {"/bin/sh", "-c", "exit 0", NULL};
    assert(!rt_process_run_owned_bounded(exhausted[0], exhausted, 1000, 0,
                                         NULL, 0, NULL, 0, &receipt));
    assert(receipt.runtime_error == EAGAIN);
    for (int i = 0; i < SLOT_COUNT; i++) {
        assert(pthread_join(threads[i], NULL) == 0);
        assert(runs[i].ok && runs[i].receipt.reaped);
    }
    assert(rt_process_run_owned_bounded(exhausted[0], exhausted, 1000, 0,
                                        NULL, 0, NULL, 0, &receipt));
    assert(receipt.reaped);

    char descendant_path[128], cancel_script[320];
    snprintf(descendant_path, sizeof(descendant_path), "/tmp/simple-owned-descendant-%ld", (long)getpid());
    snprintf(cancel_script, sizeof(cancel_script),
             "sleep 5 & child=$!; printf '%%s' \"$child\" > %s; wait", descendant_path);
    RunThread cancelled = {cancel_script, 0, {0}};
    pthread_t cancel_thread;
    assert(pthread_create(&cancel_thread, NULL, run_script, &cancelled) == 0);
    pid_t descendant = 0;
    for (int i = 0; i < 100 && descendant <= 0; i++) {
        FILE* pid_file = fopen(descendant_path, "r");
        if (pid_file) {
            if (fscanf(pid_file, "%d", &descendant) != 1) descendant = 0;
            fclose(pid_file);
        }
        if (descendant <= 0) usleep(10000);
    }
    assert(descendant > 0);
    int64_t cancel_started = now_ms();
    assert(pthread_cancel(cancel_thread) == 0);
    void* cancel_result = NULL;
    assert(pthread_join(cancel_thread, &cancel_result) == 0);
    assert(cancel_result == PTHREAD_CANCELED);
    assert(now_ms() - cancel_started < 1000);
    for (int i = 0; i < 100 && (kill(descendant, 0) == 0 || errno != ESRCH); i++) usleep(10000);
    assert(kill(descendant, 0) != 0 && errno == ESRCH);
    unlink(descendant_path);

    /* Exercise slot/pidfd turnover; stale receipts must never target a later
     * process after the kernel reuses descriptor numbers. */
    RtOwnedProcessReceipt stale = cancelled.receipt;
    for (int i = 0; i < 64; i++) {
        assert(rt_process_run_owned_bounded(exhausted[0], exhausted, 1000, 0,
                                            NULL, 0, NULL, 0, &receipt));
        assert(!rt_process_owned_terminate(stale.pid, stale.start_identity));
    }
    assert(rt_process_run_owned_bounded(exhausted[0], exhausted, 1000, 0,
                                        NULL, 0, NULL, 0, &receipt));

    /* A non-retryable capture read failure is never reported as a clean EOF.
     * The lease becomes terminal with an explicit stream truncation/error. */
    RtOwnedProcessTokenV2 read_error_token;
    const char* read_error_argv[] = {"/bin/sh", "-c", "printf x", NULL};
    assert(rt_process_owned_start_v2(read_error_argv[0], read_error_argv, 1000, 20, 8,
                                     &read_error_token, &async_start));
    usleep(20000);
    rt_process_owned_test_force_read_failure(1);
    memset(&async_poll, 0, sizeof(async_poll));
    for (int i = 0; i < 100 && !async_poll.terminal; i++)
        (void)rt_process_owned_poll_v2(read_error_token, 20, async_out, sizeof(async_out),
                                       async_err, sizeof(async_err), &async_poll);
    assert(async_poll.terminal && async_poll.stdout_truncated && async_poll.runtime_error == EIO);
    assert(!rt_process_owned_result_v2(read_error_token, &async_result));
    assert(async_result.reaped && async_result.stdout_truncated && async_result.runtime_error == EIO);
    /* A terminal provider error still owns a completed result.  Drain any
     * retained bytes, then collect must release the lease while returning the
     * error in both the boolean and result record. */
    assert(rt_process_owned_poll_v2(read_error_token, 0, async_out, sizeof(async_out),
                                    async_err, sizeof(async_err), &async_poll));
    assert(async_poll.terminal && async_poll.runtime_error == EIO);
    assert(!rt_process_owned_collect_v2(read_error_token, &async_result));
    assert(async_result.reaped && async_result.runtime_error == EIO);
    /* Turnover proves the errored terminal lease did not retain its registry
     * slot, pidfd, or capture allocation. */
    assert(rt_process_owned_start_v2(quick_v2_argv[0], quick_v2_argv, 2000, 20, 0,
                                     &quick_token, &async_start));
    assert(rt_process_owned_cancel_v2(quick_token, &cancel_v2_receipt));
    assert(rt_process_owned_collect_v2(quick_token, &async_result));

    puts("runtime_process_owned_selfcheck: PASS");
    return 0;
}
