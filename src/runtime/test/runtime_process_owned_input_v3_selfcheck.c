#include "runtime.h"

#include <assert.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

static int64_t monotonic_ms(void) {
    struct timespec value;
    assert(clock_gettime(CLOCK_MONOTONIC, &value) == 0);
    return (int64_t)value.tv_sec * 1000 + value.tv_nsec / 1000000;
}

int main(void) {
    static uint8_t input[131073];
    memset(input, 'q', sizeof(input));
    input[17] = 0;
    const char* argv[] = {"/bin/sh", "-c",
        "(yes e | head -c 131073 >&2) & od -An -tu1 | tr -s ' ' | head -c 64; wait", NULL};
    RtOwnedProcessTokenV2 token = {0, 0};
    RtOwnedProcessStartReceiptV2 start;
    assert(rt_process_owned_start_v3(argv[0], argv, input, sizeof(input),
                                     4000, 20, 262144, &token, &start));
    assert(start.version == RT_OWNED_PROCESS_INPUT_VERSION && start.accepted);
    RtOwnedProcessInputReceiptV3 admitted_receipt;
    assert(rt_process_owned_input_receipt_v3(token, &admitted_receipt));
    input[0] = 'x'; /* The admitted lease must already own its immutable copy. */

    RtOwnedProcessPollReceiptV2 poll_receipt = {0};
    char out[128], err[8192];
    char first_output[128] = {0};
    do {
        assert(rt_process_owned_poll_v2(token, 20, out, sizeof(out), err, sizeof(err),
                                        &poll_receipt));
        if (!first_output[0] && out[0]) strcpy(first_output, out);
    } while (!poll_receipt.terminal);
    do {
        assert(rt_process_owned_poll_v2(token, 0, out, sizeof(out), err, sizeof(err),
                                        &poll_receipt));
    } while (out[0] || err[0]);

    RtOwnedProcessInputReceiptV3 input_receipt;
    assert(rt_process_owned_input_receipt_v3(token, &input_receipt));
    assert(input_receipt.input_bytes_accepted == sizeof(input));
    assert(input_receipt.input_bytes_written == sizeof(input));
    assert(memcmp(input_receipt.input_sha256, admitted_receipt.input_sha256,
                  sizeof(input_receipt.input_sha256)) == 0);
    assert(input_receipt.stdin_closed && input_receipt.terminal && input_receipt.reaped);
    assert(strstr(first_output, "113 113") != NULL); /* original 'q', not later 'x' */

    RtOwnedProcessResultV2 result;
    assert(rt_process_owned_result_v2(token, &result));
    assert(result.reaped && result.exit_code == 0);
    assert(rt_process_owned_collect_v2(token, &result));

    const char* early_argv[] = {"/bin/sh", "-c", "exit 0", NULL};
    assert(rt_process_owned_start_v3(early_argv[0], early_argv, input, sizeof(input),
                                     1000, 20, 0, &token, &start));
    do (void)rt_process_owned_poll_v2(token, 20, out, sizeof(out), err, sizeof(err),
                                      &poll_receipt); while (!poll_receipt.terminal);
    assert(!rt_process_owned_input_receipt_v3(token, &input_receipt));
    assert(input_receipt.reaped && input_receipt.stdin_closed &&
           input_receipt.input_bytes_written < input_receipt.input_bytes_accepted &&
           input_receipt.runtime_error == EPIPE);
    assert(!rt_process_owned_collect_v2(token, &result) && result.runtime_error == EPIPE);

    assert(rt_process_owned_start_v2(early_argv[0], early_argv, 1000, 20, 0,
                                     &token, &start));
    assert(!rt_process_owned_input_receipt_v3(token, &input_receipt));
    assert(input_receipt.runtime_error == EPROTO);
    do assert(rt_process_owned_poll_v2(token, 20, out, sizeof(out), err, sizeof(err),
                                       &poll_receipt)); while (!poll_receipt.terminal);
    assert(rt_process_owned_collect_v2(token, &result));
    assert(!rt_process_owned_input_receipt_v3(token, &input_receipt));
    assert(input_receipt.runtime_error == ESTALE);

    const char* empty_argv[] = {"/bin/sh", "-c", "test -z \"$(cat)\"", NULL};
    assert(rt_process_owned_start_v3(empty_argv[0], empty_argv, NULL, 0, 1000, 20, 0,
                                     &token, &start));
    assert(rt_process_owned_input_receipt_v3(token, &input_receipt));
    assert(input_receipt.stdin_closed && input_receipt.input_bytes_accepted == 0 &&
           input_receipt.input_bytes_written == 0);
    do assert(rt_process_owned_poll_v2(token, 20, out, sizeof(out), err, sizeof(err),
                                       &poll_receipt)); while (!poll_receipt.terminal);
    assert(rt_process_owned_collect_v2(token, &result));

    /* A concurrently started child must not inherit another lease's parent
     * pipe end and delay that lease's EOF until the unrelated child exits. */
    const uint8_t one_byte[] = {'z'};
    const char* eof_argv[] = {"/bin/sh", "-c", "cat >/dev/null", NULL};
    const char* sleeper_argv[] = {"/bin/sh", "-c", "sleep 0.5", NULL};
    RtOwnedProcessTokenV2 eof_token, sleeper_token;
    assert(rt_process_owned_start_v3(eof_argv[0], eof_argv, one_byte, sizeof(one_byte),
                                     1000, 20, 0, &eof_token, &start));
    assert(rt_process_owned_start_v3(sleeper_argv[0], sleeper_argv, NULL, 0,
                                     1000, 20, 0, &sleeper_token, &start));
    int64_t eof_started = monotonic_ms();
    do assert(rt_process_owned_poll_v2(eof_token, 20, out, sizeof(out), err, sizeof(err),
                                       &poll_receipt)); while (!poll_receipt.terminal);
    assert(monotonic_ms() - eof_started < 400);
    assert(rt_process_owned_collect_v2(eof_token, &result));
    do assert(rt_process_owned_poll_v2(sleeper_token, 20, out, sizeof(out), err, sizeof(err),
                                       &poll_receipt)); while (!poll_receipt.terminal);
    assert(rt_process_owned_collect_v2(sleeper_token, &result));
    puts("runtime_process_owned_input_v3_selfcheck: PASS");
    return 0;
}
