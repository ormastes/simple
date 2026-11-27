/* Run from the repository root:
 * /tmp/runtime_process_observation_v4_darwin_selfcheck
 * cc -std=c11 -O0 -Wall -Wextra -Werror -pthread src/runtime/test/runtime_process_observation_v4_darwin_selfcheck.c src/runtime/runtime_process_tree.c -o /tmp/runtime_process_observation_v4_darwin_selfcheck
 * Native macOS check for the V4 cwd pin foundation, the partial Darwin V4
 * capability mask, and V4 rejection without child authority. Every other
 * owned-process family stays ENOTSUP on Darwin. The live Darwin V4 owner is
 * exercised by runtime_process_observation_v4_darwin_live_selfcheck.c. */
#if !defined(__APPLE__)
#include <stdio.h>
int main(void) { puts("runtime_process_observation_v4_darwin_selfcheck: SKIP (requires macOS)"); return 77; }
#else
#define _DARWIN_C_SOURCE
#define RT_PROCESS_OBSERVATION_V4_TESTING 1
#define RT_OWNED_EXTERNAL_PIN 1 /* This harness stubs the executable pin. */
#include "../runtime.h"
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
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
/* This harness represents every value as an untagged integer. The snapshot
 * adapter linked by runtime_process_owned.c also needs the matching predicate. */
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
static uint8_t executable_digest[32];
static int executable_acquisitions;
int64_t rt_process_acquire_pinned_executable(int64_t handle) {
    (void)handle; executable_acquisitions++; errno = ENOTSUP; return -1;
}
int rt_process_close_pinned_executable_owned_value(int64_t handle) { (void)handle; return 0; }
SplArray* rt_process_pinned_executable_sha256_value(int64_t handle) {
    (void)handle; SplArray* a = rt_array_new(32);
    for (int i = 0; i < 32; i++) assert(rt_array_push(a, executable_digest[i]));
    return a;
}
static void cwd_race_hook(void);
static void cwd_component_hook(const char* component, const char* slash);
#define POV4_CWD_TEST_AFTER_REALPATH() cwd_race_hook()
#define POV4_CWD_TEST_AFTER_COMPONENT(component, slash) cwd_component_hook(component, slash)
#include "../runtime_process_owned.c"

static const char *race_ancestor, *race_saved, *race_target;
static int race_after_component;
static void cwd_race_hook(void) {
    if (!race_ancestor || race_after_component) return;
    assert(rename(race_ancestor, race_saved) == 0);
    assert(symlink(race_target, race_ancestor) == 0);
    race_ancestor = NULL;
}

static void cwd_component_hook(const char* component, const char* slash) {
    if (!race_ancestor || !race_after_component || !slash ||
        (size_t)(slash - component) != strlen("ancestor") ||
        strncmp(component, "ancestor", strlen("ancestor")) != 0) return;
    assert(rename(race_ancestor, race_saved) == 0);
    assert(symlink(race_target, race_ancestor) == 0);
    race_ancestor = NULL;
}

static void put_u64(SplArray* a, uint64_t value) {
    for (int i = 0; i < 8; i++) assert(rt_array_push(a, (int64_t)((value >> (8 * i)) & 255)));
}
static void put_bytes(SplArray* a, const uint8_t* bytes, size_t n) {
    for (size_t i = 0; i < n; i++) assert(rt_array_push(a, bytes[i]));
}
static void put_text(SplArray* a, const char* text) {
    size_t n = strlen(text); put_u64(a, n); put_bytes(a, (const uint8_t*)text, n);
}
static SplArray* request_bytes(const char* cwd, int64_t pin, const uint8_t digest[32]) {
    SplArray* a = rt_array_new(1024);
    const uint8_t magic[8] = {'P','O','V','4','R','E','Q',0}; put_bytes(a, magic, 8);
    put_u64(a, 1); put_u64(a, 1); put_u64(a, 1000000000); put_u64(a, 100000000);
    put_u64(a, 500000000); put_u64(a, 1024); put_u64(a, 1024); put_u64(a, 0);
    put_u64(a, 1); put_u64(a, 1); put_u64(a, 1000000); put_u64(a, 77);
    put_bytes(a, executable_digest, 32); put_text(a, cwd); put_text(a, cwd);
    put_u64(a, (uint64_t)pin); put_bytes(a, digest, 32);
    put_u64(a, 1); put_text(a, "pov4-darwin-selfcheck");
    put_u64(a, 1); put_text(a, "POV4_TEST"); put_text(a, "exact");
    return a;
}
static SplArray* tuple_item(SplArray* tuple, int index) {
    return (SplArray*)(uintptr_t)rt_array_get(tuple, index);
}
static void get_digest(int64_t pin, uint8_t digest[32]) {
    SplArray* a = rt_process_observation_v4_cwd_digest_value(pin);
    assert(rt_array_len(a) == 32);
    assert(rt_array_bytes_copy_checked((int64_t)(uintptr_t)a, digest, 32) == 32);
    rt_array_free(a);
}
static void assert_digest_matches_inode(const char* path, const uint8_t digest[32]) {
    struct stat info; assert(stat(path, &info) == 0);
    uint8_t identity[32] = {'P','O','V','4','C','W','D',0}, expected[32];
    pov4_store_u64_le(identity + 8, (uint64_t)info.st_dev);
    pov4_store_u64_le(identity + 16, (uint64_t)info.st_ino);
    pov4_store_u64_le(identity + 24, (uint64_t)info.st_mode);
    owned_sha256(identity, sizeof(identity), expected);
    assert(memcmp(expected, digest, sizeof(expected)) == 0);
}
static int open_fd_count(void) {
    int count = 0;
    for (int fd = 0; fd < 4096; fd++) if (fcntl(fd, F_GETFD) >= 0) count++;
    return count;
}
static void must_reject_path(const char* bytes, size_t len) {
    assert(rt_process_observation_v4_pin_cwd_value(bytes, len) == 0);
}
static void assert_words_exact(SplArray* words, const int64_t* expected, int64_t count) {
    assert(rt_array_len(words) == count);
    for (int64_t i = 0; i < count; i++) {
        if (rt_array_get(words, i) != expected[i])
            fprintf(stderr, "word %lld: got %lld expected %lld\n", (long long)i,
                    (long long)rt_array_get(words, i), (long long)expected[i]);
        assert(rt_array_get(words, i) == expected[i]);
    }
}
/* A rejection owns no child: status REJECTED, zero ticket and pid, and a
 * positive errno (exactly `error` when non-zero). */
static void assert_v4_rejected(SplArray* result, int error) {
    assert(rt_array_len(result) == 4);
    SplArray* words = tuple_item(result, 3);
    assert(rt_array_len(words) == 64);
    assert(rt_array_get(words, POV4_STATUS) == POV4_STATUS_REJECTED);
    assert(rt_array_get(words, POV4_TICKET_HIGH) == 0 && rt_array_get(words, POV4_TICKET_LOW) == 0);
    assert(rt_array_get(words, POV4_PID) == 0);
    assert(rt_array_get(words, POV4_ERRNO) > 0);
    if (error) assert(rt_array_get(words, POV4_ERRNO) == error);
}
static void check_unavailable_process_apis(SplArray* request) {
    const int64_t caps_expected[] = {RT_OWNED_PROCESS_OBSERVATION_ADAPTER_VERSION, 0, 0};
    assert_words_exact(rt_process_owned_v3_capabilities_value(), caps_expected, 3);

    const int64_t v3_start_expected[] = {0, RT_OWNED_PROCESS_OPAQUE_V3_VERSION, 0, ENOTSUP};
    assert_words_exact(rt_process_owned_v3_start_value("x", 1, NULL, NULL, 1, 1, 1),
                       v3_start_expected, 4);
    assert_words_exact(rt_process_owned_v3_start_pinned_value(1, NULL, NULL, 1, 1, 1),
                       v3_start_expected, 4);
    SplArray* v3_poll = rt_process_owned_v3_poll_value(1, 0, 1, 1);
    assert(rt_array_len(v3_poll) == 3);
    assert(rt_array_len(tuple_item(v3_poll, 0)) == 0);
    assert(rt_array_len(tuple_item(v3_poll, 1)) == 0);
    int64_t v3_poll_expected[17] = {RT_OWNED_PROCESS_OPAQUE_V3_VERSION};
    v3_poll_expected[16] = ENOTSUP;
    assert_words_exact(tuple_item(v3_poll, 2), v3_poll_expected, 17);
    int64_t v3_input_expected[39] = {RT_OWNED_PROCESS_OPAQUE_V3_VERSION};
    v3_input_expected[6] = ENOTSUP;
    assert_words_exact(rt_process_owned_v3_input_value(1), v3_input_expected, 39);
    const int64_t v3_cancel_expected[] = {RT_OWNED_PROCESS_OPAQUE_V3_VERSION, 0, 0, ENOTSUP};
    assert_words_exact(rt_process_owned_v3_cancel_value(1), v3_cancel_expected, 4);
    int64_t v3_result_expected[15] = {RT_OWNED_PROCESS_OPAQUE_V3_VERSION};
    v3_result_expected[14] = ENOTSUP;
    assert_words_exact(rt_process_owned_v3_result_value(1), v3_result_expected, 15);
    assert_words_exact(rt_process_owned_v3_collect_value(1), v3_result_expected, 15);
    assert(rt_process_owned_v3_release_value(1) == 0);
    const int64_t capture_limits_expected[] = {
        RT_OWNED_PROCESS_OBSERVATION_ADAPTER_VERSION, 0, ENOTSUP,
    };
    assert_words_exact(rt_process_owned_v3_set_capture_limits_value(1, 1, 1),
                       capture_limits_expected, 3);

    /* Darwin V4 is available with its own, weaker capability mask: no sealed
     * executable, no ptrace exec proof, no memory cap. */
    const int64_t v4_caps_expected[] = {4, 8, 1, POV4_DARWIN_CAPABILITIES,
        POV4_SLOTS, RT_OWNED_ABI_MAX_OUTPUT_BYTES, POV4_MAX_WAIT_NS, 0};
    assert_words_exact(rt_process_observation_v4_capabilities_value(), v4_caps_expected, 8);
    assert((POV4_DARWIN_CAPABILITIES & (POV4_CAP_PINNED_EXEC | POV4_CAP_PTRACE_EXEC |
                                        POV4_CAP_RLIMIT_AS)) == 0);
    /* The unpinned start family stays refused; mismatched pins and unknown
     * tickets are rejected before any executable is acquired. */
    assert_v4_rejected(rt_process_observation_v4_start_value(request), ENOTSUP);
    assert_v4_rejected(rt_process_observation_v4_start_pinned_value(77, 1, request), ESTALE);
    assert_v4_rejected(rt_process_observation_v4_start_pinned_value(77, 1, NULL), 0);
    SplArray* ticket = rt_array_new(0), *receipt = rt_array_new(0), *digest = rt_array_new(0);
    assert_v4_rejected(rt_process_observation_v4_poll_value(ticket, 0), 0);
    assert_v4_rejected(rt_process_observation_v4_cancel_value(ticket, 0), 0);
    assert_v4_rejected(rt_process_observation_v4_collect_value(ticket, 0), 0);
    assert_v4_rejected(rt_process_observation_v4_ack_collect_value(ticket, digest), 0);
    /* Inspection V1 (atomic stdin) stays outside the Darwin scope. */
    assert_v4_rejected(rt_process_inspection_v1_start_pinned_value(
        77, 1, request, receipt, digest), ENOTSUP);
    SplArray* input_receipt = rt_process_inspection_v1_input_receipt_value(ticket);
    assert(rt_array_len(input_receipt) == 75 && rt_array_get(input_receipt, 0) == 1 &&
           rt_array_get(input_receipt, 10) == ENOTSUP);
    assert(executable_acquisitions == 0);
}
static void check_direct_unsupported_receipts(void) {
    const char* argv[] = {"selfcheck", NULL};
    const uint8_t input[] = {1, 2, 3};
    RtOwnedProcessTokenV2 token = {UINT64_MAX, UINT64_MAX};
    RtOwnedProcessStartReceiptV2 start;
    memset(&start, 0xa5, sizeof(start));
    assert(!rt_process_owned_start_v2("x", argv, 1, 1, 64, &token, &start));
    assert(token.high == 0 && token.low == 0);
    assert(start.version == RT_OWNED_PROCESS_ASYNC_VERSION && start.accepted == 0 &&
           start.runtime_error == ENOTSUP);

    token.high = token.low = UINT64_MAX;
    assert(!rt_process_owned_start_v3("x", argv, input, sizeof(input), 1, 1, 64,
                                     &token, &start));
    assert(token.high == 0 && token.low == 0);
    assert(start.version == RT_OWNED_PROCESS_INPUT_VERSION && start.accepted == 0 &&
           start.runtime_error == ENOTSUP);
    token.high = token.low = UINT64_MAX;
    assert(!rt_process_owned_start_pinned_v3(1, argv, input, sizeof(input), 1, 1, 64,
                                            &token, &start));
    assert(token.high == 0 && token.low == 0);
    assert(start.version == RT_OWNED_PROCESS_INPUT_VERSION && start.accepted == 0 &&
           start.runtime_error == ENOTSUP);

    token.high = 11; token.low = 22;
    char out[8] = {0}, err[8] = {0};
    RtOwnedProcessPollReceiptV2 poll;
    memset(&poll, 0xa5, sizeof(poll));
    assert(!rt_process_owned_poll_v2(token, 0, out, sizeof(out), err, sizeof(err), &poll));
    assert(poll.version == RT_OWNED_PROCESS_ASYNC_VERSION && poll.live == 0 &&
           poll.terminal == 0 && poll.cancel_requested == 0 && poll.timed_out == 0 &&
           poll.term_sent == 0 && poll.kill_sent == 0 && poll.reaped == 0 &&
           poll.stdout_truncated == 0 && poll.stderr_truncated == 0 &&
           poll.stdout_bytes_seen == 0 && poll.stderr_bytes_seen == 0 &&
           poll.stdout_bytes_kept == 0 && poll.stderr_bytes_kept == 0 &&
           poll.stdout_bytes_delivered == 0 && poll.stderr_bytes_delivered == 0 &&
           poll.runtime_error == ENOTSUP);

    RtOwnedProcessCancelReceipt cancel;
    memset(&cancel, 0xa5, sizeof(cancel));
    assert(!rt_process_owned_cancel_v2(token, &cancel));
    assert(cancel.version == RT_OWNED_PROCESS_ASYNC_VERSION && cancel.slot == 0 &&
           cancel.generation == 0 && cancel.pid == 0 && cancel.start_identity == 0 &&
           cancel.accepted == 0 && cancel.term_sent == 0 && cancel.runtime_error == ENOTSUP);

    RtOwnedProcessResultV2 result;
    memset(&result, 0xa5, sizeof(result));
    assert(!rt_process_owned_result_v2(token, &result));
    assert(result.version == RT_OWNED_PROCESS_ASYNC_VERSION && result.pid == 0 &&
           result.process_group_id == 0 && result.start_identity == 0 && result.exit_code == -1 &&
           result.timed_out == 0 && result.cancel_requested == 0 && result.term_sent == 0 &&
           result.kill_sent == 0 && result.identity_revalidated == 0 && result.reaped == 0 &&
           result.stdout_truncated == 0 && result.stderr_truncated == 0 &&
           result.stdout_bytes_seen == 0 && result.stderr_bytes_seen == 0 &&
           result.stdout_bytes_kept == 0 && result.stderr_bytes_kept == 0 &&
           result.runtime_error == ENOTSUP);
    memset(&result, 0xa5, sizeof(result));
    assert(!rt_process_owned_collect_v2(token, &result));
    assert(result.version == RT_OWNED_PROCESS_ASYNC_VERSION && result.pid == 0 &&
           result.exit_code == -1 && result.reaped == 0 && result.runtime_error == ENOTSUP);

    RtOwnedProcessInputReceiptV3 input_receipt;
    memset(&input_receipt, 0xa5, sizeof(input_receipt));
    assert(!rt_process_owned_input_receipt_v3(token, &input_receipt));
    assert(input_receipt.version == RT_OWNED_PROCESS_INPUT_VERSION &&
           input_receipt.input_bytes_accepted == 0 && input_receipt.input_bytes_written == 0 &&
           input_receipt.stdin_closed == 0 && input_receipt.terminal == 0 &&
           input_receipt.reaped == 0 && input_receipt.runtime_error == ENOTSUP);
    for (int i = 0; i < 32; i++) assert(input_receipt.input_sha256[i] == 0);

    RtOwnedProcessReceipt sync_receipt;
    memset(&sync_receipt, 0xa5, sizeof(sync_receipt));
    assert(!rt_process_run_owned_bounded("x", argv, 1, 64, out, sizeof(out),
                                         err, sizeof(err), &sync_receipt));
    assert(sync_receipt.version == RT_OWNED_PROCESS_RECEIPT_VERSION &&
           sync_receipt.slot == 0 && sync_receipt.generation == 0 && sync_receipt.pid == 0 &&
           sync_receipt.process_group_id == 0 && sync_receipt.start_identity == 0 &&
           sync_receipt.stdout_bytes_seen == 0 && sync_receipt.stderr_bytes_seen == 0 &&
           sync_receipt.stdout_bytes_kept == 0 && sync_receipt.stderr_bytes_kept == 0 &&
           sync_receipt.exit_code == -1 && sync_receipt.timed_out == 0 &&
           sync_receipt.term_sent == 0 && sync_receipt.kill_sent == 0 &&
           sync_receipt.identity_revalidated == 0 && sync_receipt.reaped == 0 &&
           sync_receipt.stdout_truncated == 0 && sync_receipt.stderr_truncated == 0 &&
           sync_receipt.runtime_error == ENOTSUP);
    RtOwnedProcessObservationV1 observation;
    memset(&sync_receipt, 0xa5, sizeof(sync_receipt));
    memset(&observation, 0xa5, sizeof(observation));
    assert(!rt_process_run_owned_observed_bounded("x", argv, 1, 64, out, sizeof(out),
            err, sizeof(err), &sync_receipt, &observation));
    assert(sync_receipt.version == RT_OWNED_PROCESS_RECEIPT_VERSION &&
           sync_receipt.exit_code == -1 && sync_receipt.runtime_error == ENOTSUP);
    assert(observation.version == RT_OWNED_PROCESS_OBSERVATION_VERSION &&
           observation.evidence_flags == 0 && observation.user_cpu_ms == 0 &&
           observation.system_cpu_ms == 0 && observation.peak_direct_child_rss_bytes == 0 &&
           observation.peak_tree_charge_bytes == 0 && observation.io_read_bytes == 0 &&
           observation.io_write_bytes == 0 && observation.pids_peak == 0 &&
           observation.termination_signal == 0 && observation.runtime_error == ENOTSUP);
}

int main(void) {
    for (int i = 0; i < 32; i++) executable_digest[i] = (uint8_t)(i + 7);
    char temp[] = "/tmp/pov4-darwin-selfcheck-XXXXXX";
    char* root = mkdtemp(temp); assert(root);
    char canonical_root[PATH_MAX]; assert(realpath(root, canonical_root));
    char original[PATH_MAX], renamed[PATH_MAX], linkpath[PATH_MAX];
    assert(snprintf(original, sizeof(original), "%s/work", canonical_root) > 0);
    assert(snprintf(renamed, sizeof(renamed), "%s/original", canonical_root) > 0);
    assert(snprintf(linkpath, sizeof(linkpath), "%s/link", canonical_root) > 0);
    assert(mkdir(original, 0700) == 0);
    assert(symlink(original, linkpath) == 0);

    char ancestor[PATH_MAX], saved[PATH_MAX], target[PATH_MAX], nested[PATH_MAX], target_nested[PATH_MAX];
    assert(snprintf(ancestor, sizeof(ancestor), "%s/ancestor", canonical_root) > 0);
    assert(snprintf(saved, sizeof(saved), "%s/saved", canonical_root) > 0);
    assert(snprintf(target, sizeof(target), "%s/target", canonical_root) > 0);
    assert(snprintf(nested, sizeof(nested), "%s/ancestor/nested", canonical_root) > 0);
    assert(snprintf(target_nested, sizeof(target_nested), "%s/target/nested", canonical_root) > 0);
    assert(mkdir(ancestor, 0700) == 0 && mkdir(target, 0700) == 0);
    assert(mkdir(nested, 0700) == 0 && mkdir(target_nested, 0700) == 0);
    int64_t nested_pin = rt_process_observation_v4_pin_cwd_value(nested, strlen(nested));
    assert(nested_pin > 0 && rt_process_observation_v4_close_cwd_value(nested_pin));
    race_ancestor = ancestor; race_saved = saved; race_target = target;
    int64_t raced_pin = rt_process_observation_v4_pin_cwd_value(nested, strlen(nested));
    assert(raced_pin == 0); /* An ancestor symlink must never redirect the pin. */
    assert(unlink(ancestor) == 0 && rename(saved, ancestor) == 0);
    char saved_nested[PATH_MAX];
    assert(snprintf(saved_nested, sizeof(saved_nested), "%s/saved/nested", canonical_root) > 0);
    race_ancestor = ancestor; race_after_component = 1;
    raced_pin = rt_process_observation_v4_pin_cwd_value(nested, strlen(nested));
    assert(!race_ancestor && raced_pin > 0);
    uint8_t raced_digest[32]; get_digest(raced_pin, raced_digest);
    assert_digest_matches_inode(saved_nested, raced_digest);
    int raced_fd = pov4_acquire_cwd((uint64_t)raced_pin, nested, raced_digest);
    assert(raced_fd >= 0);
    struct stat held, expected;
    assert(fstat(raced_fd, &held) == 0 && stat(saved_nested, &expected) == 0);
    assert(held.st_dev == expected.st_dev && held.st_ino == expected.st_ino);
    assert(close(raced_fd) == 0 && rt_process_observation_v4_close_cwd_value(raced_pin));
    assert(unlink(ancestor) == 0 && rename(saved, ancestor) == 0);
    assert(rmdir(nested) == 0 && rmdir(ancestor) == 0);
    assert(rmdir(target_nested) == 0 && rmdir(target) == 0);

    int64_t pin = rt_process_observation_v4_pin_cwd_value(original, strlen(original));
    assert(pin > 0);
    uint8_t digest[32]; get_digest(pin, digest);
    assert_digest_matches_inode(original, digest);
    char canonical[PATH_MAX]; assert(realpath(original, canonical));
    int acquired = pov4_acquire_cwd((uint64_t)pin, canonical, digest); assert(acquired >= 0);
    assert((fcntl(acquired, F_GETFD) & FD_CLOEXEC) != 0);
    assert(close(acquired) == 0);
    /* A successful fstat leaves errno untouched. A changed directory identity
     * must report ESTALE rather than an error from the caller's earlier work. */
    assert(chmod(original, 0750) == 0);
    int stale_fd_baseline = open_fd_count();
    errno = EIO;
    assert(pov4_acquire_cwd((uint64_t)pin, canonical, digest) < 0);
    assert(errno == ESTALE);
    assert(open_fd_count() == stale_fd_baseline);
    errno = 0;
    assert(pov4_acquire_cwd((uint64_t)pin, canonical, digest) < 0);
    assert(errno == ESTALE);
    assert(chmod(original, 0700) == 0);
    acquired = pov4_acquire_cwd((uint64_t)pin, canonical, digest);
    assert(acquired >= 0 && close(acquired) == 0);
    uint8_t bad_digest[32]; memcpy(bad_digest, digest, 32); bad_digest[0] ^= 1;
    errno = EIO;
    assert(pov4_acquire_cwd((uint64_t)pin, canonical, bad_digest) < 0);
    assert(errno == ESTALE);
    errno = EIO;
    assert(pov4_acquire_cwd((uint64_t)pin, renamed, digest) < 0);
    assert(errno == ESTALE);
    errno = EIO;
    assert(pov4_acquire_cwd((uint64_t)pin + 1, canonical, digest) < 0);
    assert(errno == ESTALE);

    char cwd_before[PATH_MAX], cwd_after[PATH_MAX];
    assert(getcwd(cwd_before, sizeof(cwd_before)));
    struct stat pinned_stat; assert(stat(original, &pinned_stat) == 0);
    assert(rename(original, renamed) == 0);
    assert(mkdir(original, 0700) == 0); /* Rebind the original pathname. */
    acquired = pov4_acquire_cwd((uint64_t)pin, canonical, digest); assert(acquired >= 0);
    pid_t child = fork(); assert(child >= 0);
    if (child == 0) {
        struct stat child_stat;
        if (fchdir(acquired) != 0 || stat(".", &child_stat) != 0 ||
            child_stat.st_dev != pinned_stat.st_dev || child_stat.st_ino != pinned_stat.st_ino)
            _exit(1);
        _exit(0);
    }
    int status = 0;
    pid_t waited;
    do { waited = waitpid(child, &status, 0); } while (waited < 0 && errno == EINTR);
    assert(waited == child);
    assert(WIFEXITED(status) && WEXITSTATUS(status) == 0);
    assert(close(acquired) == 0);
    assert(getcwd(cwd_after, sizeof(cwd_after)) && strcmp(cwd_before, cwd_after) == 0);

    char embedded_nul[] = {'/', 't', 'm', 'p', 0, 'x'};
    must_reject_path(embedded_nul, sizeof(embedded_nul));
    must_reject_path(".", 1);
    must_reject_path(linkpath, strlen(linkpath));

    assert(rt_process_observation_v4_close_cwd_value(pin) == 1);
    assert(rt_process_observation_v4_close_cwd_value(pin) == 0);
    assert(pov4_acquire_cwd((uint64_t)pin, canonical, digest) < 0);
    SplArray* stale_digest = rt_process_observation_v4_cwd_digest_value(pin);
    assert(rt_array_len(stale_digest) == 0); rt_array_free(stale_digest);

    int baseline = open_fd_count();
    int64_t pins[16];
    for (int i = 0; i < 16; i++) {
        pins[i] = rt_process_observation_v4_pin_cwd_value(renamed, strlen(renamed));
        assert(pins[i] > 0);
    }
    assert(open_fd_count() == baseline + 16);
    assert(rt_process_observation_v4_pin_cwd_value(renamed, strlen(renamed)) == 0);
    for (int i = 0; i < 16; i++) assert(rt_process_observation_v4_close_cwd_value(pins[i]) == 1);
    assert(open_fd_count() == baseline);
    int64_t after_reuse = rt_process_observation_v4_pin_cwd_value(renamed, strlen(renamed));
    assert(after_reuse > 0 && rt_process_observation_v4_close_cwd_value(after_reuse) == 1);

    SplArray* request = request_bytes(canonical, pin, digest);
    check_unavailable_process_apis(request);
    check_direct_unsupported_receipts();

    assert(unlink(linkpath) == 0); assert(rmdir(original) == 0); assert(rmdir(renamed) == 0);
    assert(rmdir(canonical_root) == 0);
    puts("runtime_process_observation_v4_darwin_selfcheck: PASS");
    return 0;
}
#endif
