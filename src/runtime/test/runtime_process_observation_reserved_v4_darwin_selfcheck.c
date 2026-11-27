/* E3 focused new controls only. NOT_RUN until the coordinator admits a slot.
 * cc -std=c11 -O0 -Wall -Wextra -Werror -pthread \
 *   src/runtime/test/runtime_process_observation_reserved_v4_darwin_selfcheck.c \
 *   src/runtime/runtime_process_tree.c -o /tmp/pov4-reserved-e3
 * Run under an external 30-second process-tree watchdog.
 * Reuses the existing private executable-snapshot fixture, NOT its old matrix.
 * C schema corruption is not execution of the Simple decoder.
 * Descriptor/slot checks do not constitute whole-heap leak qualification.
 * Snapshot pin stubs are explicit; actual spawn/observe/retire provider is real.
 */
#define main pov4_existing_fixture_main
#include "runtime_process_observation_v4_darwin_live_selfcheck.c"
#undef main

#if !defined(__APPLE__)
int main(void) { puts("reserved V4 native controls: UNSUPPORTED on this harness host"); return 77; }
#else
typedef struct StartAttempt {
    int64_t token, cwd, result;
    SplArray* request;
} StartAttempt;
static void* concurrent_start(void* arg) {
    StartAttempt* attempt = arg;
    attempt->result = rt_process_observation_v4_reserved_start_pinned_value(
        attempt->token, TEST_PIN, attempt->cwd, attempt->request);
    return NULL;
}

static SplArray* reserved_until_frozen(int64_t token) {
    for (int turn = 0; turn < 300; ++turn) {
        SplArray* observation = rt_process_observation_v4_reserved_observe_value(
            token, 10000000, 1);
        if (!observation) continue; /* Injected EAGAIN retains exact authority. */
        int64_t kind = word(observation, POV4_PACKET_KIND);
        if (kind == POV4_KIND_FROZEN || kind == POV4_KIND_CLEANUP_FROZEN) return observation;
        pov4_tuple4_free(observation);
    }
    assert(!"bounded retirement did not freeze"); return NULL;
}

static void check_reserved_child(const char* cwd, int64_t pin, const uint8_t digest[32]) {
    int64_t token = rt_process_observation_v4_reserve_value(); assert(token > 0);
    assert(rt_process_observation_v4_reserved_state_value(token) == 1);
    SplArray* request = request_bytes(cwd, pin, digest, "--wait-child", POV4_DESCENDANT_PROCESS_GROUP);
    int before = acquisitions;
    StartAttempt a = {token, pin, 0, request}, b = {token, pin, 0, request};
    pov4_reservation_test_drop_start = 1;
    pthread_t first, second;
    assert(pthread_create(&first, NULL, concurrent_start, &a) == 0);
    assert(pthread_create(&second, NULL, concurrent_start, &b) == 0);
    assert(pthread_join(first, NULL) == 0 && pthread_join(second, NULL) == 0);
    assert((a.result == 1 && b.result < 0) || (b.result == 1 && a.result < 0));
    assert(acquisitions == before + 1);
    assert(pov4_reservation_test_drop_start == 0); /* Actual initial publication was lost. */
    assert(rt_process_observation_v4_reserved_state_value(token) == 4);
    assert(rt_process_observation_v4_reserved_confirm_release_value(token) == -EBUSY);
    SplArray* running = rt_process_observation_v4_reserved_observe_value(token, 0, 0);
    assert(running && word(running, POV4_VERSION) == POV4_VERSION_VALUE);
    assert(word(running, POV4_STATUS) == POV4_STATUS_RUNNING);
    assert(word(running, POV4_STDOUT_PAYLOAD_LENGTH) == rt_array_len(tuple_item(running, 0)));
    assert(word(running, POV4_STDERR_PAYLOAD_LENGTH) == rt_array_len(tuple_item(running, 1)));
    pov4_tuple4_free(running);
    /* The actual child exists before deliberate receipt schema corruption. */
    pov4_reservation_test_corrupt_observe = 1;
    SplArray* corrupt = rt_process_observation_v4_reserved_observe_value(token, 0, 0);
    assert(corrupt && word(corrupt, POV4_VERSION) == -1);
    pid_t child = (pid_t)word(corrupt, POV4_PID); assert(child > 0);
    assert(rt_process_observation_v4_reserved_matches_value(token,
        word(corrupt, POV4_REQUEST_ID_HIGH), word(corrupt, POV4_REQUEST_ID_LOW),
        word(corrupt, POV4_TICKET_HIGH), word(corrupt, POV4_TICKET_LOW)) == 1);
    assert(rt_process_observation_v4_reserved_matches_value(token,
        -1, word(corrupt, POV4_REQUEST_ID_LOW),
        word(corrupt, POV4_TICKET_HIGH), word(corrupt, POV4_TICKET_LOW)) == 0);
    assert(rt_process_observation_v4_reserved_matches_value(token,
        word(corrupt, POV4_REQUEST_ID_HIGH), word(corrupt, POV4_REQUEST_ID_LOW),
        -1, word(corrupt, POV4_TICKET_LOW)) == 0);
    SplArray* legacy_ticket = ticket_from(corrupt);
    SplArray* refused = rt_process_observation_v4_collect_value(legacy_ticket, 0);
    assert(word(refused, POV4_STATUS) == POV4_STATUS_REJECTED);
    pov4_tuple4_free(refused);
    pov4_tuple4_free(corrupt);
    /* A changed replay must not launch again or replace the bound request. */
    SplArray* changed = request_bytes(cwd, pin, digest, "--child", POV4_DESCENDANT_LEADER);
    assert(rt_process_observation_v4_reserved_start_pinned_value(token, TEST_PIN, pin, changed) == -EALREADY);
    rt_array_free(changed);
    assert(acquisitions == before + 1);
    pov4_reservation_test_retry_collect = 1;
    SplArray* frozen = reserved_until_frozen(token);
    assert(pov4_reservation_test_retry_collect == 0);
    assert(word(frozen, POV4_LEADER_REAPED) == 1 && word(frozen, POV4_TREE_EMPTY) == 1);
    assert(pid_gone(child));
    SplArray* frozen_digest = tuple_item(frozen, 2);
    SplArray* wrong_digest = rt_array_new(32);
    for (int i = 0; i < 32; ++i)
        assert(rt_array_push(wrong_digest, rt_array_get(frozen_digest, i) ^ 1));
    assert(rt_process_observation_v4_reserved_ack_value(token, wrong_digest) == NULL);
    assert(rt_process_observation_v4_reserved_state_value(token) == 4);
    rt_array_free(wrong_digest);
    pov4_reservation_test_corrupt_ack = 1;
    SplArray* ack = rt_process_observation_v4_reserved_ack_value(token, frozen_digest);
    assert(ack && word(ack, POV4_VERSION) == -1);
    pov4_tuple4_free(ack);
    assert(rt_process_observation_v4_reserved_state_value(token) == 5);
    ack = rt_process_observation_v4_reserved_ack_value(token, frozen_digest);
    assert(ack && word(ack, POV4_VERSION) == POV4_VERSION_VALUE);
    assert(word(ack, POV4_PACKET_KIND) == POV4_KIND_ACK);
    SplArray* repeated = rt_process_observation_v4_reserved_ack_value(token, frozen_digest);
    for (int i = 0; i < POV4_WORDS; ++i) assert(word(ack, i) == word(repeated, i));
    pov4_tuple4_free(ack); pov4_tuple4_free(repeated);
    assert(rt_process_observation_v4_reserved_confirm_release_value(token) == 1);
    int64_t replacement = rt_process_observation_v4_reserve_value();
    assert(replacement > token);
    assert(rt_process_observation_v4_reserved_confirm_release_value(token) == -ESTALE);
    assert(rt_process_observation_v4_reserved_state_value(replacement) == 1);
    assert(rt_process_observation_v4_reserved_confirm_release_value(replacement) == 1);
    pov4_tuple4_free(frozen); rt_array_free(legacy_ticket); rt_array_free(request);
}

int main(int argc, char** argv) {
    if (argc > 1) return pov4_existing_fixture_main(argc, argv);
    char self[PATH_MAX]; uint32_t length = sizeof(self);
    assert(_NSGetExecutablePath(self, &length) == 0); make_snapshot(self);
    char cwd[PATH_MAX]; assert(realpath(".", cwd));
    int64_t pin = rt_process_observation_v4_pin_cwd_value(cwd, strlen(cwd)); assert(pin > 0);
    SplArray* digest_value = rt_process_observation_v4_cwd_digest_value(pin);
    uint8_t digest[32];
    assert(rt_array_bytes_copy_checked((int64_t)(uintptr_t)digest_value, digest, 32) == 32);
    int baseline = open_fd_count();
    int64_t reservations[POV4_SLOTS];
    for (int i = 0; i < POV4_SLOTS; ++i) { reservations[i] = rt_process_observation_v4_reserve_value(); assert(reservations[i] > 0); }
    assert(rt_process_observation_v4_reserve_value() == -EAGAIN);
    for (int i = 0; i < POV4_SLOTS; ++i) assert(rt_process_observation_v4_reserved_confirm_release_value(reservations[i]) == 1);
    int64_t rejected = rt_process_observation_v4_reserve_value();
    assert(rt_process_observation_v4_reserved_start_pinned_value(rejected, -1, pin, NULL) == 0);
    assert(rt_process_observation_v4_reserved_state_value(rejected) == 3);
    assert(rt_process_observation_v4_reserved_confirm_release_value(rejected) == 1);
    check_reserved_child(cwd, pin, digest);
    assert(open_fd_count() == baseline);
    for (int i = 0; i < POV4_SLOTS; ++i) assert(!pov4_reservations[i].token && !pov4_slots[i].active);
    assert(rt_process_observation_v4_close_cwd_value(pin) == 1);
    rt_array_free(digest_value);
    assert(close(snapshot_fd) == 0 && unlink(snapshot_path) == 0 && rmdir(snapshot_dir) == 0);
    puts("reserved V4 native controls: PASS"); return 0;
}
#endif
