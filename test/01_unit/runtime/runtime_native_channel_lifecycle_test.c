#include <assert.h>
#include <pthread.h>
#include <sched.h>
#include <stdint.h>
#include <stdio.h>

int64_t rt_channel_new(void);
int64_t rt_channel_send(int64_t id, int64_t value);
int64_t rt_channel_send_i64(int64_t id, int64_t value);
int64_t rt_channel_recv_i64(int64_t id);
int64_t rt_channel_try_recv_i64(int64_t id);
void rt_channel_close(int64_t id);
void rt_channel_free(int64_t id);
int64_t rt_channel_is_closed(int64_t id);
int64_t rt_channel_test_active_ops(int64_t id);

typedef struct {
    int64_t handle;
    int accepted;
} SendRace;

typedef struct {
    int64_t handle;
    int64_t received;
} ReceiveRace;

static void* race_sender(void* opaque) {
    SendRace* race = (SendRace*)opaque;
    for (int i = 1; i <= 100000; ++i) {
        if (!rt_channel_send_i64(race->handle, i)) break;
        race->accepted++;
    }
    return NULL;
}

static void* blocked_receiver(void* opaque) {
    ReceiveRace* race = (ReceiveRace*)opaque;
    race->received = rt_channel_recv_i64(race->handle);
    return NULL;
}

static void* channel_freer(void* opaque) {
    rt_channel_free(*(int64_t*)opaque);
    return NULL;
}

static void test_reclaim_and_no_aba(void) {
    int64_t stale = rt_channel_new();
    assert(stale >= 64);
    rt_channel_close(stale);
    rt_channel_free(stale);
    for (int i = 0; i < 256; ++i) {
        int64_t current = rt_channel_new();
        assert(current >= 64);
        assert(current != stale);
        assert(rt_channel_send_i64(stale, 77) == 0);
        assert(rt_channel_try_recv_i64(stale) == 0);
        assert(rt_channel_is_closed(stale) == 1);
        assert(rt_channel_send_i64(current, i + 1) == 1);
        assert(rt_channel_recv_i64(current) == i + 1);
        rt_channel_close(current);
        rt_channel_free(current);
    }
}

static void test_close_drains_then_rejects(void) {
    int64_t channel = rt_channel_new();
    assert(rt_channel_send_i64(channel, 11) == 1);
    assert(rt_channel_send_i64(channel, 22) == 1);
    rt_channel_close(channel);
    assert(rt_channel_send_i64(channel, 33) == 0);
    assert(rt_channel_recv_i64(channel) == 11);
    assert(rt_channel_recv_i64(channel) == 22);
    assert(rt_channel_recv_i64(channel) == 0);
    rt_channel_free(channel);
}

static void test_scalar_contract_empty_full_and_invalid_admission(void) {
    int64_t channel = rt_channel_new();
    assert(rt_channel_try_recv_i64(channel) == 0);
    assert(rt_channel_send(channel, 1) == 0); /* pointer-like invalid Any word */
    assert(rt_channel_send_i64(channel, INT64_MAX) == 0); /* outside tagged i61 */
    for (int i = 1; i <= 1024; ++i)
        assert(rt_channel_send_i64(channel, i) == 1);
    assert(rt_channel_send_i64(channel, 1025) == 0);
    for (int i = 1; i <= 1024; ++i)
        assert(rt_channel_recv_i64(channel) == i);
    rt_channel_close(channel);
    rt_channel_free(channel);
}

static void test_concurrent_send_close_free(void) {
    SendRace race = {.handle = rt_channel_new(), .accepted = 0};
    pthread_t sender;
    assert(pthread_create(&sender, NULL, race_sender, &race) == 0);
    rt_channel_close(race.handle);
    rt_channel_free(race.handle);
    assert(pthread_join(sender, NULL) == 0);
    assert(rt_channel_send_i64(race.handle, 1) == 0);
    assert(rt_channel_is_closed(race.handle) == 1);
}

static void test_blocked_receiver_cannot_consume_replacement(void) {
    ReceiveRace race = {.handle = rt_channel_new(), .received = -1};
    pthread_t receiver;
    assert(pthread_create(&receiver, NULL, blocked_receiver, &race) == 0);
    while (rt_channel_test_active_ops(race.handle) != 1) sched_yield();

    pthread_t freer;
    assert(pthread_create(&freer, NULL, channel_freer, &race.handle) == 0);
    assert(pthread_join(freer, NULL) == 0);
    int64_t replacement = rt_channel_new();
    assert(replacement != race.handle);
    assert(rt_channel_send_i64(replacement, 99) == 1);
    assert(pthread_join(receiver, NULL) == 0);
    assert(race.received == 0);
    assert(rt_channel_recv_i64(replacement) == 99);
    rt_channel_close(replacement);
    rt_channel_free(replacement);
}

int main(void) {
    test_reclaim_and_no_aba();
    test_close_drains_then_rejects();
    test_scalar_contract_empty_full_and_invalid_admission();
    test_concurrent_send_close_free();
    test_blocked_receiver_cannot_consume_replacement();
    puts("runtime-native-channel-lifecycle: PASS");
    return 0;
}
