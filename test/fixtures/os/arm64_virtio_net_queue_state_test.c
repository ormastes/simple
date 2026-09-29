#include <assert.h>
#include <stdint.h>

#define ARM64_NET_QUEUE_SIZE 8U

struct arm64_virtq_used_elem {
    uint32_t id;
    uint32_t len;
};

struct arm64_net_used {
    uint16_t flags;
    uint16_t idx;
    struct arm64_virtq_used_elem ring[ARM64_NET_QUEUE_SIZE];
};

struct arm64_net_avail {
    uint16_t flags;
    uint16_t idx;
    uint16_t ring[ARM64_NET_QUEUE_SIZE];
};

#include "../../../examples/09_embedded/simple_os/arch/arm64/boot/arm64_virtio_net_queue_state.h"

int main(void)
{
    struct arm64_net_used used = {0};
    uint8_t posted[ARM64_NET_QUEUE_SIZE] = {0};
    uint16_t last_used = 0U;
    uint64_t completions = 0U;

    /* Descriptor identity and producer ring position intentionally diverge. */
    posted[5] = 1U;
    struct arm64_net_avail avail = {0};
    avail.idx = 9U;
    arm64_net_tx_publish(&avail, 5U);
    assert(avail.ring[1] == 5U);
    assert(avail.ring[5] == 0U);
    avail.idx = UINT16_MAX;
    arm64_net_tx_publish(&avail, 6U);
    assert(avail.ring[7] == 6U);
    assert(avail.idx == 0U);

    /* A delayed completion is drained before allocation, making it reusable. */
    used.ring[0].id = 5U;
    used.idx = 1U;
    assert(arm64_net_tx_find_free(posted) == 0U);
    for (uint16_t i = 0; i < ARM64_NET_QUEUE_SIZE; ++i) posted[i] = 1U;
    assert(arm64_net_tx_find_free(posted) == ARM64_NET_QUEUE_SIZE);
    assert(arm64_net_tx_reap_used(&used, &last_used, posted,
                                  &completions, ARM64_NET_QUEUE_SIZE) == 0);
    assert(posted[5] == 0U);
    assert(arm64_net_tx_find_free(posted) == 5U);
    assert(completions == 1U);

    /* A full batch crossing u16 rollover drains once and reports its waiter. */
    struct arm64_net_used batch = {0};
    uint8_t batch_posted[ARM64_NET_QUEUE_SIZE] = {0};
    uint16_t batch_last = (uint16_t)(UINT16_MAX - 3U);
    uint64_t batch_completions = 0U;
    for (uint16_t i = 0; i < ARM64_NET_QUEUE_SIZE; ++i) {
        uint16_t ring_slot =
            (uint16_t)((uint16_t)(batch_last + i) % ARM64_NET_QUEUE_SIZE);
        batch.ring[ring_slot].id = i;
        batch_posted[i] = 1U;
    }
    batch.idx = (uint16_t)(batch_last + ARM64_NET_QUEUE_SIZE);
    assert(arm64_net_tx_reap_used(&batch, &batch_last, batch_posted,
                                  &batch_completions, 7U) == 1);
    assert(batch_completions == ARM64_NET_QUEUE_SIZE);
    assert(batch_last == 4U);
    for (uint16_t i = 0; i < ARM64_NET_QUEUE_SIZE; ++i)
        assert(batch_posted[i] == 0U);

    /* Corruption wins even when an awaited completion preceded a duplicate. */
    struct arm64_net_used duplicate = {0};
    uint8_t duplicate_posted[ARM64_NET_QUEUE_SIZE] = {0};
    uint16_t duplicate_last = 0U;
    uint64_t duplicate_completions = 0U;
    duplicate_posted[3] = 1U;
    duplicate.ring[0].id = 3U;
    duplicate.ring[1].id = 3U;
    duplicate.idx = 2U;
    assert(arm64_net_tx_reap_used(&duplicate, &duplicate_last,
                                  duplicate_posted, &duplicate_completions,
                                  3U) == -1);
    assert(duplicate_posted[3] == 0U);
    assert(duplicate_completions == 1U);
    assert(duplicate_last == 2U);

    struct arm64_net_used corrupt = {0};
    uint8_t corrupt_posted[ARM64_NET_QUEUE_SIZE] = {0};
    uint16_t corrupt_last = 0U;
    uint64_t corrupt_completions = 0U;
    corrupt.ring[0].id = ARM64_NET_QUEUE_SIZE;
    corrupt.idx = 1U;
    assert(arm64_net_tx_reap_used(&corrupt, &corrupt_last, corrupt_posted,
                                  &corrupt_completions, 0U) == -1);
    assert(corrupt_last == 1U);
    assert(corrupt_completions == 0U);

    uint16_t overrun_last = corrupt_last;
    corrupt.idx = (uint16_t)(overrun_last + ARM64_NET_QUEUE_SIZE + 1U);
    assert(arm64_net_tx_reap_used(&corrupt, &overrun_last, corrupt_posted,
                                  &corrupt_completions, 0U) == -1);
    assert(overrun_last == corrupt_last);
    assert(corrupt_completions == 0U);
    return 0;
}
