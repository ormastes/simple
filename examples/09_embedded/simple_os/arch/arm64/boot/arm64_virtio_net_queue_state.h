#ifndef SIMPLEOS_ARM64_VIRTIO_NET_QUEUE_STATE_H
#define SIMPLEOS_ARM64_VIRTIO_NET_QUEUE_STATE_H

/* Included after the transport's queue types.  Keeping these operations here
 * lets the host regression execute the exact ownership logic used in-guest. */
static uint16_t arm64_net_tx_find_free(const uint8_t *posted)
{
    for (uint16_t i = 0; i < ARM64_NET_QUEUE_SIZE; ++i) {
        if (!posted[i]) return i;
    }
    return ARM64_NET_QUEUE_SIZE;
}

static void arm64_net_tx_publish(struct arm64_net_avail *avail,
                                 uint16_t descriptor_id)
{
    uint16_t avail_slot = (uint16_t)(avail->idx % ARM64_NET_QUEUE_SIZE);
    avail->ring[avail_slot] = descriptor_id;
    avail->idx++;
}

/* Drain the device-owned used ring into driver-owned descriptor state.
 * Returns -1 for a corrupt/duplicate completion, otherwise one when the
 * awaited descriptor completed and zero when only older completions drained.
 */
static int arm64_net_tx_reap_used(const struct arm64_net_used *used,
                                  uint16_t *last_used,
                                  uint8_t *posted,
                                  uint64_t *completion_count,
                                  uint16_t awaited_id)
{
    uint16_t pending = (uint16_t)(used->idx - *last_used);
    int awaited_completed = 0;
    if (pending > ARM64_NET_QUEUE_SIZE) return -1;
    while (pending-- != 0U) {
        uint16_t used_slot = (uint16_t)(*last_used % ARM64_NET_QUEUE_SIZE);
        struct arm64_virtq_used_elem elem = used->ring[used_slot];
        (*last_used)++;
        if (elem.id >= ARM64_NET_QUEUE_SIZE || !posted[elem.id]) return -1;
        posted[elem.id] = 0U;
        (*completion_count)++;
        if (elem.id == awaited_id) awaited_completed = 1;
    }
    return awaited_completed;
}

#endif
