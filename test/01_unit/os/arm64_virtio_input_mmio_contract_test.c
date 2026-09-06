#include <assert.h>
#include <stdint.h>

#include "../../../examples/09_embedded/simple_os/arch/arm64/boot/virtio_input_mmio_contract.h"

int main(void)
{
    assert(arm64_virtio_status_add(1U, 2U) == 3U);
    assert(arm64_virtio_status_add(3U, 8U) == 11U);
    assert(arm64_virtio_status_fail(11U, 128U) == 139U);
    assert(arm64_virtio_status_add(67U, 8U) == 75U);
    assert(arm64_virtio_status_fail(75U, 128U) == 203U);
    assert(!arm64_virtio_status_rejected(11U, 128U, 64U));
    assert(arm64_virtio_status_rejected(139U, 128U, 64U));
    assert(arm64_virtio_status_rejected(75U, 128U, 64U));
    assert(arm64_virtio_event_length_valid(8U, 8U));
    assert(!arm64_virtio_event_length_valid(9U, 8U));
    assert(arm64_virtio_queue_shape_valid(
        32U, 64U,
        0x40001000ULL, 512U,
        0x40001200ULL, 68U,
        0x40001248ULL, 260U,
        0x40002000ULL, 256U,
        0x40000000ULL, 0x58000000ULL));
    assert(!arm64_virtio_queue_shape_valid(
        32U, 16U,
        0x40001000ULL, 512U,
        0x40001200ULL, 68U,
        0x40001248ULL, 260U,
        0x40002000ULL, 256U,
        0x40000000ULL, 0x58000000ULL));
    assert(!arm64_virtio_queue_shape_valid(
        32U, 64U,
        0x40001008ULL, 512U,
        0x40001200ULL, 68U,
        0x40001248ULL, 260U,
        0x40002000ULL, 256U,
        0x40000000ULL, 0x58000000ULL));
    return 0;
}
