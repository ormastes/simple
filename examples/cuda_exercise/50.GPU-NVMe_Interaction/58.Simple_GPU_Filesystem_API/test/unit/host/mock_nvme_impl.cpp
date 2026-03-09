/**
 * @file mock_nvme_impl.cpp
 * @brief Mock NVMe implementation (overrides weak symbols)
 */

#include "mock_nvme_device.h"

// Override weak symbols from nvme_fs_io_stubs.cpp
namespace nvme_fs {

void read_blocks(void* dev, std::uint64_t lba, std::uint64_t count, void* buffer) {
    auto* mock = reinterpret_cast<MockNvmeDevice*>(dev);
    mock->read_blocks(lba, count, buffer);
}

void write_blocks(void* dev, std::uint64_t lba, std::uint64_t count, const void* buffer) {
    auto* mock = reinterpret_cast<MockNvmeDevice*>(dev);
    mock->write_blocks(lba, count, buffer);
}

} // namespace nvme_fs
