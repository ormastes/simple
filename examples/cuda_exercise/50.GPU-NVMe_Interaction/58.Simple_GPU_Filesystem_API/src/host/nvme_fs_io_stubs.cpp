/**
 * @file nvme_fs_io_stubs.cpp
 * @brief Default NVMe block I/O implementations (overridable in tests)
 *
 * These weak symbols can be overridden by mock implementations in tests,
 * but by default they perform real NVMe I/O via Module 53 host APIs.
 */

#include <cstdint>
#include <cstddef>
#include <stdexcept>
#include "mapper/mapper_host.h"
#include "io/host_io_host_mem.h"

namespace nvme_fs {

__attribute__((weak))
void read_blocks(void* nvme_device, std::uint64_t lba, std::uint64_t count, void* buffer) {
    if (!nvme_device || !buffer) {
        throw std::invalid_argument("Invalid device or buffer pointer");
    }

    auto* dev = static_cast<NvmeDevice*>(nvme_device);
    const std::uint32_t lba_size = nvme_get_lba_size(dev);
    const std::uint64_t num_lbas = nvme_get_num_lbas(dev);

    if (lba + count > num_lbas) {
        throw std::out_of_range("Read request exceeds device capacity");
    }

    const std::size_t bytes_to_read = count * lba_size;
    const int rc = host_io_read(dev, lba, buffer, bytes_to_read);
    if (rc != 0) {
        throw std::runtime_error("NVMe read operation failed");
    }
}

__attribute__((weak))
void write_blocks(void* nvme_device, std::uint64_t lba, std::uint64_t count, const void* buffer) {
    if (!nvme_device || !buffer) {
        throw std::invalid_argument("Invalid device or buffer pointer");
    }

    auto* dev = static_cast<NvmeDevice*>(nvme_device);
    const std::uint32_t lba_size = nvme_get_lba_size(dev);
    const std::uint64_t num_lbas = nvme_get_num_lbas(dev);

    if (lba + count > num_lbas) {
        throw std::out_of_range("Write request exceeds device capacity");
    }

    const std::size_t bytes_to_write = count * lba_size;
    const int rc = host_io_write(dev, lba, buffer, bytes_to_write);
    if (rc != 0) {
        throw std::runtime_error("NVMe write operation failed");
    }
}

} // namespace nvme_fs
