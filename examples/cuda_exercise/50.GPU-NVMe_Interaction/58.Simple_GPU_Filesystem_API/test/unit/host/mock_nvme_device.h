/**
 * @file mock_nvme_device.h
 * @brief Mock NVMe device for testing
 */

#pragma once

#include "mapper/mapper_host.h"
#include <vector>
#include <cstring>
#include <stdexcept>

// Mock NVMe device for testing
class MockNvmeDevice {
public:
    static constexpr std::size_t TOTAL_BLOCKS = 10000;
    static constexpr std::size_t BLOCK_SIZE = 512;

    std::vector<std::uint8_t> storage;

    MockNvmeDevice() : storage(TOTAL_BLOCKS * BLOCK_SIZE, 0) {}

    void read_blocks(std::uint64_t lba, std::uint64_t count, void* buffer) {
        std::size_t offset = lba * BLOCK_SIZE;
        std::size_t size = count * BLOCK_SIZE;
        if (offset + size > storage.size()) {
            throw std::runtime_error("Read out of bounds");
        }
        std::memcpy(buffer, storage.data() + offset, size);
    }

    void write_blocks(std::uint64_t lba, std::uint64_t count, const void* buffer) {
        std::size_t offset = lba * BLOCK_SIZE;
        std::size_t size = count * BLOCK_SIZE;
        if (offset + size > storage.size()) {
            throw std::runtime_error("Write out of bounds");
        }
        std::memcpy(storage.data() + offset, buffer, size);
    }
};
