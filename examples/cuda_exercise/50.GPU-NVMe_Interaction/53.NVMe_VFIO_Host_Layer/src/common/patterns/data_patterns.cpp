/**
 * @file data_patterns.cpp
 * @brief Implementation of data pattern generation and verification
 *
 * Migrated from test/helper/pattern_helper.cpp to src/common/patterns/
 * for production use.
 *
 * @date 2025-11-20
 */

#include "common/patterns/data_patterns.h"
#include <cstdio>
#include <cstring>
#include <algorithm>
#include <stdexcept>

namespace nvme {
namespace patterns {

// Static member initialization
uint32_t DataPatterns::crc32_table_[256];
bool DataPatterns::crc32_table_initialized_ = false;

void DataPatterns::init_crc32_table() {
    if (crc32_table_initialized_) return;

    for (uint32_t i = 0; i < 256; i++) {
        uint32_t crc = i;
        for (int j = 0; j < 8; j++) {
            crc = (crc & 1) ? (crc >> 1) ^ 0xEDB88320 : (crc >> 1);
        }
        crc32_table_[i] = crc;
    }
    crc32_table_initialized_ = true;
}

// Implementation helpers
void DataPatterns::fill_sequential_impl(uint8_t* buf, size_t bytes, size_t offset) {
    for (size_t i = 0; i < bytes; i++) {
        buf[i] = static_cast<uint8_t>((offset + i) & 0xFF);
    }
}

void DataPatterns::fill_alternating_impl(uint8_t* buf, size_t bytes) {
    for (size_t i = 0; i < bytes; i++) {
        buf[i] = (i % 2 == 0) ? 0xAA : 0x55;
    }
}

void DataPatterns::fill_block_based_impl(uint8_t* buf, size_t bytes,
                                         uint32_t block_size, uint32_t start_block) {
    size_t num_blocks = bytes / block_size;
    for (size_t block = 0; block < num_blocks; block++) {
        uint8_t* block_start = buf + (block * block_size);
        uint32_t block_num = start_block + static_cast<uint32_t>(block);

        // First 4 bytes: block number
        *reinterpret_cast<uint32_t*>(block_start) = block_num;

        // Rest: sequential pattern
        for (size_t i = 4; i < block_size; i++) {
            block_start[i] = static_cast<uint8_t>((block_num + i) & 0xFF);
        }
    }
}

void DataPatterns::fill_prime_impl(uint8_t* buf, size_t bytes) {
    // Simple prime-based pattern using first few primes
    const uint8_t primes[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (size_t i = 0; i < bytes; i++) {
        buf[i] = primes[i % (sizeof(primes) / sizeof(primes[0]))];
    }
}

void DataPatterns::fill_random_impl(uint8_t* buf, size_t bytes, uint32_t seed) {
    uint32_t state = seed;
    for (size_t i = 0; i < bytes; i++) {
        // Simple LCG PRNG
        state = state * 1103515245 + 12345;
        buf[i] = static_cast<uint8_t>((state >> 16) & 0xFF);
    }
}

bool DataPatterns::verify_sequential_impl(const uint8_t* buf, size_t bytes, size_t offset) {
    for (size_t i = 0; i < bytes; i++) {
        uint8_t expected = static_cast<uint8_t>((offset + i) & 0xFF);
        if (buf[i] != expected) {
            return false;
        }
    }
    return true;
}

bool DataPatterns::verify_alternating_impl(const uint8_t* buf, size_t bytes) {
    for (size_t i = 0; i < bytes; i++) {
        uint8_t expected = (i % 2 == 0) ? 0xAA : 0x55;
        if (buf[i] != expected) {
            return false;
        }
    }
    return true;
}

bool DataPatterns::verify_block_based_impl(const uint8_t* buf, size_t bytes,
                                           uint32_t block_size, uint32_t start_block) {
    size_t num_blocks = bytes / block_size;
    for (size_t block = 0; block < num_blocks; block++) {
        const uint8_t* block_start = buf + (block * block_size);
        uint32_t expected_block = start_block + static_cast<uint32_t>(block);

        // Check block number
        uint32_t block_num = *reinterpret_cast<const uint32_t*>(block_start);
        if (block_num != expected_block) {
            return false;
        }

        // Check sequential pattern
        for (size_t i = 4; i < block_size; i++) {
            uint8_t expected = static_cast<uint8_t>((expected_block + i) & 0xFF);
            if (block_start[i] != expected) {
                return false;
            }
        }
    }
    return true;
}

// Public API
bool DataPatterns::fill(void* buffer, size_t size, PatternType type, size_t offset) {
    if (!buffer || size == 0) {
        return false;
    }

    uint8_t* buf = static_cast<uint8_t*>(buffer);

    switch (type) {
        case PatternType::SEQUENTIAL:
            fill_sequential_impl(buf, size, offset);
            break;
        case PatternType::ALTERNATING:
            fill_alternating_impl(buf, size);
            break;
        case PatternType::PRIME_BASED:
            fill_prime_impl(buf, size);
            break;
        case PatternType::RANDOM:
            fill_random_impl(buf, size, static_cast<uint32_t>(offset));
            break;
        default:
            return false;
    }

    return true;
}

bool DataPatterns::verify(const void* buffer, size_t size, PatternType type, size_t offset) {
    if (!buffer || size == 0) {
        return false;
    }

    const uint8_t* buf = static_cast<const uint8_t*>(buffer);

    switch (type) {
        case PatternType::SEQUENTIAL:
            return verify_sequential_impl(buf, size, offset);
        case PatternType::ALTERNATING:
            return verify_alternating_impl(buf, size);
        case PatternType::BLOCK_BASED:
            // Block-based needs special handling
            return false;
        default:
            return false;
    }
}

bool DataPatterns::fill_blocks(void* buffer, size_t size, uint32_t block_size,
                               uint32_t start_block) {
    if (!buffer || size == 0 || block_size == 0) {
        return false;
    }
    if (size % block_size != 0) {
        return false;  // Size must be multiple of block_size
    }

    uint8_t* buf = static_cast<uint8_t*>(buffer);
    fill_block_based_impl(buf, size, block_size, start_block);
    return true;
}

bool DataPatterns::verify_blocks(const void* buffer, size_t size, uint32_t block_size,
                                 uint32_t start_block) {
    if (!buffer || size == 0 || block_size == 0) {
        return false;
    }
    if (size % block_size != 0) {
        return false;
    }

    const uint8_t* buf = static_cast<const uint8_t*>(buffer);
    return verify_block_based_impl(buf, size, block_size, start_block);
}

const char* DataPatterns::pattern_name(PatternType type) {
    switch (type) {
        case PatternType::SEQUENTIAL:    return "Sequential";
        case PatternType::ALTERNATING:   return "Alternating";
        case PatternType::BLOCK_BASED:   return "Block-based";
        case PatternType::PRIME_BASED:   return "Prime-based";
        case PatternType::RANDOM:        return "Random";
        case PatternType::CHECKSUM:      return "Checksum";
        default:                         return "Unknown";
    }
}

uint32_t DataPatterns::calculate_crc32(const void* buffer, size_t size) {
    init_crc32_table();

    const uint8_t* buf = static_cast<const uint8_t*>(buffer);
    uint32_t crc = 0xFFFFFFFF;

    for (size_t i = 0; i < size; i++) {
        uint8_t index = (crc ^ buf[i]) & 0xFF;
        crc = (crc >> 8) ^ crc32_table_[index];
    }

    return crc ^ 0xFFFFFFFF;
}

bool DataPatterns::fill_with_checksum(void* buffer, size_t size, PatternType type) {
    if (!buffer || size < 4) {
        return false;
    }

    // Fill pattern (leave last 4 bytes for checksum)
    if (!fill(buffer, size - 4, type, 0)) {
        return false;
    }

    // Calculate and embed checksum
    uint32_t crc = calculate_crc32(buffer, size - 4);
    uint8_t* buf = static_cast<uint8_t*>(buffer);
    *reinterpret_cast<uint32_t*>(buf + size - 4) = crc;

    return true;
}

bool DataPatterns::verify_with_checksum(const void* buffer, size_t size, PatternType type) {
    if (!buffer || size < 4) {
        return false;
    }

    const uint8_t* buf = static_cast<const uint8_t*>(buffer);

    // Verify pattern
    if (!verify(buffer, size - 4, type, 0)) {
        return false;
    }

    // Verify checksum
    uint32_t stored_crc = *reinterpret_cast<const uint32_t*>(buf + size - 4);
    uint32_t computed_crc = calculate_crc32(buffer, size - 4);

    return stored_crc == computed_crc;
}

bool DataPatterns::find_first_mismatch(const void* buffer, size_t size, PatternType type,
                                       size_t offset, size_t* mismatch_offset,
                                       uint8_t* expected, uint8_t* actual) {
    if (!buffer || size == 0) {
        return false;
    }

    const uint8_t* buf = static_cast<const uint8_t*>(buffer);

    for (size_t i = 0; i < size; i++) {
        uint8_t exp = 0;

        switch (type) {
            case PatternType::SEQUENTIAL:
                exp = static_cast<uint8_t>((offset + i) & 0xFF);
                break;
            case PatternType::ALTERNATING:
                exp = (i % 2 == 0) ? 0xAA : 0x55;
                break;
            default:
                return false;
        }

        if (buf[i] != exp) {
            if (mismatch_offset) *mismatch_offset = i;
            if (expected) *expected = exp;
            if (actual) *actual = buf[i];
            return true;  // Found mismatch
        }
    }

    return false;  // No mismatch
}

// PatternBuffer RAII implementation
PatternBuffer::PatternBuffer(size_t size)
    : buffer_(nullptr), size_(size) {
    if (size > 0) {
        buffer_ = ::operator new(size);
    }
}

PatternBuffer::~PatternBuffer() {
    if (buffer_) {
        ::operator delete(buffer_);
    }
}

PatternBuffer::PatternBuffer(PatternBuffer&& other) noexcept
    : buffer_(other.buffer_), size_(other.size_) {
    other.buffer_ = nullptr;
    other.size_ = 0;
}

PatternBuffer& PatternBuffer::operator=(PatternBuffer&& other) noexcept {
    if (this != &other) {
        if (buffer_) {
            ::operator delete(buffer_);
        }
        buffer_ = other.buffer_;
        size_ = other.size_;
        other.buffer_ = nullptr;
        other.size_ = 0;
    }
    return *this;
}

bool PatternBuffer::fill(PatternType type, size_t offset) {
    return DataPatterns::fill(buffer_, size_, type, offset);
}

bool PatternBuffer::verify(PatternType type, size_t offset) const {
    return DataPatterns::verify(buffer_, size_, type, offset);
}

} // namespace patterns
} // namespace nvme