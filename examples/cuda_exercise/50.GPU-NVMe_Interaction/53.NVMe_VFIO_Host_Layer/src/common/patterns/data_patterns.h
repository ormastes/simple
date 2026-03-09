/**
 * @file data_patterns.h
 * @brief Data pattern generation and verification utilities
 *
 * General-purpose utility for data integrity verification in NVMe operations.
 * Moved from test/helper/pattern_helper.h to src/common/ for production use.
 *
 * Used by both tests and production code for:
 * - NVMe data verification after read operations
 * - Memory corruption detection
 * - DMA transfer validation
 * - Data integrity checks in storage operations
 */

#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <memory>

namespace nvme {
namespace patterns {

/**
 * @brief Supported data pattern types
 */
enum class PatternType {
    SEQUENTIAL,    ///< data[i] = (base_offset + i) & 0xFF
    ALTERNATING,   ///< data[i] = (i % 2 == 0) ? 0xAA : 0x55
    BLOCK_BASED,   ///< Each block starts with block number
    PRIME_BASED,   ///< Prime number based pattern
    RANDOM,        ///< Pseudo-random with seed
    CHECKSUM       ///< Pattern with embedded checksum
};

/**
 * @brief Data pattern generator and verifier
 *
 * Thread-safe utility class for generating and verifying data patterns.
 * All methods are static for easy use without instantiation.
 */
class DataPatterns {
public:
    /**
     * @brief Fill buffer with specified pattern
     *
     * @param buffer Pointer to buffer to fill
     * @param size Size in bytes
     * @param type Pattern type to generate
     * @param offset Base offset for pattern (default: 0)
     * @return true on success, false on error
     */
    static bool fill(void* buffer, size_t size, PatternType type, size_t offset = 0);

    /**
     * @brief Verify buffer contains expected pattern
     *
     * @param buffer Pointer to buffer to verify
     * @param size Size in bytes
     * @param type Expected pattern type
     * @param offset Base offset used during fill
     * @return true if pattern matches, false otherwise
     */
    static bool verify(const void* buffer, size_t size, PatternType type, size_t offset = 0);

    /**
     * @brief Fill with block-based pattern for NVMe operations
     *
     * @param buffer Buffer to fill
     * @param size Size in bytes (must be multiple of block_size)
     * @param block_size Logical block size (typically 512 or 4096)
     * @param start_block Starting block number
     * @return true on success, false if size not aligned
     */
    static bool fill_blocks(void* buffer, size_t size, uint32_t block_size,
                           uint32_t start_block = 0);

    /**
     * @brief Verify block-based pattern
     *
     * @param buffer Buffer to verify
     * @param size Size in bytes
     * @param block_size Logical block size
     * @param start_block Expected starting block number
     * @return true if valid, false otherwise
     */
    static bool verify_blocks(const void* buffer, size_t size, uint32_t block_size,
                             uint32_t start_block = 0);

    /**
     * @brief Get human-readable pattern name
     *
     * @param type Pattern type
     * @return String name of pattern
     */
    static const char* pattern_name(PatternType type);

    /**
     * @brief Calculate CRC32 checksum of buffer
     *
     * Useful for production data integrity checks
     *
     * @param buffer Buffer to checksum
     * @param size Size in bytes
     * @return CRC32 checksum value
     */
    static uint32_t calculate_crc32(const void* buffer, size_t size);

    /**
     * @brief Fill buffer with pattern and embed checksum
     *
     * Fills buffer with pattern and embeds CRC32 at the end.
     * Useful for production data integrity verification.
     *
     * @param buffer Buffer to fill (last 4 bytes used for checksum)
     * @param size Total size including checksum
     * @param type Pattern type for data portion
     * @return true on success, false if size < 4
     */
    static bool fill_with_checksum(void* buffer, size_t size, PatternType type);

    /**
     * @brief Verify pattern and checksum
     *
     * @param buffer Buffer to verify
     * @param size Total size including checksum
     * @param type Expected pattern type
     * @return true if both pattern and checksum valid
     */
    static bool verify_with_checksum(const void* buffer, size_t size, PatternType type);

    /**
     * @brief Get first mismatch location in pattern
     *
     * Useful for debugging data corruption issues
     *
     * @param buffer Buffer to check
     * @param size Size in bytes
     * @param type Expected pattern
     * @param offset Pattern offset
     * @param[out] mismatch_offset Offset of first mismatch (if found)
     * @param[out] expected Expected byte value
     * @param[out] actual Actual byte value
     * @return true if mismatch found, false if pattern matches
     */
    static bool find_first_mismatch(const void* buffer, size_t size, PatternType type,
                                   size_t offset, size_t* mismatch_offset,
                                   uint8_t* expected, uint8_t* actual);

private:
    // Implementation helpers
    static void fill_sequential_impl(uint8_t* buf, size_t bytes, size_t offset);
    static void fill_alternating_impl(uint8_t* buf, size_t bytes);
    static void fill_block_based_impl(uint8_t* buf, size_t bytes, uint32_t block_size,
                                     uint32_t start_block);
    static void fill_prime_impl(uint8_t* buf, size_t bytes);
    static void fill_random_impl(uint8_t* buf, size_t bytes, uint32_t seed);

    static bool verify_sequential_impl(const uint8_t* buf, size_t bytes, size_t offset);
    static bool verify_alternating_impl(const uint8_t* buf, size_t bytes);
    static bool verify_block_based_impl(const uint8_t* buf, size_t bytes,
                                       uint32_t block_size, uint32_t start_block);

    // CRC32 implementation
    static uint32_t crc32_table_[256];
    static bool crc32_table_initialized_;
    static void init_crc32_table();
};

/**
 * @brief RAII pattern buffer for automatic cleanup
 *
 * Useful for production code that needs temporary pattern buffers
 */
class PatternBuffer {
public:
    explicit PatternBuffer(size_t size);
    ~PatternBuffer();

    // Delete copy operations
    PatternBuffer(const PatternBuffer&) = delete;
    PatternBuffer& operator=(const PatternBuffer&) = delete;

    // Allow move operations
    PatternBuffer(PatternBuffer&& other) noexcept;
    PatternBuffer& operator=(PatternBuffer&& other) noexcept;

    bool fill(PatternType type, size_t offset = 0);
    bool verify(PatternType type, size_t offset = 0) const;

    void* data() { return buffer_; }
    const void* data() const { return buffer_; }
    size_t size() const { return size_; }

private:
    void* buffer_;
    size_t size_;
};

} // namespace patterns
} // namespace nvme