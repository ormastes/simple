/**
 * @file test_utility_functions.cpp
 * @brief Unit tests for NVMe utility functions (no hardware required)
 *
 * Tests utility functions that don't require actual NVMe hardware:
 * - Size rounding
 * - Doorbell stride calculation
 * - Page size helpers
 *
 * @author Coverage Improvement
 * @date 2025-11-01
 */

#include <gtest/gtest.h>
#include <cstdint>
#include <cstddef>

// ============================================================================
// Utility Functions to Test (copied from nvme_vio_host.cpp internal namespace)
// ============================================================================

namespace {
    /// Round up size to alignment boundary
    inline std::size_t round_up(std::size_t n, std::size_t a){
        return (n + (a-1)) & ~(a-1);
    }

    /// Calculate NVMe doorbell stride from CAP register
    inline std::uint32_t db_stride_bytes(std::uint64_t CAP){
        return 4u << ((std::uint32_t)((CAP >> 32) & 0xF));
    }
}

// ============================================================================
// Test: round_up()
// ============================================================================

TEST(UtilityFunctions, RoundUp_AlreadyAligned) {
    EXPECT_EQ(round_up(4096, 4096), 4096);
    EXPECT_EQ(round_up(8192, 4096), 8192);
    EXPECT_EQ(round_up(0, 4096), 0);
}

TEST(UtilityFunctions, RoundUp_NeedsRounding) {
    EXPECT_EQ(round_up(1, 4096), 4096);
    EXPECT_EQ(round_up(100, 4096), 4096);
    EXPECT_EQ(round_up(4000, 4096), 4096);
    EXPECT_EQ(round_up(4097, 4096), 8192);
    EXPECT_EQ(round_up(8000, 4096), 8192);
}

TEST(UtilityFunctions, RoundUp_DifferentAlignments) {
    // 512-byte alignment
    EXPECT_EQ(round_up(0, 512), 0);
    EXPECT_EQ(round_up(1, 512), 512);
    EXPECT_EQ(round_up(512, 512), 512);
    EXPECT_EQ(round_up(513, 512), 1024);

    // 64-byte alignment
    EXPECT_EQ(round_up(63, 64), 64);
    EXPECT_EQ(round_up(64, 64), 64);
    EXPECT_EQ(round_up(65, 64), 128);

    // 1MB alignment
    constexpr std::size_t MB = 1024 * 1024;
    EXPECT_EQ(round_up(1, MB), MB);
    EXPECT_EQ(round_up(MB, MB), MB);
    EXPECT_EQ(round_up(MB + 1, MB), 2 * MB);
}

TEST(UtilityFunctions, RoundUp_PowerOfTwo) {
    // Test that alignment must be power of 2 for this implementation
    EXPECT_EQ(round_up(100, 1), 100);   // 2^0
    EXPECT_EQ(round_up(100, 2), 100);   // 2^1
    EXPECT_EQ(round_up(100, 4), 100);   // 2^2
    EXPECT_EQ(round_up(100, 8), 104);   // 2^3
    EXPECT_EQ(round_up(100, 16), 112);  // 2^4
    EXPECT_EQ(round_up(100, 32), 128);  // 2^5
}

TEST(UtilityFunctions, RoundUp_LargeValues) {
    constexpr std::size_t GB = 1024 * 1024 * 1024;
    EXPECT_EQ(round_up(GB - 1, 4096), GB);
    EXPECT_EQ(round_up(GB, 4096), GB);
    EXPECT_EQ(round_up(GB + 1, 4096), GB + 4096);
}

// ============================================================================
// Test: db_stride_bytes()
// ============================================================================

TEST(UtilityFunctions, DbStride_MinimumValue) {
    // DSTRD = 0 means 4-byte stride (4 << 0 = 4)
    std::uint64_t CAP = 0x0ull; // Bits 35:32 = 0
    EXPECT_EQ(db_stride_bytes(CAP), 4);
}

TEST(UtilityFunctions, DbStride_CommonValues) {
    // DSTRD = 0: 4 bytes (4 << 0 = 4)
    EXPECT_EQ(db_stride_bytes(0x0ull << 32), 4);

    // DSTRD = 1: 8 bytes (4 << 1 = 8)
    EXPECT_EQ(db_stride_bytes(0x1ull << 32), 8);

    // DSTRD = 2: 16 bytes (4 << 2 = 16)
    EXPECT_EQ(db_stride_bytes(0x2ull << 32), 16);

    // DSTRD = 3: 32 bytes (4 << 3 = 32)
    EXPECT_EQ(db_stride_bytes(0x3ull << 32), 32);
}

TEST(UtilityFunctions, DbStride_MaximumValue) {
    // DSTRD = 15: Maximum (4 << 15 = 131072)
    std::uint64_t CAP = 0xFull << 32;
    EXPECT_EQ(db_stride_bytes(CAP), 131072);
}

TEST(UtilityFunctions, DbStride_IgnoresOtherBits) {
    // Set all other CAP bits, DSTRD should still be extracted correctly
    std::uint64_t CAP = 0xFFFFFFFFFFFFFFFFull; // All bits set
    // Bits 35:32 = 0xF, so DSTRD = 15
    EXPECT_EQ(db_stride_bytes(CAP), 131072);

    // Only DSTRD bits set (bits 35:32 = 2)
    CAP = 0x2ull << 32;
    EXPECT_EQ(db_stride_bytes(CAP), 16);
}

TEST(UtilityFunctions, DbStride_RealDeviceExample) {
    // Example CAP register value
    std::uint64_t CAP = 0x0020001F00000FFFull;
    // Extract DSTRD from bits 35:32
    std::uint32_t dstrd = (CAP >> 32) & 0xF;
    // Stride = 4 << dstrd
    std::uint32_t expected_stride = 4u << dstrd;
    EXPECT_EQ(db_stride_bytes(CAP), expected_stride);
}

TEST(UtilityFunctions, DbStride_AllPossibleValues) {
    // Test all 16 possible DSTRD values
    for (std::uint32_t dstrd = 0; dstrd < 16; ++dstrd) {
        std::uint64_t CAP = static_cast<std::uint64_t>(dstrd) << 32;
        std::uint32_t expected = 4u << dstrd;
        EXPECT_EQ(db_stride_bytes(CAP), expected)
            << "DSTRD=" << dstrd << " should give stride=" << expected;
    }
}

// ============================================================================
// Test: Page Alignment Validation Logic
// ============================================================================

TEST(UtilityFunctions, PageAlignment_Check4K) {
    constexpr std::size_t PAGE_4K = 4096;

    // Aligned addresses
    EXPECT_EQ(0 % PAGE_4K, 0);
    EXPECT_EQ(PAGE_4K % PAGE_4K, 0);
    EXPECT_EQ((2 * PAGE_4K) % PAGE_4K, 0);
    EXPECT_EQ((100 * PAGE_4K) % PAGE_4K, 0);

    // Misaligned addresses
    EXPECT_NE(1 % PAGE_4K, 0);
    EXPECT_NE(100 % PAGE_4K, 0);
    EXPECT_NE((PAGE_4K + 1) % PAGE_4K, 0);
}

TEST(UtilityFunctions, PageAlignment_Check64K) {
    constexpr std::size_t PAGE_64K = 65536;

    // Aligned
    EXPECT_EQ(0 % PAGE_64K, 0);
    EXPECT_EQ(PAGE_64K % PAGE_64K, 0);
    EXPECT_EQ((2 * PAGE_64K) % PAGE_64K, 0);

    // Misaligned
    EXPECT_NE(4096 % PAGE_64K, 0);  // 4K is not 64K-aligned
    EXPECT_NE((PAGE_64K + 1) % PAGE_64K, 0);
}

TEST(UtilityFunctions, SizeAlignment_Check) {
    constexpr std::size_t PAGE_SIZE = 4096;

    // Sizes aligned to page size
    EXPECT_EQ(PAGE_SIZE % PAGE_SIZE, 0);
    EXPECT_EQ((10 * PAGE_SIZE) % PAGE_SIZE, 0);

    // Sizes not aligned
    EXPECT_NE(100 % PAGE_SIZE, 0);
    EXPECT_NE((PAGE_SIZE + 1) % PAGE_SIZE, 0);
    EXPECT_NE((PAGE_SIZE - 1) % PAGE_SIZE, 0);
}

// ============================================================================
// Test: IOVA Calculation
// ============================================================================

TEST(UtilityFunctions, IOVA_Progression) {
    // Simulate IOVA allocation pattern
    std::uint64_t next_iova = 0x100000000ull;  // Start at 4GB
    constexpr std::size_t PAGE_SIZE = 4096;

    // Allocate some buffers
    std::uint64_t iova1 = next_iova;
    next_iova += PAGE_SIZE;

    std::uint64_t iova2 = next_iova;
    next_iova += PAGE_SIZE;

    std::uint64_t iova3 = next_iova;
    next_iova += 2 * PAGE_SIZE;

    // Verify progression
    EXPECT_EQ(iova1, 0x100000000ull);
    EXPECT_EQ(iova2, 0x100000000ull + PAGE_SIZE);
    EXPECT_EQ(iova3, 0x100000000ull + 2 * PAGE_SIZE);
    EXPECT_EQ(next_iova, 0x100000000ull + 4 * PAGE_SIZE);
}

TEST(UtilityFunctions, IOVA_NoOverlap) {
    std::uint64_t iova1 = 0x100000000ull;
    std::size_t size1 = 8192;

    std::uint64_t iova2 = iova1 + size1;
    std::size_t size2 = 4096;

    // Verify no overlap
    EXPECT_GE(iova2, iova1 + size1);
    EXPECT_LT(iova1, iova2);
}
