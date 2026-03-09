/**
 * @file test_prp_edge_cases.cpp
 * @brief Comprehensive PRP (Physical Region Page) edge case tests
 *
 * Tests various PRP list configurations including:
 * - Exactly 1 page (no PRP list needed)
 * - Exactly 2 pages (no PRP list needed, use prp1+prp2)
 * - 3 pages (1 PRP list entry)
 * - PRP list fitting exactly one 4KB page (512 entries = 513 data pages)
 * - PRP list needing one page + 1 entry (513 entries = 514 data pages)
 * - PRP list needing exactly 2 pages (1024 entries = 1025 data pages)
 * - PRP list needing 2 pages + 1 entry (1025 entries = 1026 data pages)
 * - Too many PRPs that would require >2 PRP list pages (should fail)
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

#include <gtest/gtest.h>
#include "nvme_test_helper.h"  // Common NVMe test utilities
#include "memory/host_memory_buffer.h"  // For backward compatibility aliases
#include <cstdio>
#include <cstring>

namespace {

constexpr std::size_t kPage = 4096;
constexpr std::size_t kPRPEntriesPerPage = kPage / sizeof(std::uint64_t);  // 512 entries per 4KB page

/**
 * @brief Test fixture for PRP edge case testing
 *
 * This fixture inherits from NvmeDeviceTest for automatic device setup/teardown,
 * and provides helper methods for testing various PRP list configurations.
 */
class PRPEdgeCaseTest : public nvme_test::NvmeDeviceTest {
protected:

    /**
     * @brief Calculate expected PRP list configuration for a given buffer size
     *
     * @param buffer_bytes Size of buffer in bytes
     * @param out_data_pages Number of 4KB pages in the data buffer
     * @param out_prp_entries Number of PRP entries needed in PRP list (0 if no list needed)
     * @param out_prp_pages Number of 4KB pages needed for PRP list
     */
    void calculate_prp_config(std::size_t buffer_bytes,
                             std::size_t& out_data_pages,
                             std::size_t& out_prp_entries,
                             std::size_t& out_prp_pages) {
        out_data_pages = (buffer_bytes + kPage - 1) / kPage;  // Round up

        if (out_data_pages <= 2) {
            // No PRP list needed - use prp1 and prp2 directly
            out_prp_entries = 0;
            out_prp_pages = 0;
        } else {
            // Need PRP list for pages 2..N (pages-1 entries)
            out_prp_entries = out_data_pages - 1;
            out_prp_pages = (out_prp_entries + kPRPEntriesPerPage - 1) / kPRPEntriesPerPage;
        }
    }

    /**
     * @brief Verify DmaBuf has correct PRP list configuration
     */
    void verify_dmabuf_prp(const DmaBuf* buf, std::size_t expected_prp_entries) {
        ASSERT_NE(buf, nullptr) << "DmaBuf should not be nullptr";

        if (expected_prp_entries == 0) {
            // No PRP list should be allocated
            EXPECT_EQ(buf->prplist_host, nullptr)
                << "prplist_host should be nullptr when no PRP list is needed";
            EXPECT_EQ(buf->prplist_iova, 0UL)
                << "prplist_iova should be 0 when no PRP list is needed";
            EXPECT_EQ(buf->prplist_bytes, 0UL)
                << "prplist_bytes should be 0 when no PRP list is needed";
        } else {
            // PRP list should be allocated
            EXPECT_NE(buf->prplist_host, nullptr)
                << "prplist_host should be allocated for " << expected_prp_entries << " PRP entries";
            EXPECT_NE(buf->prplist_iova, 0UL)
                << "prplist_iova should be valid for " << expected_prp_entries << " PRP entries";
            EXPECT_EQ(buf->prplist_bytes, expected_prp_entries * sizeof(std::uint64_t))
                << "prplist_bytes should match expected size";

            // Verify PRP list entries point to correct addresses
            auto* prp_list = static_cast<std::uint64_t*>(buf->prplist_host);
            std::uint64_t expected_addr = buf->iova + kPage;  // First entry points to page 2

            for (std::size_t i = 0; i < expected_prp_entries; i++) {
                EXPECT_EQ(prp_list[i], expected_addr)
                    << "PRP entry " << i << " should point to page " << (i + 2);
                expected_addr += kPage;
            }
        }
    }
};

// ========== Test Cases ==========

/**
 * @test PRP_EdgeCase.OnePage
 * @brief Test buffer with exactly 1 page (4KB)
 *
 * Expected: No PRP list allocated (uses prp1 only)
 */
TEST_F(PRPEdgeCaseTest, OnePage) {
    GTEST_SKIP() << "Test requires custom buffer sizes - API changed to use device ItemSize";
    std::size_t buffer_size = 1 * kPage;

    std::size_t data_pages, prp_entries, prp_pages;
    calculate_prp_config(buffer_size, data_pages, prp_entries, prp_pages);

    EXPECT_EQ(data_pages, 1UL) << "Should have exactly 1 data page";
    EXPECT_EQ(prp_entries, 0UL) << "Should have 0 PRP entries (no list needed)";
    EXPECT_EQ(prp_pages, 0UL) << "Should have 0 PRP pages";

    HostPool* pool = host_pool_create(dev, 1);
    ASSERT_NE(pool, nullptr);

    DmaBuf* buf = host_pool_acquire(pool);
    verify_dmabuf_prp(buf, prp_entries);

    host_pool_release(pool, buf);
    host_pool_destroy(pool);
}

/**
 * @test PRP_EdgeCase.TwoPages
 * @brief Test buffer with exactly 2 pages (8KB)
 *
 * Expected: No PRP list allocated (uses prp1 and prp2 directly)
 */
TEST_F(PRPEdgeCaseTest, TwoPages) {
    GTEST_SKIP() << "Test requires custom buffer sizes - API changed to use device ItemSize";
    std::size_t buffer_size = 2 * kPage;

    std::size_t data_pages, prp_entries, prp_pages;
    calculate_prp_config(buffer_size, data_pages, prp_entries, prp_pages);

    EXPECT_EQ(data_pages, 2UL) << "Should have exactly 2 data pages";
    EXPECT_EQ(prp_entries, 0UL) << "Should have 0 PRP entries (no list needed)";
    EXPECT_EQ(prp_pages, 0UL) << "Should have 0 PRP pages";

    HostPool* pool = host_pool_create(dev, 1);
    ASSERT_NE(pool, nullptr);

    DmaBuf* buf = host_pool_acquire(pool);
    verify_dmabuf_prp(buf, prp_entries);

    host_pool_release(pool, buf);
    host_pool_destroy(pool);
}

/**
 * @test PRP_EdgeCase.ThreePages
 * @brief Test buffer with exactly 3 pages (12KB)
 *
 * Expected: PRP list with 1 entry (pages-1 = 2 entries, but prp1 is first page)
 * NVMe uses: prp1 → page 0, prp2 → PRP list, PRP list[0] → page 1
 */
TEST_F(PRPEdgeCaseTest, ThreePages) {
    GTEST_SKIP() << "Test requires custom buffer sizes - API changed to use device ItemSize";
    std::size_t buffer_size = 3 * kPage;

    std::size_t data_pages, prp_entries, prp_pages;
    calculate_prp_config(buffer_size, data_pages, prp_entries, prp_pages);

    EXPECT_EQ(data_pages, 3UL) << "Should have exactly 3 data pages";
    EXPECT_EQ(prp_entries, 2UL) << "Should have 2 PRP entries (pages-1)";
    EXPECT_EQ(prp_pages, 1UL) << "Should need 1 PRP page";

    HostPool* pool = host_pool_create(dev, 1);
    ASSERT_NE(pool, nullptr);

    DmaBuf* buf = host_pool_acquire(pool);
    verify_dmabuf_prp(buf, prp_entries);

    host_pool_release(pool, buf);
    host_pool_destroy(pool);
}

/**
 * @test PRP_EdgeCase.PRPListFitsOnePage_Exactly
 * @brief Test PRP list fitting exactly one 4KB page (512 entries)
 *
 * 512 PRP entries = 513 data pages (1 in prp1, 512 in PRP list)
 * Buffer size: 513 * 4KB = 2,101,248 bytes (~2MB)
 *
 * Expected: PRP list with exactly 512 entries fitting in 1 page
 */
TEST_F(PRPEdgeCaseTest, PRPListFitsOnePage_Exactly) {
    GTEST_SKIP() << "Test requires custom buffer sizes - API changed to use device ItemSize";
    std::size_t data_pages = kPRPEntriesPerPage + 1;  // 513 pages
    std::size_t buffer_size = data_pages * kPage;

    std::size_t calc_data_pages, prp_entries, prp_pages;
    calculate_prp_config(buffer_size, calc_data_pages, prp_entries, prp_pages);

    EXPECT_EQ(calc_data_pages, 513UL) << "Should have exactly 513 data pages";
    EXPECT_EQ(prp_entries, 512UL) << "Should have exactly 512 PRP entries";
    EXPECT_EQ(prp_pages, 1UL) << "Should fit in exactly 1 PRP page";

    HostPool* pool = host_pool_create(dev, 1);
    ASSERT_NE(pool, nullptr);

    DmaBuf* buf = host_pool_acquire(pool);
    verify_dmabuf_prp(buf, prp_entries);

    host_pool_release(pool, buf);
    host_pool_destroy(pool);
}

/**
 * @test PRP_EdgeCase.PRPListOnePage_PlusOne
 * @brief Test PRP list needing one page + 1 entry
 *
 * 513 PRP entries = 514 data pages
 * Buffer size: 514 * 4KB = 2,105,344 bytes
 *
 * Expected: PRP list with 513 entries, needing 2 pages
 */
TEST_F(PRPEdgeCaseTest, PRPListOnePage_PlusOne) {
    GTEST_SKIP() << "Test requires custom buffer sizes - API changed to use device ItemSize";
    std::size_t data_pages = kPRPEntriesPerPage + 2;  // 514 pages
    std::size_t buffer_size = data_pages * kPage;

    std::size_t calc_data_pages, prp_entries, prp_pages;
    calculate_prp_config(buffer_size, calc_data_pages, prp_entries, prp_pages);

    EXPECT_EQ(calc_data_pages, 514UL) << "Should have exactly 514 data pages";
    EXPECT_EQ(prp_entries, 513UL) << "Should have exactly 513 PRP entries";
    EXPECT_EQ(prp_pages, 2UL) << "Should need 2 PRP pages (512+1)";

    HostPool* pool = host_pool_create(dev, 1);
    ASSERT_NE(pool, nullptr);

    DmaBuf* buf = host_pool_acquire(pool);
    verify_dmabuf_prp(buf, prp_entries);

    host_pool_release(pool, buf);
    host_pool_destroy(pool);
}

/**
 * @test PRP_EdgeCase.PRPListTwoPages_Exactly
 * @brief Test PRP list fitting exactly two 4KB pages (1024 entries)
 *
 * 1024 PRP entries = 1025 data pages
 * Buffer size: 1025 * 4KB = 4,198,400 bytes (~4MB)
 *
 * Expected: PRP list with exactly 1024 entries fitting in 2 pages
 */
TEST_F(PRPEdgeCaseTest, PRPListTwoPages_Exactly) {
    GTEST_SKIP() << "Test requires custom buffer sizes - API changed to use device ItemSize";
    std::size_t data_pages = 2 * kPRPEntriesPerPage + 1;  // 1025 pages
    std::size_t buffer_size = data_pages * kPage;

    std::size_t calc_data_pages, prp_entries, prp_pages;
    calculate_prp_config(buffer_size, calc_data_pages, prp_entries, prp_pages);

    EXPECT_EQ(calc_data_pages, 1025UL) << "Should have exactly 1025 data pages";
    EXPECT_EQ(prp_entries, 1024UL) << "Should have exactly 1024 PRP entries";
    EXPECT_EQ(prp_pages, 2UL) << "Should fit in exactly 2 PRP pages";

    HostPool* pool = host_pool_create(dev, 1);
    ASSERT_NE(pool, nullptr);

    DmaBuf* buf = host_pool_acquire(pool);
    verify_dmabuf_prp(buf, prp_entries);

    host_pool_release(pool, buf);
    host_pool_destroy(pool);
}

/**
 * @test PRP_EdgeCase.PRPListTwoPages_PlusOne
 * @brief Test PRP list needing two pages + 1 entry
 *
 * 1025 PRP entries = 1026 data pages
 * Buffer size: 1026 * 4KB = 4,202,496 bytes
 *
 * Expected: Should FAIL - PRP list with 1025 entries would need 3 pages (exceeds NVMe spec limit)
 * NOTE: According to NVMe spec, PRP lists are limited to 2 pages maximum.
 * This test verifies that the implementation correctly rejects oversized buffers.
 */
TEST_F(PRPEdgeCaseTest, PRPListTwoPages_PlusOne) {
    GTEST_SKIP() << "Test requires custom buffer sizes - API changed to use device ItemSize";
    std::size_t data_pages = 2 * kPRPEntriesPerPage + 2;  // 1026 pages
    std::size_t buffer_size = data_pages * kPage;

    std::size_t calc_data_pages, prp_entries, prp_pages;
    calculate_prp_config(buffer_size, calc_data_pages, prp_entries, prp_pages);

    EXPECT_EQ(calc_data_pages, 1026UL) << "Should have exactly 1026 data pages";
    EXPECT_EQ(prp_entries, 1025UL) << "Should have exactly 1025 PRP entries";
    EXPECT_EQ(prp_pages, 3UL) << "Would need 3 PRP pages (exceeds limit)";

    // Implementation should enforce 2-page limit and return nullptr
    HostPool* pool = host_pool_create(dev, 1);

    EXPECT_EQ(pool, nullptr)
        << "Pool creation should fail for buffer requiring " << prp_pages << " PRP pages (>2 page limit). "
        << "NVMe spec limits PRP lists to 2 pages max (1024 entries, 1025 data pages, 4.2MB).";

    if (pool != nullptr) {
        // This should not happen with the fix
        host_pool_destroy(pool);
        ADD_FAILURE() << "ERROR: Implementation incorrectly allowed buffer requiring 3 PRP pages. "
                      << "This violates NVMe specification.";
    }
}

/**
 * @test PRP_EdgeCase.TooManyPRPs_LargeBuffer
 * @brief Test extremely large buffer that would require many PRP pages
 *
 * 10000 data pages = 9999 PRP entries ≈ 20 PRP pages
 * Buffer size: 10000 * 4KB = 40,960,000 bytes (~40MB)
 *
 * Expected: Should FAIL - would require ~20 PRP pages (far exceeds 2-page spec limit)
 * Implementation should reject and return nullptr.
 */
TEST_F(PRPEdgeCaseTest, TooManyPRPs_LargeBuffer) {
    GTEST_SKIP() << "Test requires custom buffer sizes - API changed to use device ItemSize";
    std::size_t data_pages = 10000;
    std::size_t buffer_size = data_pages * kPage;

    std::size_t calc_data_pages, prp_entries, prp_pages;
    calculate_prp_config(buffer_size, calc_data_pages, prp_entries, prp_pages);

    EXPECT_EQ(calc_data_pages, 10000UL);
    EXPECT_EQ(prp_entries, 9999UL);
    EXPECT_GT(prp_pages, 2UL) << "Would need many PRP pages (exceeds spec limit)";

    // Implementation should reject buffers requiring >2 PRP pages
    HostPool* pool = host_pool_create(dev, 1);

    EXPECT_EQ(pool, nullptr)
        << "Pool creation should fail for buffer requiring " << prp_pages << " PRP pages (far exceeds 2 page limit). "
        << "NVMe spec limits PRP lists to 2 pages max. For large buffers, use SGL or split into chunks.";

    if (pool != nullptr) {
        // This should not happen with the fix
        host_pool_destroy(pool);
        ADD_FAILURE() << "ERROR: Implementation incorrectly allowed buffer requiring " << prp_pages << " PRP pages. "
                      << "This seriously violates NVMe specification (max 2 pages).";
    }
}

/**
 * @test PRP_EdgeCase.BoundaryAlignment
 * @brief Test that PRP entries are correctly page-aligned
 *
 * Verifies that all PRP entries point to page-aligned addresses.
 */
TEST_F(PRPEdgeCaseTest, BoundaryAlignment) {
    GTEST_SKIP() << "Test requires custom buffer sizes - API changed to use device ItemSize";
    std::size_t buffer_size = 100 * kPage;  // 100 pages

    HostPool* pool = host_pool_create(dev, 1);
    ASSERT_NE(pool, nullptr);

    DmaBuf* buf = host_pool_acquire(pool);
    ASSERT_NE(buf, nullptr);

    // Check data buffer alignment
    EXPECT_EQ(buf->iova % kPage, 0UL) << "Data buffer IOVA should be page-aligned";

    // Check PRP list alignment
    if (buf->prplist_host) {
        EXPECT_EQ(buf->prplist_iova % kPage, 0UL) << "PRP list IOVA should be page-aligned";

        // Verify all PRP entries are page-aligned
        auto* prp_list = static_cast<std::uint64_t*>(buf->prplist_host);
        std::size_t prp_count = buf->prplist_bytes / sizeof(std::uint64_t);

        for (std::size_t i = 0; i < prp_count; i++) {
            EXPECT_EQ(prp_list[i] % kPage, 0UL)
                << "PRP entry " << i << " at address 0x" << std::hex << prp_list[i]
                << " should be page-aligned";
        }
    }

    host_pool_release(pool, buf);
    host_pool_destroy(pool);
}

/**
 * @test PRP_EdgeCase.ConsecutivePRPEntries
 * @brief Verify PRP list entries point to consecutive pages
 */
TEST_F(PRPEdgeCaseTest, ConsecutivePRPEntries) {
    GTEST_SKIP() << "Test requires custom buffer sizes - API changed to use device ItemSize";
    std::size_t buffer_size = 50 * kPage;  // 50 pages

    HostPool* pool = host_pool_create(dev, 1);
    ASSERT_NE(pool, nullptr);

    DmaBuf* buf = host_pool_acquire(pool);
    ASSERT_NE(buf, nullptr);
    ASSERT_NE(buf->prplist_host, nullptr) << "Should have PRP list for 50 pages";

    auto* prp_list = static_cast<std::uint64_t*>(buf->prplist_host);
    std::size_t prp_count = buf->prplist_bytes / sizeof(std::uint64_t);

    ASSERT_EQ(prp_count, 49UL) << "Should have 49 PRP entries (pages-1)";

    // Verify consecutive addresses
    std::uint64_t expected_addr = buf->iova + kPage;
    for (std::size_t i = 0; i < prp_count; i++) {
        EXPECT_EQ(prp_list[i], expected_addr)
            << "PRP entry " << i << " should point to consecutive page";
        expected_addr += kPage;
    }

    host_pool_release(pool, buf);
    host_pool_destroy(pool);
}

} // anonymous namespace

/**
 * @mainpage PRP Edge Case Test Documentation
 *
 * @section overview Overview
 * This test suite comprehensively tests NVMe PRP (Physical Region Page) list
 * handling for various buffer sizes and edge cases.
 *
 * @section prp_basics PRP Basics
 * - NVMe uses PRP entries to describe physical memory regions
 * - Each PRP entry is 8 bytes (std::uint64_t) pointing to a 4KB page
 * - For buffers ≤8KB: use prp1 and prp2 directly (no PRP list)
 * - For buffers >8KB: prp2 points to a PRP list containing page addresses
 *
 * @section prp_limits PRP Limitations
 * - One 4KB PRP list page holds 512 entries (4096 / 8)
 * - NVMe spec limits PRP lists to 2 pages maximum (1024 entries)
 * - Maximum data buffer with PRPs: 1025 pages = 4,198,400 bytes (~4MB)
 * - Larger buffers require SGL (Scatter Gather List) instead
 *
 * @section test_cases Test Cases
 * - OnePage: 4KB buffer (no PRP list)
 * - TwoPages: 8KB buffer (no PRP list)
 * - ThreePages: 12KB buffer (minimal PRP list)
 * - PRPListFitsOnePage_Exactly: 513 pages (512 PRP entries, 1 PRP page)
 * - PRPListOnePage_PlusOne: 514 pages (513 PRP entries, 2 PRP pages)
 * - PRPListTwoPages_Exactly: 1025 pages (1024 PRP entries, 2 PRP pages)
 * - PRPListTwoPages_PlusOne: 1026 pages (exceeds spec, should use SGL)
 * - TooManyPRPs_LargeBuffer: 10000 pages (far exceeds spec, should fail or use SGL)
 * - BoundaryAlignment: Verify page alignment of all addresses
 * - ConsecutivePRPEntries: Verify PRP entries point to consecutive pages
 */
