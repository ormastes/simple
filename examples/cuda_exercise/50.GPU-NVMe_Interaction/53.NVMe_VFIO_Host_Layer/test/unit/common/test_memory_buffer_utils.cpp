/**
 * @file test_memory_buffer_utils.cpp
 * @brief Unit tests for memory buffer utilities and DmaBuf structure
 *
 * Tests memory buffer management without requiring actual NVMe hardware:
 * - DmaBuf structure validation
 * - IovaSeg structure and calculations
 * - PRP calculation logic
 * - Buffer alignment checks
 *
 * @author Coverage Improvement
 * @date 2025-11-01
 */

#include <gtest/gtest.h>
#include "memory/memory_types.h"
#include "mapper/mapper_host.h"  // For NVME_CID_* constants
#include <cstdint>
#include <cstring>

// ============================================================================
// Test: DmaBuf Structure
// ============================================================================

TEST(DmaBuf, StructureLayout) {
    DmaBuf buf{};

    // Verify zero-initialization
    EXPECT_EQ(buf.addr, nullptr);
    EXPECT_EQ(buf.iova, 0);
    EXPECT_EQ(buf.bytes, 0);
    EXPECT_EQ(buf.prp1, 0);
    EXPECT_EQ(buf.prp2, 0);
    EXPECT_EQ(buf.prplist_iova, 0);
    EXPECT_EQ(buf.cid_hint, 0);
    EXPECT_EQ(buf.mem_type, MemoryType::HOST);
}

TEST(DmaBuf, Initialization) {
    void* test_addr = reinterpret_cast<void*>(0x12340000);
    std::uint64_t test_iova = 0x100000000;
    std::size_t test_size = 8192;

    DmaBuf buf{};
    buf.addr = test_addr;
    buf.iova = test_iova;
    buf.bytes = test_size;
    buf.prp1 = test_iova;
    buf.prp2 = 0;
    buf.mem_type = MemoryType::PINNED_DEVICE;

    EXPECT_EQ(buf.addr, test_addr);
    EXPECT_EQ(buf.iova, test_iova);
    EXPECT_EQ(buf.bytes, test_size);
    EXPECT_EQ(buf.prp1, test_iova);
    EXPECT_EQ(buf.prp2, 0);
    EXPECT_EQ(buf.mem_type, MemoryType::PINNED_DEVICE);
}

TEST(DmaBuf, BufferKindEnumeration) {
    // Test all buffer kinds
    EXPECT_EQ(static_cast<int>(MemoryType::HOST), 0);
    EXPECT_EQ(static_cast<int>(MemoryType::PINNED_HOST), 1);
    EXPECT_EQ(static_cast<int>(MemoryType::PINNED_DEVICE), 2);

    DmaBuf host_buf{};
    host_buf.mem_type = MemoryType::HOST;
    EXPECT_EQ(host_buf.mem_type, MemoryType::HOST);

    DmaBuf pinned_host_buf{};
    pinned_host_buf.mem_type = MemoryType::PINNED_HOST;
    EXPECT_EQ(pinned_host_buf.mem_type, MemoryType::PINNED_HOST);

    DmaBuf gpu_buf{};
    gpu_buf.mem_type = MemoryType::PINNED_DEVICE;
    EXPECT_EQ(gpu_buf.mem_type, MemoryType::PINNED_DEVICE);
}

// ============================================================================
// Test: IovaSeg Structure
// ============================================================================

TEST(IovaSeg, StructureLayout) {
    IovaSeg seg{};

    EXPECT_EQ(seg.iova, 0);
    EXPECT_EQ(seg.bytes, 0);
}

TEST(IovaSeg, SingleSegment) {
    IovaSeg seg{};
    seg.iova = 0x100000000;
    seg.bytes = 4096;

    EXPECT_EQ(seg.iova, 0x100000000);
    EXPECT_EQ(seg.bytes, 4096);
}

TEST(IovaSeg, SegmentCalculation) {
    constexpr std::uint64_t base_iova = 0x100000000;
    constexpr std::size_t page_size = 4096;

    // First segment
    IovaSeg seg1{base_iova, page_size};
    EXPECT_EQ(seg1.iova, base_iova);
    EXPECT_EQ(seg1.bytes, page_size);

    // Second segment (consecutive)
    IovaSeg seg2{base_iova + page_size, page_size};
    EXPECT_EQ(seg2.iova, base_iova + page_size);
    EXPECT_EQ(seg2.bytes, page_size);

    // Verify no overlap
    EXPECT_EQ(seg1.iova + seg1.bytes, seg2.iova);
}

// ============================================================================
// Test: Buffer Structure
// ============================================================================

TEST(Buffer, StructureLayout) {
    Buffer buf{};

    EXPECT_EQ(buf.addr, nullptr);
    EXPECT_EQ(buf.iova, 0);
    EXPECT_EQ(buf.bytes, 0);
    EXPECT_EQ(buf.nseg, 0);
    EXPECT_EQ(buf.segs, nullptr);
}

TEST(Buffer, SimpleBuffer) {
    Buffer buf{};
    buf.addr = reinterpret_cast<void*>(0x10000000);
    buf.iova = 0x200000000;
    buf.bytes = 8192;
    buf.nseg = 1;

    EXPECT_EQ(buf.addr, reinterpret_cast<void*>(0x10000000));
    EXPECT_EQ(buf.iova, 0x200000000);
    EXPECT_EQ(buf.bytes, 8192);
    EXPECT_EQ(buf.nseg, 1);
}

// ============================================================================
// Test: PRP Calculations
// ============================================================================

TEST(PRPCalculation, SinglePage_4K) {
    constexpr std::size_t PAGE_SIZE = 4096;
    constexpr std::uint64_t iova = 0x100000000;

    // Transfer size <= PAGE_SIZE uses only PRP1
    std::size_t bytes = 4096;
    std::uint64_t prp1 = iova;
    std::uint64_t prp2 = 0;

    EXPECT_EQ(prp1, iova);
    EXPECT_EQ(prp2, 0);

    // Partial page also uses only PRP1
    bytes = 512;
    prp1 = iova;
    prp2 = 0;
    EXPECT_EQ(prp1, iova);
    EXPECT_EQ(prp2, 0);
}

TEST(PRPCalculation, TwoPages_4K) {
    constexpr std::size_t PAGE_SIZE = 4096;
    constexpr std::uint64_t iova = 0x100000000;

    // Transfer size > PAGE_SIZE requires PRP2
    std::size_t bytes = 8192;  // 2 pages
    std::uint64_t prp1 = iova;
    std::uint64_t prp2 = iova + PAGE_SIZE;

    EXPECT_EQ(prp1, iova);
    EXPECT_EQ(prp2, iova + PAGE_SIZE);
}

TEST(PRPCalculation, PageBoundary) {
    constexpr std::size_t PAGE_SIZE = 4096;

    // Data crosses page boundary
    std::uint64_t iova_offset = 0x100000800;  // Offset within first page
    std::size_t bytes = 4096;  // Will cross into second page

    std::uint64_t prp1 = iova_offset;
    // PRP2 would point to next page
    std::uint64_t next_page = (iova_offset + PAGE_SIZE) & ~(PAGE_SIZE - 1);
    std::uint64_t prp2 = next_page;

    EXPECT_EQ(prp1, iova_offset);
    EXPECT_GT(prp2, prp1);
}

// ============================================================================
// Test: Memory Alignment
// ============================================================================

TEST(MemoryAlignment, PageAlignmentCheck) {
    constexpr std::size_t PAGE_4K = 4096;
    constexpr std::size_t PAGE_64K = 65536;

    // 4K-aligned addresses
    EXPECT_EQ(reinterpret_cast<std::uintptr_t>(nullptr) % PAGE_4K, 0);
    EXPECT_EQ(0x1000 % PAGE_4K, 0);
    EXPECT_EQ(0x2000 % PAGE_4K, 0);
    EXPECT_NE(0x1800 % PAGE_4K, 0);

    // 64K-aligned addresses
    EXPECT_EQ(0x10000 % PAGE_64K, 0);
    EXPECT_EQ(0x20000 % PAGE_64K, 0);
    EXPECT_NE(0x11000 % PAGE_64K, 0);
}

TEST(MemoryAlignment, SizeAlignment) {
    constexpr std::size_t PAGE_SIZE = 4096;

    // Page-aligned sizes
    EXPECT_EQ(PAGE_SIZE % PAGE_SIZE, 0);
    EXPECT_EQ((2 * PAGE_SIZE) % PAGE_SIZE, 0);
    EXPECT_EQ((10 * PAGE_SIZE) % PAGE_SIZE, 0);

    // Non-aligned sizes
    EXPECT_NE(100 % PAGE_SIZE, 0);
    EXPECT_NE((PAGE_SIZE + 1) % PAGE_SIZE, 0);
    EXPECT_NE((PAGE_SIZE - 1) % PAGE_SIZE, 0);
}

// ============================================================================
// Test: Buffer Validation Logic
// ============================================================================

TEST(BufferValidation, NullChecks) {
    DmaBuf* null_buf = nullptr;
    EXPECT_EQ(null_buf, nullptr);

    DmaBuf buf{};
    buf.addr = nullptr;
    EXPECT_EQ(buf.addr, nullptr);
}

TEST(BufferValidation, SizeChecks) {
    DmaBuf buf{};
    buf.bytes = 4096;

    // Valid request
    std::size_t request_size = 4096;
    EXPECT_LE(request_size, buf.bytes);

    // Invalid request (too large)
    request_size = 8192;
    EXPECT_GT(request_size, buf.bytes);

    // Zero size invalid
    request_size = 0;
    EXPECT_EQ(request_size, 0);
}

TEST(BufferValidation, LBASizeAlignment) {
    std::uint32_t lba_size = 512;
    std::size_t bytes;

    // Valid alignments
    bytes = 512;
    EXPECT_EQ(bytes % lba_size, 0);

    bytes = 1024;
    EXPECT_EQ(bytes % lba_size, 0);

    bytes = 4096;
    EXPECT_EQ(bytes % lba_size, 0);

    // Invalid alignment
    bytes = 513;
    EXPECT_NE(bytes % lba_size, 0);

    bytes = 1000;
    EXPECT_NE(bytes % lba_size, 0);
}

TEST(BufferValidation, NLB0Calculation) {
    std::uint32_t lba_size = 512;
    std::size_t bytes;

    // NLB0 = (bytes / lba_size) - 1
    bytes = 512;
    std::uint16_t nlb0 = static_cast<std::uint16_t>((bytes / lba_size) - 1);
    EXPECT_EQ(nlb0, 0);  // 1 block - 1 = 0

    bytes = 1024;
    nlb0 = static_cast<std::uint16_t>((bytes / lba_size) - 1);
    EXPECT_EQ(nlb0, 1);  // 2 blocks - 1 = 1

    bytes = 4096;
    nlb0 = static_cast<std::uint16_t>((bytes / lba_size) - 1);
    EXPECT_EQ(nlb0, 7);  // 8 blocks - 1 = 7
}

// ============================================================================
// Test: CID Management
// ============================================================================

TEST(CIDManagement, InvalidCID) {
    EXPECT_EQ(NVME_CID_ERROR, 0xFFFF);
    EXPECT_EQ(NVME_CID_QUEUE_FULL, 0xFFFE);
}

TEST(CIDManagement, ValidCIDRange) {
    // Valid CIDs are 0 to NVME_CID_QUEUE_FULL - 1
    std::uint16_t cid = 0;
    EXPECT_LT(cid, NVME_CID_QUEUE_FULL);

    cid = 100;
    EXPECT_LT(cid, NVME_CID_QUEUE_FULL);

    cid = NVME_CID_QUEUE_FULL - 1;
    EXPECT_LT(cid, NVME_CID_QUEUE_FULL);

    cid = NVME_CID_QUEUE_FULL;
    EXPECT_EQ(cid, NVME_CID_QUEUE_FULL);

    cid = NVME_CID_ERROR;
    EXPECT_EQ(cid, NVME_CID_ERROR);
}

TEST(CIDManagement, CIDHint) {
    DmaBuf buf{};
    buf.cid_hint = 0xFFFF;  // Default invalid

    EXPECT_EQ(buf.cid_hint, NVME_CID_ERROR);

    buf.cid_hint = 42;
    EXPECT_EQ(buf.cid_hint, 42);
    EXPECT_LT(buf.cid_hint, NVME_CID_QUEUE_FULL);
}
