/**
 * @file test_doorbell_strategies.cpp
 * @brief Unit tests for NVMe doorbell strategies (no hardware required)
 *
 * Tests doorbell strategy classes:
 * - MmioDoorbell: MMIO register writes
 * - ShadowDoorbell: DBC shadow buffer writes
 *
 * @author Yoon, Jonghyun
 * @date 2025-11-01
 */

#include <gtest/gtest.h>
#include <cstdint>
#include <cstring>

#include "doorbell/nvme_doorbell.h"    // For DoorbellStrategy, MmioDoorbell, ShadowDoorbell

// ============================================================================
// Test: DoorbellStrategy CRTP Trait
// ============================================================================

TEST(DoorbellStrategy, DISABLED_TraitDetectsMmioDoorbell) {
    // MmioDoorbell class removed - GPUs cannot access MMIO registers
    GTEST_SKIP() << "MmioDoorbell class removed - use ShadowDoorbell instead";
}

TEST(DoorbellStrategy, TraitDetectsShadowDoorbell) {
    EXPECT_TRUE(is_doorbell_strategy_v<ShadowDoorbell>);
}

// ============================================================================
// Test: MmioDoorbell
// ============================================================================

class MmioDoorbellTest : public ::testing::Test {
protected:
    volatile std::uint32_t sq_reg;
    volatile std::uint32_t cq_reg;

    void SetUp() override {
        sq_reg = 0xDEADBEEF;  // Initial garbage value
        cq_reg = 0xCAFEBABE;
    }
};

TEST_F(MmioDoorbellTest, DISABLED_ConstructorStoresPointers) {
    GTEST_SKIP() << "MmioDoorbell class removed - use ShadowDoorbell instead";
}

TEST_F(MmioDoorbellTest, DISABLED_RingSqDoorbellWritesRegister) {
    GTEST_SKIP() << "MmioDoorbell class removed - use ShadowDoorbell instead";
}

TEST_F(MmioDoorbellTest, DISABLED_RingCqDoorbellWritesRegister) {
    GTEST_SKIP() << "MmioDoorbell class removed - use ShadowDoorbell instead";
}

TEST_F(MmioDoorbellTest, DISABLED_MultipleRingsUpdateRegister) {
    GTEST_SKIP() << "MmioDoorbell class removed - use ShadowDoorbell instead";
}

TEST_F(MmioDoorbellTest, DISABLED_ReadDoorbellReturnsCurrentValue) {
    GTEST_SKIP() << "MmioDoorbell class removed - use ShadowDoorbell instead";
}

TEST_F(MmioDoorbellTest, DISABLED_WrapAroundValues) {
    GTEST_SKIP() << "MmioDoorbell class removed - use ShadowDoorbell instead";
}

// ============================================================================
// Test: ShadowDoorbell
// ============================================================================

class ShadowDoorbellTest : public ::testing::Test {
protected:
    static constexpr std::size_t NUM_QUEUES = 8;
    volatile std::uint32_t shadow_buffer[NUM_QUEUES * 2];

    void SetUp() override {
        // Initialize with garbage values
        for (std::size_t i = 0; i < NUM_QUEUES * 2; ++i) {
            shadow_buffer[i] = 0xDEAD0000 | i;
        }
    }
};

TEST_F(ShadowDoorbellTest, ConstructorStoresBaseAndQid) {
    ShadowDoorbell doorbell(shadow_buffer, 2);

    EXPECT_EQ(doorbell.shadow_db_ptr(), shadow_buffer);
    EXPECT_EQ(doorbell.queue_id(), 2);
}

TEST_F(ShadowDoorbellTest, RingSqDoorbellWritesCorrectIndex) {
    ShadowDoorbell doorbell(shadow_buffer, 3);  // QID 3

    doorbell.ring_sq_doorbell(42);

    // SQ index = 2 * qid = 6
    EXPECT_EQ(shadow_buffer[6], 42);

    // Other entries unchanged
    EXPECT_EQ(shadow_buffer[5], 0xDEAD0005);
    EXPECT_EQ(shadow_buffer[7], 0xDEAD0007);
}

TEST_F(ShadowDoorbellTest, RingCqDoorbellWritesCorrectIndex) {
    ShadowDoorbell doorbell(shadow_buffer, 3);  // QID 3

    doorbell.ring_cq_doorbell(99);

    // CQ index = 2 * qid + 1 = 7
    EXPECT_EQ(shadow_buffer[7], 99);

    // Other entries unchanged
    EXPECT_EQ(shadow_buffer[6], 0xDEAD0006);
    EXPECT_EQ(shadow_buffer[8], 0xDEAD0008);
}

TEST_F(ShadowDoorbellTest, MultipleQueuesIndependent) {
    ShadowDoorbell doorbell1(shadow_buffer, 0);  // QID 0
    ShadowDoorbell doorbell2(shadow_buffer, 1);  // QID 1
    ShadowDoorbell doorbell3(shadow_buffer, 2);  // QID 2

    doorbell1.ring_sq_doorbell(10);  // shadow_buffer[0]
    doorbell1.ring_cq_doorbell(11);  // shadow_buffer[1]

    doorbell2.ring_sq_doorbell(20);  // shadow_buffer[2]
    doorbell2.ring_cq_doorbell(21);  // shadow_buffer[3]

    doorbell3.ring_sq_doorbell(30);  // shadow_buffer[4]
    doorbell3.ring_cq_doorbell(31);  // shadow_buffer[5]

    EXPECT_EQ(shadow_buffer[0], 10);
    EXPECT_EQ(shadow_buffer[1], 11);
    EXPECT_EQ(shadow_buffer[2], 20);
    EXPECT_EQ(shadow_buffer[3], 21);
    EXPECT_EQ(shadow_buffer[4], 30);
    EXPECT_EQ(shadow_buffer[5], 31);
}

TEST_F(ShadowDoorbellTest, ReadDoorbellReturnsCurrentValue) {
    ShadowDoorbell doorbell(shadow_buffer, 4);

    doorbell.ring_sq_doorbell(123);
    EXPECT_EQ(doorbell.read_sq_doorbell(), 123);

    doorbell.ring_cq_doorbell(456);
    EXPECT_EQ(doorbell.read_cq_doorbell(), 456);
}

TEST_F(ShadowDoorbellTest, QueueIdZeroCorrectIndexing) {
    // Admin queue (QID 0) uses indices 0 and 1
    ShadowDoorbell doorbell(shadow_buffer, 0);

    doorbell.ring_sq_doorbell(5);
    doorbell.ring_cq_doorbell(6);

    EXPECT_EQ(shadow_buffer[0], 5);  // 2 * 0 = 0
    EXPECT_EQ(shadow_buffer[1], 6);  // 2 * 0 + 1 = 1
}

TEST_F(ShadowDoorbellTest, HighQueueIdCorrectIndexing) {
    // High queue ID (e.g., QID 7)
    ShadowDoorbell doorbell(shadow_buffer, 7);

    doorbell.ring_sq_doorbell(77);
    doorbell.ring_cq_doorbell(78);

    EXPECT_EQ(shadow_buffer[14], 77);  // 2 * 7 = 14
    EXPECT_EQ(shadow_buffer[15], 78);  // 2 * 7 + 1 = 15
}

TEST_F(ShadowDoorbellTest, PointerAccessors) {
    ShadowDoorbell doorbell(shadow_buffer, 5);

    // Verify direct pointer accessors
    EXPECT_EQ(doorbell.sq_doorbell_ptr(), &shadow_buffer[10]);  // 2 * 5
    EXPECT_EQ(doorbell.cq_doorbell_ptr(), &shadow_buffer[11]);  // 2 * 5 + 1
}

TEST_F(ShadowDoorbellTest, WrapAroundValues) {
    ShadowDoorbell doorbell(shadow_buffer, 1);

    // Test 16-bit wrap (queue depth wraparound)
    doorbell.ring_sq_doorbell(65535);
    EXPECT_EQ(shadow_buffer[2], 65535);

    doorbell.ring_sq_doorbell(0);
    EXPECT_EQ(shadow_buffer[2], 0);

    doorbell.ring_sq_doorbell(1);
    EXPECT_EQ(shadow_buffer[2], 1);
}

// ============================================================================
// Test: CRTP Compile-Time Dispatch
// ============================================================================

TEST(CRTPDispatch, DISABLED_MmioDoorbellDispatch) {
    GTEST_SKIP() << "MmioDoorbell class removed - use ShadowDoorbell instead";
}

TEST(CRTPDispatch, ShadowDoorbellDispatch) {
    volatile std::uint32_t shadow_buffer[4] = {0, 0, 0, 0};

    ShadowDoorbell doorbell(shadow_buffer, 1);

    // Call through base class interface (should resolve to ShadowDoorbell::ring_cq_doorbell_impl)
    DoorbellStrategy<ShadowDoorbell>& base = doorbell;
    base.ring_cq_doorbell(77);

    EXPECT_EQ(shadow_buffer[3], 77);  // 2 * 1 + 1 = 3
}

// ============================================================================
// Test: Doorbell Strategy Polymorphism
// ============================================================================

// Template function that works with any doorbell strategy
template<typename DoorbellT>
void generic_ring_doorbells(DoorbellT& doorbell) {
    doorbell.ring_sq_doorbell(123);
    doorbell.ring_cq_doorbell(456);
}

TEST(PolymorphicUsage, DISABLED_MmioDoorbellGeneric) {
    GTEST_SKIP() << "MmioDoorbell class removed - use ShadowDoorbell instead";
}

TEST(PolymorphicUsage, ShadowDoorbellGeneric) {
    volatile std::uint32_t shadow_buffer[4] = {0, 0, 0, 0};

    ShadowDoorbell doorbell(shadow_buffer, 0);
    generic_ring_doorbells(doorbell);

    EXPECT_EQ(shadow_buffer[0], 123);  // SQ at 2*0 = 0
    EXPECT_EQ(shadow_buffer[1], 456);  // CQ at 2*0+1 = 1
}
