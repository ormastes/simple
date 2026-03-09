/**
 * @file test_buffer_factory_c_interface.cpp
 * @brief Unit tests for BufferFactory C interface
 *
 * Tests the C interface for the unified buffer factory, demonstrating
 * usage from C code and validating the C API wrapper functions.
 *
 * @author Converted from examples
 * @date 2025-11-22
 */

#include <gtest/gtest.h>
#include "memory/buffer_factory.h"
#include "memory/memory_pool.h"
#include <cstring>

class BufferFactoryCInterfaceTest : public ::testing::Test {
protected:
    void SetUp() override {
        c_factory_ = buffer_factory_create();
        ASSERT_NE(c_factory_, nullptr) << "Failed to create C factory";
    }

    void TearDown() override {
        if (c_factory_) {
            buffer_factory_destroy(c_factory_);
        }
    }

    BufferFactoryHandle* c_factory_;
    static constexpr std::size_t kTestBytes = 4096;
};

// ============================================================================
// Test: C Interface Basic Operations
// ============================================================================

TEST_F(BufferFactoryCInterfaceTest, CreateDestroy) {
    // Factory should be created successfully in SetUp
    EXPECT_NE(c_factory_, nullptr);
    
    // Test creating another factory
    BufferFactoryHandle* factory2 = buffer_factory_create();
    ASSERT_NE(factory2, nullptr);
    
    buffer_factory_destroy(factory2);
}

TEST_F(BufferFactoryCInterfaceTest, HostMemoryAllocation) {
    void* c_ptr = buffer_factory_alloc(c_factory_, MemoryType::HOST, kTestBytes);
    ASSERT_NE(c_ptr, nullptr) << "C API allocation failed";

    // Test memory accessibility
    std::memset(c_ptr, 0xCD, kTestBytes);
    EXPECT_EQ(static_cast<unsigned char*>(c_ptr)[0], 0xCD);
    EXPECT_EQ(static_cast<unsigned char*>(c_ptr)[kTestBytes - 1], 0xCD);

    buffer_factory_dealloc(c_factory_, MemoryType::HOST, c_ptr, kTestBytes);
}

TEST_F(BufferFactoryCInterfaceTest, PinnedHostMemoryAllocation) {
    void* pinned_ptr = buffer_factory_alloc(c_factory_, MemoryType::PINNED_HOST, kTestBytes);
    
    if (pinned_ptr) {
        // Test memory is accessible if allocation succeeded
        std::memset(pinned_ptr, 0xEF, kTestBytes);
        EXPECT_EQ(static_cast<unsigned char*>(pinned_ptr)[0], 0xEF);
        EXPECT_EQ(static_cast<unsigned char*>(pinned_ptr)[kTestBytes - 1], 0xEF);
        
        buffer_factory_dealloc(c_factory_, MemoryType::PINNED_HOST, pinned_ptr, kTestBytes);
    } else {
        GTEST_SKIP() << "PINNED_HOST allocation not available in this build";
    }
}

TEST_F(BufferFactoryCInterfaceTest, NullFactoryHandling) {
    // Test that null factory is handled gracefully
    void* ptr = buffer_factory_alloc(nullptr, MemoryType::HOST, kTestBytes);
    EXPECT_EQ(ptr, nullptr);
    
    // Should not crash
    buffer_factory_dealloc(nullptr, MemoryType::HOST, nullptr, kTestBytes);
}

TEST_F(BufferFactoryCInterfaceTest, ZeroSizeAllocation) {
    void* ptr = buffer_factory_alloc(c_factory_, MemoryType::HOST, 0);
    // Implementation may return nullptr for zero size - both behaviors are valid
    if (ptr) {
        buffer_factory_dealloc(c_factory_, MemoryType::HOST, ptr, 0);
    }
}

// ============================================================================
// Test: Pool Creation (C Interface)
// ============================================================================

TEST_F(BufferFactoryCInterfaceTest, HostPoolCreation) {
    constexpr size_t buf_size = 4096;
    constexpr uint16_t count = 32;
    
    HostPool* pool = buffer_factory_create_pool(c_factory_, MemoryType::HOST, buf_size, count);
    
    if (pool) {
        // Verify pool properties if creation succeeded
        EXPECT_EQ(pool->buf_size, buf_size);
        EXPECT_EQ(pool->cap, count);
        EXPECT_EQ(pool->in_use, 0);
        
        buffer_factory_destroy_pool(c_factory_, MemoryType::HOST, pool);
    } else {
        GTEST_SKIP() << "Pool creation not supported for HOST memory type";
    }
}

TEST_F(BufferFactoryCInterfaceTest, NullPoolHandling) {
    // Test that null pool is handled gracefully
    buffer_factory_destroy_pool(c_factory_, MemoryType::HOST, nullptr);
    buffer_factory_destroy_pool(nullptr, MemoryType::HOST, nullptr);
}

// ============================================================================
// Test: Support Detection (C Interface)
// ============================================================================

TEST_F(BufferFactoryCInterfaceTest, SupportDetection) {
    // HOST should always be supported
    int host_supported = buffer_factory_is_supported(c_factory_, MemoryType::HOST);
    EXPECT_EQ(host_supported, 1);
    
    // Check other types
    int pinned_host_supported = buffer_factory_is_supported(c_factory_, MemoryType::PINNED_HOST);
    int device_supported = buffer_factory_is_supported(c_factory_, MemoryType::PINNED_DEVICE);
    
    // Log support status
    std::cout << "C API Support status:\n";
    std::cout << "  HOST: " << (host_supported ? "Supported" : "Not supported") << "\n";
    std::cout << "  PINNED_HOST: " << (pinned_host_supported ? "Supported" : "Not supported") << "\n";
    std::cout << "  PINNED_DEVICE: " << (device_supported ? "Supported" : "Not supported") << "\n";
}

TEST_F(BufferFactoryCInterfaceTest, NullFactorySupport) {
    // Test null factory handling
    int result = buffer_factory_is_supported(nullptr, MemoryType::HOST);
    EXPECT_EQ(result, 0);
}

TEST_F(BufferFactoryCInterfaceTest, RecommendedKind) {
    MemoryType host_preferred = buffer_factory_get_recommended_kind(c_factory_, 0);
    MemoryType gpu_preferred = buffer_factory_get_recommended_kind(c_factory_, 1);
    
    // Should return valid memory types
    EXPECT_TRUE(host_preferred == MemoryType::HOST || 
                host_preferred == MemoryType::PINNED_HOST ||
                host_preferred == MemoryType::PINNED_DEVICE);
                
    EXPECT_TRUE(gpu_preferred == MemoryType::HOST || 
                gpu_preferred == MemoryType::PINNED_HOST ||
                gpu_preferred == MemoryType::PINNED_DEVICE);
                
    std::cout << "C API Recommended types:\n";
    std::cout << "  Host-preferred: " << static_cast<int>(host_preferred) << "\n";
    std::cout << "  GPU-preferred: " << static_cast<int>(gpu_preferred) << "\n";
}

// ============================================================================
// Test: Global Factory (C Interface)
// ============================================================================

TEST(BufferFactoryGlobalCTest, GlobalFactoryAccess) {
    BufferFactoryHandle* global_factory = get_global_buffer_factory();
    ASSERT_NE(global_factory, nullptr);
    
    // Test allocation with global factory
    void* buf = buffer_factory_alloc(global_factory, MemoryType::HOST, 4096);
    ASSERT_NE(buf, nullptr);
    
    // Verify memory works
    std::memset(buf, 0x99, 4096);
    EXPECT_EQ(static_cast<unsigned char*>(buf)[0], 0x99);
    
    buffer_factory_dealloc(global_factory, MemoryType::HOST, buf, 4096);
}

TEST(BufferFactoryGlobalCTest, MultipleCalls) {
    BufferFactoryHandle* global1 = get_global_buffer_factory();
    BufferFactoryHandle* global2 = get_global_buffer_factory();
    
    // Should return same instance
    EXPECT_EQ(global1, global2);
}
