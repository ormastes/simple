/**
 * @file test_buffer_factory.cpp
 * @brief Unit tests for BufferFactory C++ API
 *
 * Tests the unified BufferFactory interface for memory allocation and management.
 * These tests validate both the C++ interface and basic memory operations.
 *
 * @author Converted from examples
 * @date 2025-11-22
 */

#include <gtest/gtest.h>
#include "memory/buffer_factory.h"
#include <cstring>
#include <memory>

class BufferFactoryTest : public ::testing::Test {
protected:
    void SetUp() override {
        factory_ = std::make_unique<BufferFactory>();
    }

    void TearDown() override {
        factory_.reset();
    }

    std::unique_ptr<BufferFactory> factory_;
    static constexpr std::size_t kTestBytes = 4096;
};

// ============================================================================
// Test: BufferFactory C++ API Basic Operations
// ============================================================================

TEST_F(BufferFactoryTest, HostMemoryAllocation) {
    void* host_buf = factory_->alloc(MemoryType::HOST, kTestBytes);
    ASSERT_NE(host_buf, nullptr) << "Failed to allocate host memory";

    // Test memory is accessible
    std::memset(host_buf, 0xAB, kTestBytes);
    EXPECT_EQ(static_cast<unsigned char*>(host_buf)[0], 0xAB);
    EXPECT_EQ(static_cast<unsigned char*>(host_buf)[kTestBytes - 1], 0xAB);

    factory_->dealloc(MemoryType::HOST, host_buf, kTestBytes);
}

TEST_F(BufferFactoryTest, PinnedHostMemoryAllocation) {
    void* pinned_buf = factory_->alloc(MemoryType::PINNED_HOST, kTestBytes);
    
    if (pinned_buf) {
        // Test memory is accessible if allocation succeeded
        std::memset(pinned_buf, 0xCD, kTestBytes);
        EXPECT_EQ(static_cast<unsigned char*>(pinned_buf)[0], 0xCD);
        EXPECT_EQ(static_cast<unsigned char*>(pinned_buf)[kTestBytes - 1], 0xCD);
        
        factory_->dealloc(MemoryType::PINNED_HOST, pinned_buf, kTestBytes);
    } else {
        // PINNED_HOST might not be available in all builds - this is acceptable
        GTEST_SKIP() << "PINNED_HOST allocation not available in this build";
    }
}

TEST_F(BufferFactoryTest, NullAllocation) {
    // Test zero-size allocation
    void* null_buf = factory_->alloc(MemoryType::HOST, 0);
    // Implementation may return nullptr for zero size - both behaviors are valid
    if (null_buf) {
        factory_->dealloc(MemoryType::HOST, null_buf, 0);
    }
}

TEST_F(BufferFactoryTest, MultipleAllocations) {
    std::vector<void*> buffers;
    const size_t num_buffers = 10;
    
    // Allocate multiple buffers
    for (size_t i = 0; i < num_buffers; ++i) {
        void* buf = factory_->alloc(MemoryType::HOST, kTestBytes);
        ASSERT_NE(buf, nullptr) << "Failed allocation " << i;
        buffers.push_back(buf);
        
        // Write unique pattern to each buffer
        std::memset(buf, static_cast<int>(i + 1), kTestBytes);
    }
    
    // Verify each buffer has correct pattern
    for (size_t i = 0; i < num_buffers; ++i) {
        EXPECT_EQ(static_cast<unsigned char*>(buffers[i])[0], 
                  static_cast<unsigned char>(i + 1));
        EXPECT_EQ(static_cast<unsigned char*>(buffers[i])[kTestBytes - 1], 
                  static_cast<unsigned char>(i + 1));
    }
    
    // Deallocate all buffers
    for (size_t i = 0; i < num_buffers; ++i) {
        factory_->dealloc(MemoryType::HOST, buffers[i], kTestBytes);
    }
}

// ============================================================================
// Test: BufferFactory Support Detection
// ============================================================================

TEST_F(BufferFactoryTest, SupportDetection) {
    // HOST should always be supported
    EXPECT_TRUE(factory_->is_supported(MemoryType::HOST));
    
    // Check other types (may or may not be supported)
    bool pinned_host_supported = factory_->is_supported(MemoryType::PINNED_HOST);
    bool device_supported = factory_->is_supported(MemoryType::PINNED_DEVICE);
    
    // At least HOST should be supported
    EXPECT_TRUE(factory_->is_supported(MemoryType::HOST));
    
    // Log support status for debugging
    EXPECT_NO_FATAL_FAILURE({
        std::cout << "Support status:\n";
        std::cout << "  HOST: " << (factory_->is_supported(MemoryType::HOST) ? "Yes" : "No") << "\n";
        std::cout << "  PINNED_HOST: " << (pinned_host_supported ? "Yes" : "No") << "\n";
        std::cout << "  PINNED_DEVICE: " << (device_supported ? "Yes" : "No") << "\n";
    });
}

TEST_F(BufferFactoryTest, RecommendedKind) {
    // Get recommendations for different preferences
    MemoryType host_preferred = factory_->get_recommended_kind(false);
    MemoryType gpu_preferred = factory_->get_recommended_kind(true);
    
    // Should return valid memory types
    EXPECT_TRUE(host_preferred == MemoryType::HOST || 
                host_preferred == MemoryType::PINNED_HOST ||
                host_preferred == MemoryType::PINNED_DEVICE);
                
    EXPECT_TRUE(gpu_preferred == MemoryType::HOST || 
                gpu_preferred == MemoryType::PINNED_HOST ||
                gpu_preferred == MemoryType::PINNED_DEVICE);
    
    std::cout << "Recommended types:\n";
    std::cout << "  Host-preferred: " << static_cast<int>(host_preferred) << "\n";
    std::cout << "  GPU-preferred: " << static_cast<int>(gpu_preferred) << "\n";
}

// ============================================================================
// Test: Global Singleton
// ============================================================================

TEST(BufferFactoryGlobalTest, GlobalSingleton) {
    BufferFactory& singleton = get_buffer_factory();
    
    // Test basic allocation with singleton
    void* singleton_buf = singleton.alloc(MemoryType::HOST, 4096);
    ASSERT_NE(singleton_buf, nullptr);
    
    // Verify memory works
    std::memset(singleton_buf, 0x42, 4096);
    EXPECT_EQ(static_cast<unsigned char*>(singleton_buf)[0], 0x42);
    
    singleton.dealloc(MemoryType::HOST, singleton_buf, 4096);
}

TEST(BufferFactoryGlobalTest, MultipleSingletonAccess) {
    BufferFactory& singleton1 = get_buffer_factory();
    BufferFactory& singleton2 = get_buffer_factory();
    
    // Should be the same instance
    EXPECT_EQ(&singleton1, &singleton2);
}