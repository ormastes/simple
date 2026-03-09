/**
 * @file 53_test_page_size_config_system.cpp
 * @brief System tests for NVMe page size configuration functions
 *
 * Tests the enhanced page size configuration functionality:
 * - nvme_init(): Initialize device without enabling controller
 * - nvme_set_page_size(): Configure page size while controller is disabled
 * - nvme_enable(): Enable controller with configured settings
 * - nvme_available_sizes(): Query all supported page sizes
 * - nvme_get_page_size(): Query current page size
 * - Controller state protection after enablement
 * - Legacy API compatibility (nvme_open)
 *
 * ENHANCED API WORKFLOW: nvme_init() -> nvme_set_page_size() -> nvme_enable()
 * allows full page size configuration before controller enablement.
 *
 * Requirements:
 * - Real NVMe device accessible via VFIO
 * - Environment variables: NVME_BDF, NVME_NSID, NVME_LBA_SIZE, NVME_SLBA
 */

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <set>
#include <vector>

#include <gtest/gtest.h>

// Module 53 APIs
#include "mapper/mapper_host.h"
#include "memory/host_memory_buffer.h"
#include "io/host_io_host_mem.h"

// Test helpers
#include "helper/system_test_config.h"
#include "helper/log_helper.h"

using nvme_test::HostTestConfig;

/**
 * @brief System test fixture for page size configuration
 *
 * Tests page size configuration functionality that must occur before
 * controller enablement. Uses manual device initialization (not SetupHelper)
 * to test the configuration phase.
 */
class PageSizeConfigSystemTest : public ::testing::Test {
protected:
    HostTestConfig config;
    std::string skip_reason_;

    void SetUp() override {
        // Load test configuration from environment
        config.load_from_env(nullptr, false);
        
        if (!config.is_valid()) {
            skip_reason_ = "Missing required environment variables. Set NVME_BDF, NVME_NSID, NVME_LBA_SIZE, NVME_SLBA";
            GTEST_SKIP() << skip_reason_;
        }

        printf("Testing page size configuration on device %s\n", config.bdf);
    }

    void TearDown() override {
        // Cleanup handled by individual tests
    }
};

// ============================================================================
// Test 1: Query Available Page Sizes (before device initialization)
// ============================================================================

TEST_F(PageSizeConfigSystemTest, QueryAvailablePageSizes) {
    // Test with nullptr device (should return safe defaults)
    size_t num_sizes_null = 0;
    size_t* available_null = nvme_available_sizes(nullptr, &num_sizes_null);
    
    if (available_null) {
        EXPECT_GE(num_sizes_null, 1) << "Should return at least one size (4KB default)";
        EXPECT_EQ(available_null[0], 4096) << "First size should be 4KB default";
        free(available_null);
    }

    // Test with uninitialized device - should open device but not enable controller
    NvmeDevice* dev = nvme_open(config.bdf, config.sq_depth, config.cq_depth, config.lba_size);
    ASSERT_NE(dev, nullptr) << "Failed to open NVMe device " << config.bdf;

    // Query available sizes from actual device
    size_t num_sizes = 0;
    size_t* available_sizes = nvme_available_sizes(dev, &num_sizes);
    ASSERT_NE(available_sizes, nullptr) << "nvme_available_sizes() should not return nullptr";
    ASSERT_GT(num_sizes, 0) << "Should return at least one supported page size";

    // Verify all sizes are powers of 2 and >= 4KB
    std::set<size_t> unique_sizes;
    for (size_t i = 0; i < num_sizes; i++) {
        size_t size = available_sizes[i];
        EXPECT_GE(size, 4096) << "Page size " << i << " should be >= 4KB, got " << size;
        EXPECT_EQ(size & (size - 1), 0) << "Page size " << size << " should be power of 2";
        unique_sizes.insert(size);
    }
    
    EXPECT_EQ(unique_sizes.size(), num_sizes) << "Should not have duplicate page sizes";

    // Log discovered sizes
    printf("Device %s supports %zu page sizes:\n", config.bdf, num_sizes);
    for (size_t i = 0; i < num_sizes; i++) {
        printf("  %zuKB (%zu bytes)\n", available_sizes[i] / 1024, available_sizes[i]);
    }

    free(available_sizes);
    nvme_close(dev);
}

// ============================================================================
// Test 2: Verify Controller State Protection (API Limitation Test)
// ============================================================================

TEST_F(PageSizeConfigSystemTest, VerifyControllerStateProtection) {
    // This test verifies controller state protection in both APIs:
    // 1. Legacy API (nvme_open) - automatically enables controller, protection should activate
    // 2. Enhanced API (nvme_init/nvme_enable) - allows configuration before enable
    
    printf("Part A: Legacy API - Controller State Protection\n");
    NvmeDevice* dev = nvme_open(config.bdf, config.sq_depth, config.cq_depth, config.lba_size);
    ASSERT_NE(dev, nullptr) << "Failed to open NVMe device";

    // Get available sizes
    size_t num_sizes = 0;
    size_t* available_sizes = nvme_available_sizes(dev, &num_sizes);
    ASSERT_NE(available_sizes, nullptr);
    ASSERT_GT(num_sizes, 0);

    // Test that setting page size fails when controller is enabled (legacy API)
    for (size_t i = 0; i < std::min((size_t)3, num_sizes); i++) {  // Test first 3 sizes only
        size_t target_size = available_sizes[i];
        
        printf("  Testing protection with %zuKB\n", target_size / 1024);
        
        bool result = nvme_set_page_size(dev, target_size);
        EXPECT_FALSE(result) << "nvme_set_page_size() should fail when controller is enabled (legacy API)";
    }

    printf("✓ Legacy API protection verified - nvme_set_page_size() correctly rejects changes after nvme_open()\n");
    free(available_sizes);
    nvme_close(dev);

    printf("\nPart B: Enhanced API - Successful Configuration\n");
    // Demonstrate that enhanced API allows page size configuration
    NvmeDevice* dev2 = nvme_init(config.bdf, config.lba_size);
    ASSERT_NE(dev2, nullptr) << "Failed to initialize device with enhanced API";

    // Get available sizes again
    size_t num_sizes2 = 0;
    size_t* available_sizes2 = nvme_available_sizes(dev2, &num_sizes2);
    ASSERT_NE(available_sizes2, nullptr);
    
    // Test that configuration succeeds with disabled controller
    if (num_sizes2 > 1) {
        size_t target_size = available_sizes2[1];  // Try second available size
        printf("  Configuring %zuKB with disabled controller\n", target_size / 1024);
        
        bool config_result = nvme_set_page_size(dev2, target_size);
        EXPECT_TRUE(config_result) << "nvme_set_page_size() should succeed with disabled controller";
        
        if (config_result) {
            size_t configured_size = nvme_get_page_size(dev2);
            EXPECT_EQ(configured_size, target_size) << "Page size should be updated";
            printf("✓ Successfully configured %zuKB page size\n", configured_size / 1024);
        }
    } else {
        printf("  Only one page size available, using default\n");
    }

    // Enable controller
    bool enable_result = nvme_enable(dev2, config.sq_depth, config.cq_depth);
    EXPECT_TRUE(enable_result) << "Controller enable should succeed";
    
    if (enable_result) {
        printf("✓ Controller enabled successfully\n");
        
        // Now protection should activate
        if (num_sizes2 > 0) {
            bool protection_result = nvme_set_page_size(dev2, available_sizes2[0]);
            EXPECT_FALSE(protection_result) << "Protection should activate after nvme_enable()";
            printf("✓ Protection activated after controller enable\n");
        }
    }

    free(available_sizes2);
    nvme_close(dev2);
    
    printf("Controller state protection verification complete:\n");
    printf("  - Legacy API (nvme_open): Protection active immediately\n");
    printf("  - Enhanced API (nvme_init): Allows configuration, then protects after nvme_enable()\n");
}

// ============================================================================
// Test 3: Test Invalid Page Size Rejection
// ============================================================================

TEST_F(PageSizeConfigSystemTest, RejectInvalidPageSizes) {
    NvmeDevice* dev = nvme_open(config.bdf, config.sq_depth, config.cq_depth, config.lba_size);
    ASSERT_NE(dev, nullptr);

    // Test invalid sizes that should be rejected
    std::vector<size_t> invalid_sizes = {
        0,          // Zero size
        1024,       // Less than 4KB minimum
        2048,       // Less than 4KB minimum  
        5000,       // Not power of 2
        8192 + 1,   // Not power of 2
        1024 * 1024 * 1024  // Too large (1GB - likely exceeds hardware)
    };

    for (size_t invalid_size : invalid_sizes) {
        printf("Testing invalid page size: %zu bytes\n", invalid_size);
        bool result = nvme_set_page_size(dev, invalid_size);
        EXPECT_FALSE(result) << "Should reject invalid page size " << invalid_size;
    }

    nvme_close(dev);
}

// ============================================================================
// Test 4: Current Page Size Query and Hardware Capabilities
// ============================================================================

TEST_F(PageSizeConfigSystemTest, QueryCurrentPageSizeAndCapabilities) {
    // This test verifies that page size querying works correctly
    // and that hardware capabilities are properly detected
    
    NvmeDevice* dev = nvme_open(config.bdf, config.sq_depth, config.cq_depth, config.lba_size);
    ASSERT_NE(dev, nullptr);

    // Query available sizes
    size_t num_sizes = 0;
    size_t* available_sizes = nvme_available_sizes(dev, &num_sizes);
    ASSERT_NE(available_sizes, nullptr);
    ASSERT_GT(num_sizes, 0);

    // Get current and maximum page sizes
    size_t current_size = nvme_get_page_size(dev);
    size_t max_size = nvme_get_max_page_size(dev);

    // Verify relationships
    EXPECT_GE(current_size, 4096) << "Current page size should be at least 4KB";
    EXPECT_GE(max_size, current_size) << "Max page size should be >= current size";
    EXPECT_EQ(current_size & (current_size - 1), 0) << "Current page size should be power of 2";
    EXPECT_EQ(max_size & (max_size - 1), 0) << "Max page size should be power of 2";

    // Current size should be in available sizes list
    bool current_found = false;
    for (size_t i = 0; i < num_sizes; i++) {
        if (available_sizes[i] == current_size) {
            current_found = true;
            break;
        }
    }
    EXPECT_TRUE(current_found) << "Current page size should be in available sizes list";

    printf("Page size capabilities verified:\n");
    printf("  Current: %zuKB, Maximum: %zuKB, Available count: %zu\n",
           current_size / 1024, max_size / 1024, num_sizes);
    printf("  Note: Current size is determined during device initialization based on hardware capabilities\n");

    free(available_sizes);
    nvme_close(dev);
}

// ============================================================================
// Test 5: Consistency Between Page Size Functions  
// ============================================================================

TEST_F(PageSizeConfigSystemTest, PageSizeFunctionConsistency) {
    NvmeDevice* dev = nvme_open(config.bdf, config.sq_depth, config.cq_depth, config.lba_size);
    ASSERT_NE(dev, nullptr);

    // Get current and maximum page sizes
    size_t current_size = nvme_get_page_size(dev);
    size_t max_size = nvme_get_max_page_size(dev);
    
    // Get available sizes
    size_t num_sizes = 0;
    size_t* available_sizes = nvme_available_sizes(dev, &num_sizes);
    ASSERT_NE(available_sizes, nullptr);

    // Verify consistency rules
    EXPECT_LE(current_size, max_size) 
        << "Current page size should be <= maximum page size";

    // Current size should be in the available sizes list
    bool current_found = false;
    for (size_t i = 0; i < num_sizes; i++) {
        if (available_sizes[i] == current_size) {
            current_found = true;
            break;
        }
    }
    EXPECT_TRUE(current_found) 
        << "Current page size " << current_size << " should be in available sizes list";

    // Maximum size should be in the available sizes list
    bool max_found = false;
    for (size_t i = 0; i < num_sizes; i++) {
        if (available_sizes[i] == max_size) {
            max_found = true;
            break;
        }
    }
    EXPECT_TRUE(max_found) 
        << "Maximum page size " << max_size << " should be in available sizes list";

    printf("Page size consistency check passed:\n");
    printf("  Current: %zuKB, Maximum: %zuKB, Available count: %zu\n",
           current_size / 1024, max_size / 1024, num_sizes);

    free(available_sizes);
    nvme_close(dev);
}

// ============================================================================
// Test 6: Enhanced API - Page Size Configuration with nvme_init/nvme_enable
// ============================================================================

TEST_F(PageSizeConfigSystemTest, EnhancedAPIPageSizeConfiguration) {
    // Test the new enhanced API that allows page size configuration
    // before controller enablement
    
    printf("Testing enhanced API: nvme_init() -> nvme_set_page_size() -> nvme_enable()\n");
    
    // Step 1: Initialize device without enabling controller
    NvmeDevice* dev = nvme_init(config.bdf, config.lba_size);
    ASSERT_NE(dev, nullptr) << "Failed to initialize NVMe device " << config.bdf;
    printf("✓ nvme_init() successful - controller disabled, ready for configuration\n");

    // Step 2: Query available page sizes
    size_t num_sizes = 0;
    size_t* available_sizes = nvme_available_sizes(dev, &num_sizes);
    ASSERT_NE(available_sizes, nullptr) << "Failed to query available page sizes";
    ASSERT_GT(num_sizes, 0) << "Should have at least one supported page size";
    
    printf("Available page sizes: ");
    for (size_t i = 0; i < num_sizes; i++) {
        printf("%zuKB ", available_sizes[i] / 1024);
    }
    printf("\n");

    // Step 3: Try to configure a different page size (if available)
    size_t original_size = nvme_get_page_size(dev);
    printf("Original page size: %zuKB\n", original_size / 1024);
    
    size_t target_size = 0;
    for (size_t i = 0; i < num_sizes; i++) {
        if (available_sizes[i] != original_size && available_sizes[i] >= 8192) {
            target_size = available_sizes[i];
            break;
        }
    }
    
    if (target_size > 0) {
        printf("Attempting to configure %zuKB page size...\n", target_size / 1024);
        bool config_result = nvme_set_page_size(dev, target_size);
        EXPECT_TRUE(config_result) << "nvme_set_page_size() should succeed with disabled controller";
        
        if (config_result) {
            size_t new_size = nvme_get_page_size(dev);
            EXPECT_EQ(new_size, target_size) << "Page size should be updated to " << target_size;
            printf("✓ Page size successfully configured to %zuKB\n", new_size / 1024);
        }
    } else {
        printf("Only one page size supported or no suitable alternative, using original: %zuKB\n", 
               original_size / 1024);
    }

    // Step 4: Enable controller with configured settings
    bool enable_result = nvme_enable(dev, config.sq_depth, config.cq_depth);
    EXPECT_TRUE(enable_result) << "nvme_enable() should succeed";
    printf("✓ Controller enabled, I/O queues created\n");
    
    if (enable_result) {
        // Step 5: Verify page size cannot be changed after enable
        size_t test_size = (target_size > 0) ? original_size : (available_sizes[0] == 4096 ? 8192 : 4096);
        if (test_size <= nvme_get_max_page_size(dev)) {
            printf("Verifying page size protection after enable...\n");
            bool protection_result = nvme_set_page_size(dev, test_size);
            EXPECT_FALSE(protection_result) << "nvme_set_page_size() should fail after controller enable";
            printf("✓ Controller state protection verified\n");
        }
        
        // Step 6: Verify device is ready for I/O operations
        Queue* iosq = nvme_get_iosq(dev);
        Queue* iocq = nvme_get_iocq(dev);
        EXPECT_NE(iosq, nullptr) << "I/O submission queue should be available";
        EXPECT_NE(iocq, nullptr) << "I/O completion queue should be available";
        printf("✓ I/O queues ready for operations\n");
    }

    free(available_sizes);
    nvme_close(dev);
    
    printf("Enhanced API test completed successfully!\n");
    printf("Summary: nvme_init() -> configure page size -> nvme_enable() -> protected from changes\n");
}

// ============================================================================
// Test 7: Multiple Device Initialization Cycles
// ============================================================================

TEST_F(PageSizeConfigSystemTest, MultipleInitializationCycles) {
    // Test that page size configuration works correctly across multiple
    // device open/close cycles
    
    std::vector<size_t> test_sizes = {4096, 8192, 16384}; // Common sizes
    
    for (size_t target_size : test_sizes) {
        printf("Testing initialization cycle with %zuKB page size\n", target_size / 1024);
        
        // Open device
        NvmeDevice* dev = nvme_open(config.bdf, config.sq_depth, config.cq_depth, config.lba_size);
        ASSERT_NE(dev, nullptr) << "Failed to open device for size " << target_size;

        // Check if this size is supported
        size_t num_sizes = 0;
        size_t* available_sizes = nvme_available_sizes(dev, &num_sizes);
        ASSERT_NE(available_sizes, nullptr);
        
        bool size_supported = false;
        for (size_t i = 0; i < num_sizes; i++) {
            if (available_sizes[i] == target_size) {
                size_supported = true;
                break;
            }
        }
        
        if (size_supported) {
            // Configure the size
            bool result = nvme_set_page_size(dev, target_size);
            EXPECT_TRUE(result) << "Failed to set page size " << target_size;
            
            if (result) {
                size_t configured = nvme_get_page_size(dev);
                EXPECT_EQ(configured, target_size) 
                    << "Page size mismatch after configuration";
            }
        } else {
            printf("  Size %zuKB not supported by device, skipping\n", target_size / 1024);
        }

        free(available_sizes);
        nvme_close(dev);
    }

    printf("Multiple initialization cycles completed successfully\n");
}