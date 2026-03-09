#include <gtest/gtest.h>
#include <gmock/gmock.h>
#include <cuda_runtime.h>
#include <iostream>
#include <vector>
#include "cuda_utils.h"


// Main function with device checking and initialization
int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    ::testing::InitGoogleMock(&argc, argv);

    // Check if we're only listing tests (don't need GPU for that)
    bool listingTests = false;
    for (int i = 1; i < argc; i++) {
        std::string arg(argv[i]);
        if (arg == "--gtest_list_tests" || arg == "--help" || arg == "-h") {
            listingTests = true;
            break;
        }
    }

    // Only check for CUDA device when actually running tests
    if (!listingTests) {
        int deviceCount = 0;
        cudaError_t err = cudaGetDeviceCount(&deviceCount);

        if (err != cudaSuccess) {
            std::cerr << "Failed to get CUDA device count: " << cudaGetErrorString(err) << std::endl;
            return 1;
        }

        if (deviceCount == 0) {
            std::cerr << "No CUDA devices found!" << std::endl;
            return 1;
        }

        // Print device info
        std::cout << "\n=== CUDA Device Information ===" << std::endl;
        print_device_info(0);
        std::cout << "================================\n" << std::endl;
    }

    // Run all tests
    return RUN_ALL_TESTS();
}