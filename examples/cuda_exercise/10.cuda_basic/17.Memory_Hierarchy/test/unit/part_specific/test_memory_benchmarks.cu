// test_memory_benchmarks.cu - GTest-based tests for memory hierarchy benchmarks
#include <gtest/gtest.h>
#include "gpu_gtest.h"

#define BUILDING_LIB
#include "part_specific/vector_add_memory.cu"
#include "kernels/matrix_multiply.cu"
#include "part_specific/memory_benchmarks.cu"

// Test fixture for memory benchmarks
class MemoryBenchmarkTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
        // Print device info once for all tests
        static bool printed = false;
        if (!printed) {
            print_device_info();
            printed = true;
        }
    }
};

// Test global memory benchmark
TEST_F(MemoryBenchmarkTest, GlobalMemoryBenchmark) {
    std::cout << "\n=== Global Memory Vector Add Benchmark ===\n";
    MemoryBenchmark bench;
    ASSERT_NO_THROW(bench.benchmark_global_memory());
}

// Test shared memory benchmark
TEST_F(MemoryBenchmarkTest, SharedMemoryBenchmark) {
    std::cout << "\n=== Shared Memory Vector Add Benchmark ===\n";
    MemoryBenchmark bench;
    ASSERT_NO_THROW(bench.benchmark_shared_memory());
}

// Test memory coalescing comparison
TEST_F(MemoryBenchmarkTest, CoalescingBenchmark) {
    std::cout << "\n=== Memory Coalescing Benchmark ===\n";
    MemoryBenchmark bench;
    ASSERT_NO_THROW(bench.benchmark_coalescing());
}

// Test bank conflict analysis
TEST_F(MemoryBenchmarkTest, BankConflictBenchmark) {
    std::cout << "\n=== Bank Conflict Analysis Benchmark ===\n";
    MemoryBenchmark bench;
    ASSERT_NO_THROW(bench.benchmark_bank_conflicts());
}

// Test matrix multiplication benchmarks
TEST_F(MemoryBenchmarkTest, MatrixMultiplicationBenchmark) {
    std::cout << "\n=== Matrix Multiplication Memory Optimizations ===\n";
    MatrixBenchmark bench;
    ASSERT_NO_THROW(bench.benchmark_all());
}
