/**
 * @file test_posix_io.cu
 * @brief Unit tests for POSIX I/O implementations
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include <fcntl.h>
#include <unistd.h>
#include <cstdio>
#include <cstring>
#include <vector>

/**
 * Test fixture for I/O tests
 */
class IOTest : public ::testing::Test {
protected:
    std::string test_file;
    std::vector<char> test_data;

    void SetUp() override {
        // Create temporary test file
        test_file = "/tmp/nvme_io_test_XXXXXX";
        int fd = mkstemp(&test_file[0]);
        ASSERT_GE(fd, 0) << "Failed to create temp file";

        // Write test data
        const size_t size = 1024 * 1024;  // 1 MB
        test_data.resize(size);
        for (size_t i = 0; i < size; i++) {
            test_data[i] = static_cast<char>(i % 256);
        }

        ssize_t written = write(fd, test_data.data(), size);
        ASSERT_EQ(written, size) << "Failed to write test data";

        close(fd);
    }

    void TearDown() override {
        // Clean up test file
        unlink(test_file.c_str());
    }
};

/**
 * Test basic file read
 */
TEST_F(IOTest, BasicRead) {
    int fd = open(test_file.c_str(), O_RDONLY);
    ASSERT_GE(fd, 0) << "Failed to open test file";

    std::vector<char> buffer(test_data.size());
    ssize_t n = read(fd, buffer.data(), buffer.size());

    EXPECT_EQ(n, test_data.size()) << "Read size mismatch";
    EXPECT_EQ(buffer, test_data) << "Data mismatch";

    close(fd);
}

/**
 * Test alignment check for O_DIRECT
 */
TEST_F(IOTest, AlignmentCheck) {
    const size_t sector_size = 4096;

    // Aligned pointer
    void* aligned_ptr;
    ASSERT_EQ(posix_memalign(&aligned_ptr, sector_size, sector_size), 0);

    uintptr_t addr = reinterpret_cast<uintptr_t>(aligned_ptr);
    EXPECT_EQ(addr % sector_size, 0) << "Pointer not aligned";

    free(aligned_ptr);

    // Unaligned pointer
    void* unaligned_ptr = malloc(sector_size);
    addr = reinterpret_cast<uintptr_t>(unaligned_ptr);
    EXPECT_NE(addr % sector_size, 0) << "Regular malloc should not be aligned";

    free(unaligned_ptr);
}

/**
 * Test O_DIRECT flag behavior
 */
TEST_F(IOTest, DirectIOFlag) {
    // Create aligned test file (O_DIRECT requires aligned sizes)
    const size_t sector_size = 4096;
    const size_t aligned_size = (test_data.size() + sector_size - 1) & ~(sector_size - 1);

    std::string direct_file = "/tmp/nvme_direct_test_XXXXXX";
    int fd = mkstemp(&direct_file[0]);
    ASSERT_GE(fd, 0);

    // Write aligned data
    std::vector<char> aligned_data(aligned_size);
    std::copy(test_data.begin(), test_data.end(), aligned_data.begin());

    ssize_t written = write(fd, aligned_data.data(), aligned_size);
    ASSERT_EQ(written, aligned_size);
    close(fd);

    // Try to open with O_DIRECT (may fail on some filesystems)
    fd = open(direct_file.c_str(), O_RDONLY | O_DIRECT);
    if (fd >= 0) {
        // Allocate aligned buffer
        void* buffer;
        ASSERT_EQ(posix_memalign(&buffer, sector_size, aligned_size), 0);

        ssize_t n = read(fd, buffer, aligned_size);
        EXPECT_EQ(n, aligned_size) << "O_DIRECT read size mismatch";

        free(buffer);
        close(fd);
    } else {
        // O_DIRECT not supported on this filesystem
        GTEST_SKIP() << "O_DIRECT not supported on test filesystem";
    }

    unlink(direct_file.c_str());
}

/**
 * Test sequential read performance
 */
TEST_F(IOTest, SequentialReadPerformance) {
    int fd = open(test_file.c_str(), O_RDONLY);
    ASSERT_GE(fd, 0);

    std::vector<char> buffer(test_data.size());

    auto start = std::chrono::high_resolution_clock::now();
    ssize_t n = read(fd, buffer.data(), buffer.size());
    auto end = std::chrono::high_resolution_clock::now();

    ASSERT_EQ(n, test_data.size());

    std::chrono::duration<double, std::micro> duration = end - start;
    double throughput_mbs = (test_data.size() / (duration.count() / 1e6)) / (1024 * 1024);

    // Sanity check: should be at least 100 MB/s on any modern system
    EXPECT_GT(throughput_mbs, 100.0) << "Throughput too low: " << throughput_mbs << " MB/s";

    printf("Sequential read throughput: %.2f MB/s\n", throughput_mbs);

    close(fd);
}

/**
 * Test page cache effect
 */
TEST_F(IOTest, PageCacheEffect) {
    std::vector<char> buffer(test_data.size());

    // First read (cold cache)
    auto start1 = std::chrono::high_resolution_clock::now();
    int fd1 = open(test_file.c_str(), O_RDONLY);
    read(fd1, buffer.data(), buffer.size());
    close(fd1);
    auto end1 = std::chrono::high_resolution_clock::now();
    double time1 = std::chrono::duration<double, std::micro>(end1 - start1).count();

    // Second read (warm cache)
    auto start2 = std::chrono::high_resolution_clock::now();
    int fd2 = open(test_file.c_str(), O_RDONLY);
    read(fd2, buffer.data(), buffer.size());
    close(fd2);
    auto end2 = std::chrono::high_resolution_clock::now();
    double time2 = std::chrono::duration<double, std::micro>(end2 - start2).count();

    // Warm cache should be faster (page cache effect)
    EXPECT_LT(time2, time1) << "Warm cache not faster than cold cache";

    double speedup = time1 / time2;
    printf("Cache speedup: %.2fx (cold: %.2f μs, warm: %.2f μs)\n",
           speedup, time1, time2);
}
