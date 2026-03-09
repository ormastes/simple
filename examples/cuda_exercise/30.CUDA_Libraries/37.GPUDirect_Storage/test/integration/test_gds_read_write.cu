#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cufile_wrapper.h"
#include "pattern_generator.h"
#include <vector>
#include <chrono>
#include <iostream>
#include <fcntl.h>

class GDSIntegrationTest : public GpuTest {
protected:
    // Test file path - use /tmp for CI, can be changed to NVMe mount point
    const std::string test_file_ = "/tmp/gds_integration_test.bin";

    void TearDown() override {
        std::remove(test_file_.c_str());
        GpuTest::TearDown();
    }
};

TEST_F(GDSIntegrationTest, BasicReadWrite) {
    CuFileDriver driver;

    const size_t data_size = 4 * 1024 * 1024;  // 4 MB
    std::vector<uint8_t> pattern(data_size);

    // Generate test pattern
    for (size_t i = 0; i < data_size; i++) {
        pattern[i] = i % 256;
    }

    // Write via GDS
    {
        CuFileBuffer buffer(data_size);
        buffer.copyToDevice(pattern.data(), data_size);

        CuFileHandle file(test_file_, O_CREAT | O_RDWR | O_TRUNC);
        ssize_t written = file.write(buffer.get(), data_size, 0);
        ASSERT_EQ(written, static_cast<ssize_t>(data_size));

        fsync(file.getFd());
    }

    // Read back via GDS
    std::vector<uint8_t> read_data(data_size);
    {
        CuFileBuffer buffer(data_size);
        CuFileHandle file(test_file_, O_RDONLY);

        ssize_t read_bytes = file.read(buffer.get(), data_size, 0);
        ASSERT_EQ(read_bytes, static_cast<ssize_t>(data_size));

        buffer.copyToHost(read_data.data(), data_size);
    }

    // Verify data integrity
    EXPECT_EQ(pattern, read_data);
}

TEST_F(GDSIntegrationTest, LargeFileTransfer) {
    CuFileDriver driver;

    const size_t file_size = 64 * 1024 * 1024;  // 64 MB
    std::vector<uint8_t> pattern(file_size);

    // Generate block-based test pattern
    for (size_t i = 0; i < file_size; i++) {
        pattern[i] = (i / 4096) % 256;  // Block-based pattern
    }

    // Write large file via GDS
    auto write_start = std::chrono::high_resolution_clock::now();
    {
        CuFileBuffer buffer(file_size);
        buffer.copyToDevice(pattern.data(), file_size);

        CuFileHandle file(test_file_, O_CREAT | O_RDWR | O_TRUNC);
        ssize_t written = file.write(buffer.get(), file_size, 0);
        ASSERT_EQ(written, static_cast<ssize_t>(file_size));

        fsync(file.getFd());
    }
    auto write_end = std::chrono::high_resolution_clock::now();

    // Read back via GDS
    auto read_start = std::chrono::high_resolution_clock::now();
    std::vector<uint8_t> read_data(file_size);
    {
        CuFileBuffer buffer(file_size);
        CuFileHandle file(test_file_, O_RDONLY);

        ssize_t read_bytes = file.read(buffer.get(), file_size, 0);
        ASSERT_EQ(read_bytes, static_cast<ssize_t>(file_size));

        buffer.copyToHost(read_data.data(), file_size);
    }
    auto read_end = std::chrono::high_resolution_clock::now();

    // Verify data integrity
    EXPECT_EQ(pattern, read_data);

    // Report performance
    double write_time = std::chrono::duration<double>(write_end - write_start).count();
    double read_time = std::chrono::duration<double>(read_end - read_start).count();
    double write_bw = (file_size / 1e9) / write_time;
    double read_bw = (file_size / 1e9) / read_time;

    std::cout << "\n[Performance Metrics]\n";
    std::cout << "  Write bandwidth: " << write_bw << " GB/s\n";
    std::cout << "  Read bandwidth:  " << read_bw << " GB/s\n";

    // Expect reasonable performance (very conservative thresholds)
    EXPECT_GT(write_bw, 0.5);  // At least 500 MB/s
    EXPECT_GT(read_bw, 0.5);
}

TEST_F(GDSIntegrationTest, RandomAccessPattern) {
    CuFileDriver driver;

    const size_t block_size = 4096;
    const size_t num_blocks = 1024;
    const size_t file_size = block_size * num_blocks;

    // Write file with block-numbered pattern
    {
        CuFileBuffer buffer(file_size);
        std::vector<uint32_t> pattern(file_size / sizeof(uint32_t));

        for (size_t i = 0; i < pattern.size(); i++) {
            pattern[i] = i / (block_size / sizeof(uint32_t));  // Block number
        }

        buffer.copyToDevice(pattern.data(), file_size);

        CuFileHandle file(test_file_, O_CREAT | O_RDWR | O_TRUNC);
        file.write(buffer.get(), file_size, 0);
        fsync(file.getFd());
    }

    // Random read test
    {
        CuFileBuffer buffer(block_size);
        CuFileHandle file(test_file_, O_RDONLY);

        // Read blocks 0, 512, 256, 768 (random access)
        std::vector<size_t> block_indices = {0, 512, 256, 768};

        for (size_t block_idx : block_indices) {
            off_t offset = block_idx * block_size;
            ssize_t read_bytes = file.read(buffer.get(), block_size, offset);
            ASSERT_EQ(read_bytes, static_cast<ssize_t>(block_size));

            // Verify block number
            std::vector<uint32_t> block_data(block_size / sizeof(uint32_t));
            buffer.copyToHost(block_data.data(), block_size);

            EXPECT_EQ(block_data[0], static_cast<uint32_t>(block_idx));
        }
    }
}

TEST_F(GDSIntegrationTest, GPUGeneratedPattern) {
    CuFileDriver driver;

    const size_t data_size = 16 * 1024 * 1024;  // 16 MB

    // Generate pattern on GPU and write directly
    {
        CuFileBuffer buffer(data_size);

        // Use GPU kernel to generate pattern
        launchGeneratePattern(reinterpret_cast<uint8_t*>(buffer.get()),
                              data_size, 0, 0);
        cudaDeviceSynchronize();

        CuFileHandle file(test_file_, O_CREAT | O_RDWR | O_TRUNC);
        ssize_t written = file.write(buffer.get(), data_size, 0);
        ASSERT_EQ(written, static_cast<ssize_t>(data_size));

        fsync(file.getFd());
    }

    // Read back and verify on GPU
    {
        CuFileBuffer buffer(data_size);
        CuFileHandle file(test_file_, O_RDONLY);

        ssize_t read_bytes = file.read(buffer.get(), data_size, 0);
        ASSERT_EQ(read_bytes, static_cast<ssize_t>(data_size));

        // Verify pattern on GPU
        int mismatches = launchVerifyPattern(
            reinterpret_cast<const uint8_t*>(buffer.get()),
            data_size, 0, 0);

        EXPECT_EQ(mismatches, 0);
    }
}

TEST_F(GDSIntegrationTest, ChunkedTransfer) {
    CuFileDriver driver;

    const size_t total_size = 32 * 1024 * 1024;   // 32 MB total
    const size_t chunk_size = 4 * 1024 * 1024;    // 4 MB chunks
    const size_t num_chunks = total_size / chunk_size;

    std::vector<uint8_t> full_data(total_size);
    for (size_t i = 0; i < total_size; i++) {
        full_data[i] = i % 256;
    }

    // Write in chunks
    {
        CuFileHandle file(test_file_, O_CREAT | O_RDWR | O_TRUNC);
        CuFileBuffer buffer(chunk_size);

        for (size_t chunk = 0; chunk < num_chunks; chunk++) {
            off_t offset = chunk * chunk_size;
            buffer.copyToDevice(&full_data[offset], chunk_size);

            ssize_t written = file.write(buffer.get(), chunk_size, offset);
            ASSERT_EQ(written, static_cast<ssize_t>(chunk_size));
        }

        fsync(file.getFd());
    }

    // Read back in chunks and verify
    {
        CuFileHandle file(test_file_, O_RDONLY);
        CuFileBuffer buffer(chunk_size);
        std::vector<uint8_t> read_chunk(chunk_size);

        for (size_t chunk = 0; chunk < num_chunks; chunk++) {
            off_t offset = chunk * chunk_size;

            ssize_t read_bytes = file.read(buffer.get(), chunk_size, offset);
            ASSERT_EQ(read_bytes, static_cast<ssize_t>(chunk_size));

            buffer.copyToHost(read_chunk.data(), chunk_size);

            // Verify this chunk
            for (size_t i = 0; i < chunk_size; i++) {
                EXPECT_EQ(read_chunk[i], full_data[offset + i]);
            }
        }
    }
}
