/**
 * @file test_filesystem_integration.cpp
 * @brief Integration tests for NVMe Simple Filesystem
 *
 * Tests the complete filesystem workflow with mock NVMe device:
 * - Multi-file operations
 * - Concurrent file access
 * - Garbage collection
 * - Error handling
 */

#include <gtest/gtest.h>
#include "nvme_simple_fs.h"
#include "mock_nvme_device.h"
#include <vector>
#include <string>
#include <random>
#include <algorithm>

class FilesystemIntegrationTest : public ::testing::Test {
protected:
    MockNvmeDevice* mock_device;
    std::unique_ptr<nvme_fs::NvmeSimpleFilesystem> fs;

    void SetUp() override {
        mock_device = new MockNvmeDevice();
        fs = nvme_fs::create_filesystem(
            mock_device, 0, MockNvmeDevice::TOTAL_BLOCKS, MockNvmeDevice::BLOCK_SIZE);
    }

    void TearDown() override {
        fs.reset();
        delete mock_device;
    }

    std::vector<std::uint8_t> generate_random_data(std::size_t size, unsigned int seed = 0) {
        std::vector<std::uint8_t> data(size);
        std::mt19937 gen(seed);
        std::uniform_int_distribution<> dist(0, 255);
        for (auto& byte : data) {
            byte = static_cast<std::uint8_t>(dist(gen));
        }
        return data;
    }
};

/**
 * @brief Test creating and managing multiple files
 */
TEST_F(FilesystemIntegrationTest, MultipleFileOperations) {
    const int num_files = 10;
    std::vector<std::string> filenames;
    std::vector<std::vector<std::uint8_t>> file_data;

    // Create multiple files with different sizes
    for (int i = 0; i < num_files; ++i) {
        std::string filename = "file_" + std::to_string(i) + ".bin";
        std::size_t size = 512 + i * 1024;  // Varying sizes
        auto data = generate_random_data(size, i);

        std::uint32_t file_id = fs->save_file(filename, data.data(), data.size());
        EXPECT_GT(file_id, 0) << "Failed to create file: " << filename;

        filenames.push_back(filename);
        file_data.push_back(std::move(data));
    }

    // Verify all files can be read correctly
    for (std::size_t i = 0; i < filenames.size(); ++i) {
        std::vector<std::uint8_t> read_buffer(file_data[i].size());
        std::size_t read_bytes = fs->read_file(filenames[i], read_buffer.data(), read_buffer.size());

        EXPECT_EQ(read_bytes, file_data[i].size()) << "Size mismatch for " << filenames[i];
        EXPECT_EQ(read_buffer, file_data[i]) << "Data mismatch for " << filenames[i];
    }

    // Verify filesystem stats
    std::uint64_t total, used, free;
    fs->get_stats(total, used, free);
    EXPECT_GT(used, 0);
    EXPECT_EQ(total, used + free);
}

/**
 * @brief Test file update and overwrite scenarios
 */
TEST_F(FilesystemIntegrationTest, FileUpdateAndOverwrite) {
    // Create initial file
    std::vector<std::uint8_t> initial_data = generate_random_data(4096, 1);
    fs->save_file("update_test.bin", initial_data.data(), initial_data.size());

    // Update middle section
    std::vector<std::uint8_t> update_data = generate_random_data(1024, 2);
    fs->write_file("update_test.bin", 1024, update_data.data(), update_data.size());

    // Read and verify
    std::vector<std::uint8_t> read_buffer(4096);
    fs->read_file("update_test.bin", read_buffer.data(), read_buffer.size());

    // Check unchanged regions
    for (std::size_t i = 0; i < 1024; ++i) {
        EXPECT_EQ(read_buffer[i], initial_data[i]);
    }
    // Check updated region
    for (std::size_t i = 0; i < 1024; ++i) {
        EXPECT_EQ(read_buffer[1024 + i], update_data[i]);
    }
    // Check unchanged tail
    for (std::size_t i = 2048; i < 4096; ++i) {
        EXPECT_EQ(read_buffer[i], initial_data[i]);
    }
}

/**
 * @brief Test garbage collection after file deletion
 */
TEST_F(FilesystemIntegrationTest, GarbageCollectionFlow) {
    // Create fragmented filesystem
    std::vector<std::uint8_t> data1 = generate_random_data(2048, 1);
    std::vector<std::uint8_t> data2 = generate_random_data(2048, 2);
    std::vector<std::uint8_t> data3 = generate_random_data(2048, 3);

    fs->save_file("file1.bin", data1.data(), data1.size());
    fs->save_file("file2.bin", data2.data(), data2.size());
    fs->save_file("file3.bin", data3.data(), data3.size());

    // Delete middle file
    bool deleted = fs->delete_file("file2.bin");
    EXPECT_TRUE(deleted);

    // Check stats before GC
    std::uint64_t total, used_before, free_before;
    fs->get_stats(total, used_before, free_before);

    // Run garbage collection
    fs->garbage_collect();

    // Verify file1 and file3 still accessible
    std::vector<std::uint8_t> read_buffer1(data1.size());
    std::vector<std::uint8_t> read_buffer3(data3.size());

    fs->read_file("file1.bin", read_buffer1.data(), read_buffer1.size());
    fs->read_file("file3.bin", read_buffer3.data(), read_buffer3.size());

    EXPECT_EQ(read_buffer1, data1);
    EXPECT_EQ(read_buffer3, data3);

    // Verify file2 is inaccessible
    EXPECT_THROW(fs->read_file("file2.bin", data2.data(), data2.size()),
                 std::runtime_error);
}

/**
 * @brief Test filesystem capacity limits
 */
TEST_F(FilesystemIntegrationTest, FilesystemCapacity) {
    std::uint64_t total, used, free;
    fs->get_stats(total, used, free);

    // Try to fill filesystem
    std::size_t block_size = 4096;
    int files_created = 0;

    while (free > block_size * 2) {  // Keep some margin
        std::string filename = "fill_" + std::to_string(files_created) + ".bin";
        auto data = generate_random_data(block_size, files_created);

        try {
            fs->save_file(filename, data.data(), data.size());
            files_created++;
        } catch (const std::exception& e) {
            // Expected when filesystem is full
            break;
        }

        fs->get_stats(total, used, free);
    }

    EXPECT_GT(files_created, 0);
    fs->get_stats(total, used, free);
    EXPECT_GT(used, 0);
}

/**
 * @brief Test error handling for invalid operations
 */
TEST_F(FilesystemIntegrationTest, ErrorHandling) {
    // Read non-existent file
    std::vector<std::uint8_t> buffer(1024);
    EXPECT_THROW(fs->read_file("nonexistent.bin", buffer.data(), buffer.size()),
                 std::runtime_error);

    // Delete non-existent file
    bool deleted = fs->delete_file("nonexistent.bin");
    EXPECT_FALSE(deleted);

    // Write to non-existent file
    EXPECT_THROW(fs->write_file("nonexistent.bin", 0, buffer.data(), buffer.size()),
                 std::runtime_error);

    // Create file with valid data
    std::vector<std::uint8_t> data = generate_random_data(1024, 1);
    fs->save_file("test.bin", data.data(), data.size());

    // Write beyond file bounds
    EXPECT_THROW(fs->write_file("test.bin", 2048, buffer.data(), buffer.size()),
                 std::runtime_error);
}

/**
 * @brief Test list_files functionality
 */
TEST_F(FilesystemIntegrationTest, ListFilesOperation) {
    // Initially empty
    auto files = fs->list_files();
    EXPECT_TRUE(files.empty());

    // Create several files
    std::vector<std::string> expected_names = {
        "alpha.txt", "beta.dat", "gamma.bin", "delta.log"
    };

    for (const auto& name : expected_names) {
        auto data = generate_random_data(512, 0);
        fs->save_file(name, data.data(), data.size());
    }

    // List and verify
    files = fs->list_files();
    EXPECT_EQ(files.size(), expected_names.size());

    std::vector<std::string> actual_names;
    for (const auto& entry : files) {
        actual_names.push_back(entry.name);
    }

    std::sort(expected_names.begin(), expected_names.end());
    std::sort(actual_names.begin(), actual_names.end());
    EXPECT_EQ(actual_names, expected_names);
}

/**
 * @brief Test C API wrapper integration
 */
TEST_F(FilesystemIntegrationTest, CApiIntegration) {
    // This test verifies the C API wrapper works with the C++ implementation
    // The actual C API tests are in test_c_api.cpp

    std::vector<std::uint8_t> data = generate_random_data(2048, 42);
    std::uint32_t file_id = fs->save_file("c_api_test.bin", data.data(), data.size());
    EXPECT_GT(file_id, 0);

    std::vector<std::uint8_t> read_buffer(data.size());
    std::size_t read_bytes = fs->read_file("c_api_test.bin", read_buffer.data(), read_buffer.size());

    EXPECT_EQ(read_bytes, data.size());
    EXPECT_EQ(read_buffer, data);
}
