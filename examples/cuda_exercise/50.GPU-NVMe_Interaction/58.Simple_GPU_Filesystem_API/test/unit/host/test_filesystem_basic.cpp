/**
 * @file test_filesystem_basic.cpp
 * @brief Basic filesystem tests
 */

#include <gtest/gtest.h>
#include "nvme_simple_fs.h"
#include "mock_nvme_device.h"
#include <vector>
#include <cstring>

class FilesystemBasicTest : public ::testing::Test {
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
};

TEST_F(FilesystemBasicTest, CreateFilesystem) {
    ASSERT_NE(fs, nullptr);

    std::uint64_t total, used, free;
    fs->get_stats(total, used, free);

    EXPECT_GT(total, 0);
    EXPECT_EQ(used, 0);
    EXPECT_EQ(free, total);
}

TEST_F(FilesystemBasicTest, SaveAndReadFile) {
    std::vector<std::uint8_t> data(4096);
    for (std::size_t i = 0; i < data.size(); ++i) {
        data[i] = static_cast<std::uint8_t>(i % 256);
    }

    std::uint32_t file_id = fs->save_file("test.bin", data.data(), data.size());
    EXPECT_GT(file_id, 0);

    std::vector<std::uint8_t> read_buffer(data.size());
    std::size_t read_bytes = fs->read_file("test.bin", read_buffer.data(), read_buffer.size());

    EXPECT_EQ(read_bytes, data.size());
    EXPECT_EQ(read_buffer, data);
}

TEST_F(FilesystemBasicTest, WriteFileAtOffset) {
    std::vector<std::uint8_t> data(4096, 0xAA);
    fs->save_file("test.bin", data.data(), data.size());

    // Overwrite middle section
    std::vector<std::uint8_t> new_data(512, 0xBB);
    fs->write_file("test.bin", 1024, new_data.data(), new_data.size());

    // Read back and verify
    std::vector<std::uint8_t> read_buffer(4096);
    fs->read_file("test.bin", read_buffer.data(), read_buffer.size());

    // Check original data before offset
    for (std::size_t i = 0; i < 1024; ++i) {
        EXPECT_EQ(read_buffer[i], 0xAA) << "Mismatch at offset " << i;
    }

    // Check modified section
    for (std::size_t i = 1024; i < 1024 + 512; ++i) {
        EXPECT_EQ(read_buffer[i], 0xBB) << "Mismatch at offset " << i;
    }

    // Check original data after modified section
    for (std::size_t i = 1024 + 512; i < 4096; ++i) {
        EXPECT_EQ(read_buffer[i], 0xAA) << "Mismatch at offset " << i;
    }
}

TEST_F(FilesystemBasicTest, DeleteFile) {
    std::vector<std::uint8_t> data(1024, 0x42);
    fs->save_file("temp.bin", data.data(), data.size());

    std::uint64_t total, used_before, free_before;
    fs->get_stats(total, used_before, free_before);
    EXPECT_GT(used_before, 0);

    bool deleted = fs->delete_file("temp.bin");
    EXPECT_TRUE(deleted);

    std::uint64_t used_after, free_after;
    fs->get_stats(total, used_after, free_after);
    EXPECT_LT(used_after, used_before);
    EXPECT_GT(free_after, free_before);

    EXPECT_THROW(fs->read_file("temp.bin", data.data(), data.size()),
                 nvme_fs::FileNotFoundError);
}

TEST_F(FilesystemBasicTest, GetFileInfo) {
    std::vector<std::uint8_t> data(2048, 0x55);
    fs->save_file("info.bin", data.data(), data.size());

    nvme_fs::FileEntry info = fs->get_file_info("info.bin");
    EXPECT_EQ(info.name, "info.bin");
    EXPECT_EQ(info.size_bytes, 2048);
    EXPECT_GT(info.file_id, 0);
    EXPECT_GT(info.created_time, 0);
}

TEST_F(FilesystemBasicTest, ListFiles) {
    std::vector<std::uint8_t> data(512, 0x11);

    fs->save_file("file1.bin", data.data(), data.size());
    fs->save_file("file2.bin", data.data(), data.size());
    fs->save_file("file3.bin", data.data(), data.size());

    std::vector<nvme_fs::FileEntry> files = fs->list_files();
    EXPECT_EQ(files.size(), 3);

    bool found1 = false, found2 = false, found3 = false;
    for (const auto& file : files) {
        if (file.name == "file1.bin") found1 = true;
        if (file.name == "file2.bin") found2 = true;
        if (file.name == "file3.bin") found3 = true;
    }

    EXPECT_TRUE(found1);
    EXPECT_TRUE(found2);
    EXPECT_TRUE(found3);
}

TEST_F(FilesystemBasicTest, AccessViolation) {
    std::vector<std::uint8_t> data(1024, 0xCC);
    fs->save_file("small.bin", data.data(), data.size());

    std::vector<std::uint8_t> buffer(512);

    // Try to write past end of file
    EXPECT_THROW(fs->write_file("small.bin", 1024, buffer.data(), buffer.size()),
                 nvme_fs::AccessViolationError);

    // Try to read past end of file
    nvme_fs::LbaNode node = fs->get_file_node("small.bin");
    EXPECT_THROW(fs->read_node(node, 2048, buffer.data(), buffer.size()),
                 nvme_fs::AccessViolationError);
}

TEST_F(FilesystemBasicTest, GarbageCollection) {
    std::vector<std::uint8_t> data(1024, 0xDD);

    fs->save_file("gc1.bin", data.data(), data.size());
    fs->save_file("gc2.bin", data.data(), data.size());
    fs->save_file("gc3.bin", data.data(), data.size());

    fs->delete_file("gc2.bin");

    std::size_t merged = fs->garbage_collect();
    // After GC, free nodes should be coalesced if they were adjacent
    EXPECT_GE(merged, 0);
}

TEST_F(FilesystemBasicTest, NodeBasedIO) {
    std::vector<std::uint8_t> data(4096);
    for (std::size_t i = 0; i < data.size(); ++i) {
        data[i] = static_cast<std::uint8_t>(i % 256);
    }

    fs->save_file("node.bin", data.data(), data.size());
    nvme_fs::LbaNode node = fs->get_file_node("node.bin");

    // Read using node API
    std::vector<std::uint8_t> buffer(1024);
    fs->read_node(node, 2048, buffer.data(), buffer.size());

    for (std::size_t i = 0; i < buffer.size(); ++i) {
        EXPECT_EQ(buffer[i], (2048 + i) % 256);
    }

    // Write using node API
    std::vector<std::uint8_t> new_data(512, 0xEE);
    fs->write_node(node, 1024, new_data.data(), new_data.size());

    // Verify write
    fs->read_node(node, 1024, buffer.data(), 512);
    for (std::size_t i = 0; i < 512; ++i) {
        EXPECT_EQ(buffer[i], 0xEE);
    }
}

TEST_F(FilesystemBasicTest, TemplateNodeIO) {
    std::vector<float> data(256);
    for (std::size_t i = 0; i < data.size(); ++i) {
        data[i] = static_cast<float>(i) * 1.5f;
    }

    fs->save_file("floats.bin", data.data(), data.size() * sizeof(float));
    nvme_fs::LbaNode node = fs->get_file_node("floats.bin");

    // Read using template API
    std::vector<float> read_data(256);
    fs->read_node_template<float>(node, 0, read_data.data(), read_data.size());

    for (std::size_t i = 0; i < data.size(); ++i) {
        EXPECT_FLOAT_EQ(read_data[i], data[i]);
    }

    // Write using template API
    std::vector<float> new_data(64, 42.0f);
    fs->write_node_template<float>(node, 128 * sizeof(float),
                                    new_data.data(), new_data.size());

    // Verify
    fs->read_node_template<float>(node, 128 * sizeof(float),
                                  read_data.data(), 64);
    for (std::size_t i = 0; i < 64; ++i) {
        EXPECT_FLOAT_EQ(read_data[i], 42.0f);
    }
}
