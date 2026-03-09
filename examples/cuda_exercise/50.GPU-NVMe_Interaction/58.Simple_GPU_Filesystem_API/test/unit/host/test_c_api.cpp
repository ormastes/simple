/**
 * @file test_c_api.cpp
 * @brief Tests for C API wrapper
 */

#include <gtest/gtest.h>
#include "nvme_simple_fs_c_api.h"
#include "mock_nvme_device.h"
#include <vector>
#include <cstring>

class CApiTest : public ::testing::Test {
protected:
    MockNvmeDevice* mock_device;
    nvme_fs_handle_t* fs;

    void SetUp() override {
        mock_device = new MockNvmeDevice();
        fs = nvme_fs_create(mock_device, 0, MockNvmeDevice::TOTAL_BLOCKS,
                           MockNvmeDevice::BLOCK_SIZE);
        ASSERT_NE(fs, nullptr);
    }

    void TearDown() override {
        nvme_fs_close(fs);
        delete mock_device;
    }
};

TEST_F(CApiTest, SaveAndReadFile) {
    std::vector<uint8_t> data(2048);
    for (size_t i = 0; i < data.size(); ++i) {
        data[i] = static_cast<uint8_t>(i % 256);
    }

    uint32_t file_id = nvme_fs_save_file(fs, "test.bin", data.data(), data.size());
    EXPECT_GT(file_id, 0);

    std::vector<uint8_t> buffer(2048);
    size_t read_bytes = nvme_fs_read_file(fs, "test.bin", buffer.data(), buffer.size());

    EXPECT_EQ(read_bytes, data.size());
    EXPECT_EQ(buffer, data);
}

TEST_F(CApiTest, WriteFile) {
    std::vector<uint8_t> data(1024, 0xAA);
    nvme_fs_save_file(fs, "write.bin", data.data(), data.size());

    std::vector<uint8_t> new_data(256, 0xBB);
    int ret = nvme_fs_write_file(fs, "write.bin", 512, new_data.data(), new_data.size());
    EXPECT_EQ(ret, 0);

    std::vector<uint8_t> buffer(1024);
    nvme_fs_read_file(fs, "write.bin", buffer.data(), buffer.size());

    for (size_t i = 0; i < 512; ++i) {
        EXPECT_EQ(buffer[i], 0xAA);
    }
    for (size_t i = 512; i < 512 + 256; ++i) {
        EXPECT_EQ(buffer[i], 0xBB);
    }
    for (size_t i = 512 + 256; i < 1024; ++i) {
        EXPECT_EQ(buffer[i], 0xAA);
    }
}

TEST_F(CApiTest, DeleteFile) {
    std::vector<uint8_t> data(512, 0x42);
    nvme_fs_save_file(fs, "delete.bin", data.data(), data.size());

    int ret = nvme_fs_delete_file(fs, "delete.bin");
    EXPECT_EQ(ret, 1);

    // Try to read deleted file
    size_t read_bytes = nvme_fs_read_file(fs, "delete.bin", data.data(), data.size());
    EXPECT_EQ(read_bytes, 0);
}

TEST_F(CApiTest, GetFileInfo) {
    std::vector<uint8_t> data(1536, 0x77);
    nvme_fs_save_file(fs, "info.bin", data.data(), data.size());

    nvme_fs_file_info_t info;
    int ret = nvme_fs_get_file_info(fs, "info.bin", &info);

    EXPECT_EQ(ret, 0);
    EXPECT_STREQ(info.name, "info.bin");
    EXPECT_EQ(info.size_bytes, 1536);
    EXPECT_GT(info.file_id, 0);
}

TEST_F(CApiTest, ListFiles) {
    std::vector<uint8_t> data(256, 0x11);

    nvme_fs_save_file(fs, "file1.bin", data.data(), data.size());
    nvme_fs_save_file(fs, "file2.bin", data.data(), data.size());
    nvme_fs_save_file(fs, "file3.bin", data.data(), data.size());

    nvme_fs_file_info_t files[10];
    size_t count = nvme_fs_list_files(fs, files, 10);

    EXPECT_EQ(count, 3);
}

TEST_F(CApiTest, NodeBasedIO) {
    std::vector<uint8_t> data(4096);
    for (size_t i = 0; i < data.size(); ++i) {
        data[i] = static_cast<uint8_t>(i % 256);
    }

    nvme_fs_save_file(fs, "node.bin", data.data(), data.size());

    nvme_fs_node_t node;
    int ret = nvme_fs_get_file_node(fs, "node.bin", &node);
    EXPECT_EQ(ret, 0);

    std::vector<uint8_t> buffer(1024);
    ret = nvme_fs_read_node(fs, &node, 2048, buffer.data(), buffer.size());
    EXPECT_EQ(ret, 0);

    for (size_t i = 0; i < buffer.size(); ++i) {
        EXPECT_EQ(buffer[i], (2048 + i) % 256);
    }

    std::vector<uint8_t> new_data(512, 0xFF);
    ret = nvme_fs_write_node(fs, &node, 1024, new_data.data(), new_data.size());
    EXPECT_EQ(ret, 0);

    ret = nvme_fs_read_node(fs, &node, 1024, buffer.data(), 512);
    EXPECT_EQ(ret, 0);

    for (size_t i = 0; i < 512; ++i) {
        EXPECT_EQ(buffer[i], 0xFF);
    }
}

TEST_F(CApiTest, GetStats) {
    nvme_fs_stats_t stats;
    int ret = nvme_fs_get_stats(fs, &stats);

    EXPECT_EQ(ret, 0);
    EXPECT_GT(stats.total_bytes, 0);
    EXPECT_EQ(stats.num_files, 0);

    std::vector<uint8_t> data(1024, 0xAA);
    nvme_fs_save_file(fs, "stats.bin", data.data(), data.size());

    ret = nvme_fs_get_stats(fs, &stats);
    EXPECT_EQ(ret, 0);
    EXPECT_GT(stats.used_bytes, 0);
    EXPECT_EQ(stats.num_files, 1);
}

TEST_F(CApiTest, GarbageCollect) {
    std::vector<uint8_t> data(512, 0xBB);

    nvme_fs_save_file(fs, "gc1.bin", data.data(), data.size());
    nvme_fs_save_file(fs, "gc2.bin", data.data(), data.size());
    nvme_fs_save_file(fs, "gc3.bin", data.data(), data.size());

    nvme_fs_delete_file(fs, "gc2.bin");

    size_t merged = nvme_fs_garbage_collect(fs);
    EXPECT_GE(merged, 0);
}

TEST_F(CApiTest, FlushMetadata) {
    std::vector<uint8_t> data(1024, 0xCC);
    nvme_fs_save_file(fs, "flush.bin", data.data(), data.size());

    int ret = nvme_fs_flush(fs);
    EXPECT_EQ(ret, 0);
}
