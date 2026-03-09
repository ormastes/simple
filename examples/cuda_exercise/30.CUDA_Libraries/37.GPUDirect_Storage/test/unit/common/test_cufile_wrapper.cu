#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cufile_wrapper.h"
#include <vector>
#include <cstdio>
#include <fcntl.h>

class CuFileWrapperTest : public GpuTest {
protected:
    const std::string test_file_ = "/tmp/cufile_test.bin";

    void TearDown() override {
        std::remove(test_file_.c_str());
        GpuTest::TearDown();
    }
};

TEST_F(CuFileWrapperTest, DriverInitialization) {
    // Test that driver can be initialized
    ASSERT_NO_THROW({
        CuFileDriver driver;
        EXPECT_TRUE(driver.isOpen());
    });
}

TEST_F(CuFileWrapperTest, FileHandleCreation) {
    CuFileDriver driver;

    // Test file creation and opening
    ASSERT_NO_THROW({
        CuFileHandle file(test_file_, O_CREAT | O_RDWR | O_TRUNC);
        EXPECT_TRUE(file.isValid());
        EXPECT_GE(file.getFd(), 0);
    });
}

TEST_F(CuFileWrapperTest, BufferAllocation) {
    const size_t buffer_size = 4 * 1024 * 1024;  // 4 MB

    ASSERT_NO_THROW({
        CuFileBuffer buffer(buffer_size);
        EXPECT_NE(buffer.get(), nullptr);
        EXPECT_EQ(buffer.size(), buffer_size);
    });
}

TEST_F(CuFileWrapperTest, WriteAndReadData) {
    CuFileDriver driver;
    const size_t data_size = 1 * 1024 * 1024;  // 1 MB

    // Prepare test data
    std::vector<uint8_t> write_data(data_size);
    for (size_t i = 0; i < data_size; i++) {
        write_data[i] = i % 256;
    }

    // Write to file
    {
        CuFileBuffer buffer(data_size);
        buffer.copyToDevice(write_data.data(), data_size);

        CuFileHandle file(test_file_, O_CREAT | O_RDWR | O_TRUNC);
        ssize_t written = file.write(buffer.get(), data_size, 0);
        EXPECT_EQ(written, static_cast<ssize_t>(data_size));

        fsync(file.getFd());
    }

    // Read back and verify
    {
        CuFileBuffer buffer(data_size);
        CuFileHandle file(test_file_, O_RDONLY);

        ssize_t read_bytes = file.read(buffer.get(), data_size, 0);
        EXPECT_EQ(read_bytes, static_cast<ssize_t>(data_size));

        std::vector<uint8_t> read_data(data_size);
        buffer.copyToHost(read_data.data(), data_size);

        EXPECT_EQ(write_data, read_data);
    }
}

TEST_F(CuFileWrapperTest, OffsetReadWrite) {
    CuFileDriver driver;
    const size_t total_size = 8 * 1024 * 1024;   // 8 MB file
    const size_t chunk_size = 1 * 1024 * 1024;   // 1 MB chunks
    const off_t offset = 4 * 1024 * 1024;        // Write at 4 MB offset

    std::vector<uint8_t> data(chunk_size, 0xAB);

    // Write at offset
    {
        CuFileBuffer buffer(total_size);
        buffer.copyToDevice(data.data(), chunk_size);

        CuFileHandle file(test_file_, O_CREAT | O_RDWR | O_TRUNC);

        // First, write zeros to ensure file is large enough
        std::vector<uint8_t> zeros(total_size, 0);
        buffer.copyToDevice(zeros.data(), total_size);
        file.write(buffer.get(), total_size, 0);

        // Now write chunk at 4 MB offset
        buffer.copyToDevice(data.data(), chunk_size);
        ssize_t written = file.write(buffer.get(), chunk_size, offset, 0);
        EXPECT_EQ(written, static_cast<ssize_t>(chunk_size));
        fsync(file.getFd());
    }

    // Read at offset and verify
    {
        CuFileBuffer buffer(total_size);
        CuFileHandle file(test_file_, O_RDONLY);

        ssize_t read_bytes = file.read(buffer.get(), chunk_size, offset, 0);
        EXPECT_EQ(read_bytes, static_cast<ssize_t>(chunk_size));

        std::vector<uint8_t> read_data(chunk_size);
        buffer.copyToHost(read_data.data(), chunk_size);

        EXPECT_EQ(data, read_data);
    }
}

TEST_F(CuFileWrapperTest, MultipleBuffers) {
    CuFileDriver driver;
    const size_t buffer_size = 2 * 1024 * 1024;  // 2 MB

    // Test multiple buffer allocations don't interfere
    CuFileBuffer buffer1(buffer_size);
    CuFileBuffer buffer2(buffer_size);
    CuFileBuffer buffer3(buffer_size);

    EXPECT_NE(buffer1.get(), nullptr);
    EXPECT_NE(buffer2.get(), nullptr);
    EXPECT_NE(buffer3.get(), nullptr);

    // Ensure they have different addresses
    EXPECT_NE(buffer1.get(), buffer2.get());
    EXPECT_NE(buffer2.get(), buffer3.get());
    EXPECT_NE(buffer1.get(), buffer3.get());
}
