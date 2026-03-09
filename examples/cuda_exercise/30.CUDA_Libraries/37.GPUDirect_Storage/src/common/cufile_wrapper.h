#pragma once
#include <cufile.h>
#include <string>
#include <memory>

/**
 * RAII wrapper for cuFile driver initialization.
 * Automatically opens driver on construction and closes on destruction.
 */
class CuFileDriver {
public:
    CuFileDriver();
    ~CuFileDriver();

    // Non-copyable
    CuFileDriver(const CuFileDriver&) = delete;
    CuFileDriver& operator=(const CuFileDriver&) = delete;

    bool isOpen() const { return is_open_; }

private:
    bool is_open_;
};

/**
 * RAII wrapper for cuFile file handle.
 * Manages file descriptor and cuFile handle registration/deregistration.
 */
class CuFileHandle {
public:
    /**
     * Open file and register with cuFile.
     * @param filepath Path to file
     * @param flags Open flags (O_DIRECT will be added automatically)
     * @param mode File mode for creation (default 0664)
     */
    CuFileHandle(const std::string& filepath, int flags, mode_t mode = 0664);
    ~CuFileHandle();

    // Non-copyable, movable
    CuFileHandle(const CuFileHandle&) = delete;
    CuFileHandle& operator=(const CuFileHandle&) = delete;

    /**
     * Read data from file directly into GPU memory.
     * @param d_buffer GPU buffer pointer
     * @param size Number of bytes to read
     * @param file_offset File offset to read from
     * @param buffer_offset Offset into GPU buffer
     * @return Number of bytes read, or negative on error
     */
    ssize_t read(void* d_buffer, size_t size, off_t file_offset,
                 off_t buffer_offset = 0);

    /**
     * Write data from GPU memory directly to file.
     * @param d_buffer GPU buffer pointer
     * @param size Number of bytes to write
     * @param file_offset File offset to write to
     * @param buffer_offset Offset into GPU buffer
     * @return Number of bytes written, or negative on error
     */
    ssize_t write(const void* d_buffer, size_t size, off_t file_offset,
                  off_t buffer_offset = 0);

    int getFd() const { return fd_; }
    bool isValid() const { return fd_ >= 0; }

private:
    int fd_;
    CUfileHandle_t cf_handle_;
};

/**
 * RAII wrapper for GPU buffer allocation and cuFile registration.
 * Automatically allocates, registers, and frees GPU memory.
 */
class CuFileBuffer {
public:
    /**
     * Allocate and register GPU buffer.
     * @param size Buffer size in bytes
     */
    explicit CuFileBuffer(size_t size);
    ~CuFileBuffer();

    // Non-copyable
    CuFileBuffer(const CuFileBuffer&) = delete;
    CuFileBuffer& operator=(const CuFileBuffer&) = delete;

    void* get() const { return d_buffer_; }
    size_t size() const { return size_; }

    /**
     * Copy data from host to GPU buffer.
     * @param h_src Host source pointer
     * @param size Number of bytes to copy
     */
    void copyToDevice(const void* h_src, size_t size);

    /**
     * Copy data from GPU buffer to host.
     * @param h_dst Host destination pointer
     * @param size Number of bytes to copy
     */
    void copyToHost(void* h_dst, size_t size) const;

private:
    void* d_buffer_;
    size_t size_;
};
