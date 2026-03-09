#include "cufile_wrapper.h"
#include <cuda_runtime.h>
#include <fcntl.h>
#include <unistd.h>
#include <cstring>
#include <stdexcept>
#include <iostream>

// Helper function to convert cuFile error to string
static std::string cuFileErrorToString(CUfileError_t err) {
    // cuFile API doesn't provide error string function, so we create our own
    std::string msg = "cuFile error code: " + std::to_string(err.err);
    if (err.err == CU_FILE_DRIVER_NOT_INITIALIZED) {
        msg += " (Driver not initialized)";
    } else if (err.err == CU_FILE_INVALID_VALUE) {
        msg += " (Invalid value)";
    } else if (err.err == CU_FILE_IO_NOT_SUPPORTED) {
        msg += " (I/O not supported)";
    } else if (err.err == CU_FILE_PERMISSION_DENIED) {
        msg += " (Permission denied)";
    }
    return msg;
}

// Helper macro for cuFile error checking
#define CHECK_CUFILE_THROW(call) do { \
    CUfileError_t err = call; \
    if (err.err != CU_FILE_SUCCESS) { \
        throw std::runtime_error(cuFileErrorToString(err)); \
    } \
} while(0)

// ============ CuFileDriver ============

CuFileDriver::CuFileDriver() : is_open_(false) {
    CHECK_CUFILE_THROW(cuFileDriverOpen());
    is_open_ = true;
}

CuFileDriver::~CuFileDriver() {
    if (is_open_) {
        cuFileDriverClose();
    }
}

// ============ CuFileHandle ============

CuFileHandle::CuFileHandle(const std::string& filepath, int flags, mode_t mode)
    : fd_(-1) {
    // Ensure O_DIRECT is set for direct I/O (required for GDS)
    flags |= O_DIRECT;

    fd_ = open(filepath.c_str(), flags, mode);
    if (fd_ < 0) {
        throw std::runtime_error("Failed to open file: " + filepath +
                                 " (errno: " + std::to_string(errno) + ")");
    }

    // Register file descriptor with cuFile
    CUfileDescr_t desc;
    memset(&desc, 0, sizeof(desc));
    desc.type = CU_FILE_HANDLE_TYPE_OPAQUE_FD;
    desc.handle.fd = fd_;

    CUfileError_t status = cuFileHandleRegister(&cf_handle_, &desc);
    if (status.err != CU_FILE_SUCCESS) {
        close(fd_);
        fd_ = -1;
        throw std::runtime_error(std::string("cuFileHandleRegister failed: ") +
                                 cuFileErrorToString(status));
    }
}

CuFileHandle::~CuFileHandle() {
    if (fd_ >= 0) {
        cuFileHandleDeregister(cf_handle_);
        close(fd_);
    }
}

ssize_t CuFileHandle::read(void* d_buffer, size_t size, off_t file_offset,
                           off_t buffer_offset) {
    return cuFileRead(cf_handle_, d_buffer, size, file_offset, buffer_offset);
}

ssize_t CuFileHandle::write(const void* d_buffer, size_t size, off_t file_offset,
                            off_t buffer_offset) {
    return cuFileWrite(cf_handle_, d_buffer, size, file_offset, buffer_offset);
}

// ============ CuFileBuffer ============

CuFileBuffer::CuFileBuffer(size_t size) : d_buffer_(nullptr), size_(size) {
    cudaError_t err = cudaMalloc(&d_buffer_, size);
    if (err != cudaSuccess) {
        throw std::runtime_error(std::string("cudaMalloc failed: ") +
                                 cudaGetErrorString(err));
    }

    CUfileError_t status = cuFileBufRegister(d_buffer_, size, 0);
    if (status.err != CU_FILE_SUCCESS) {
        cudaFree(d_buffer_);
        d_buffer_ = nullptr;
        throw std::runtime_error(std::string("cuFileBufRegister failed: ") +
                                 cuFileErrorToString(status));
    }
}

CuFileBuffer::~CuFileBuffer() {
    if (d_buffer_) {
        cuFileBufDeregister(d_buffer_);
        cudaFree(d_buffer_);
    }
}

void CuFileBuffer::copyToDevice(const void* h_src, size_t copy_size) {
    if (copy_size > size_) {
        throw std::invalid_argument("Copy size exceeds buffer size");
    }
    cudaError_t err = cudaMemcpy(d_buffer_, h_src, copy_size, cudaMemcpyHostToDevice);
    if (err != cudaSuccess) {
        throw std::runtime_error(std::string("cudaMemcpy H2D failed: ") +
                                 cudaGetErrorString(err));
    }
}

void CuFileBuffer::copyToHost(void* h_dst, size_t copy_size) const {
    if (copy_size > size_) {
        throw std::invalid_argument("Copy size exceeds buffer size");
    }
    cudaError_t err = cudaMemcpy(h_dst, d_buffer_, copy_size, cudaMemcpyDeviceToHost);
    if (err != cudaSuccess) {
        throw std::runtime_error(std::string("cudaMemcpy D2H failed: ") +
                                 cudaGetErrorString(err));
    }
}
