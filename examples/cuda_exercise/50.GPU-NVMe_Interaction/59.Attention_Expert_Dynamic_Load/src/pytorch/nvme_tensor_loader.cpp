/**
 * @file nvme_tensor_loader.cpp
 * @brief NVMe tensor loading utilities for PyTorch
 *
 * Provides direct NVMe-to-tensor loading with dictionary-based access patterns.
 * Integrates with Module 58's filesystem API for structured data loading.
 */

#include <torch/extension.h>
#include <c10/cuda/CUDAGuard.h>
#include <cuda_runtime.h>
#include <map>
#include <string>
#include <vector>
#include <fcntl.h>
#include <unistd.h>

namespace attention_expert {

/**
 * @brief Read NVMe data directly into PyTorch tensor
 *
 * @param tensor    Existing CUDA tensor to read into
 * @param device_path Path to NVMe device/file
 * @param offset    Byte offset in device
 * @param size      Number of bytes to read
 * @return The input tensor (for chaining)
 */
at::Tensor read_into_tensor(
    at::Tensor& tensor,
    const std::string& device_path,
    int64_t offset,
    int64_t size
) {
    // Validate tensor properties
    TORCH_CHECK(tensor.is_cuda(), "Tensor must be on CUDA device");
    TORCH_CHECK(tensor.is_contiguous(), "Tensor must be contiguous");
    TORCH_CHECK(tensor.numel() * tensor.element_size() >= size,
                "Tensor too small: need ", size, " bytes, have ",
                tensor.numel() * tensor.element_size());

    const at::cuda::OptionalCUDAGuard device_guard(device_of(tensor));

    // Get CUDA device pointer
    void* gpu_ptr = tensor.data_ptr();

    // Open NVMe device
    int fd = open(device_path.c_str(), O_RDONLY | O_DIRECT);
    TORCH_CHECK(fd >= 0, "Failed to open device: ", device_path);

    // Allocate aligned host buffer for O_DIRECT
    void* host_buffer = nullptr;
    int ret = posix_memalign(&host_buffer, 4096, size);
    TORCH_CHECK(ret == 0, "Failed to allocate aligned buffer");

    // Read from NVMe to host buffer
    ssize_t bytes_read = pread(fd, host_buffer, size, offset);
    close(fd);

    TORCH_CHECK(bytes_read == size, "Read failed: expected ", size,
                " bytes, got ", bytes_read);

    // Copy from host to GPU
    cudaError_t err = cudaMemcpy(gpu_ptr, host_buffer, size, cudaMemcpyHostToDevice);
    free(host_buffer);

    TORCH_CHECK(err == cudaSuccess, "CUDA memcpy failed: ", cudaGetErrorString(err));

    return tensor;
}

/**
 * @brief Allocate tensor and read NVMe data
 *
 * @param device_path Path to NVMe device/file
 * @param offset      Byte offset in device
 * @param shape       Tensor shape
 * @param dtype       Data type
 * @return Tensor containing NVMe data
 */
at::Tensor read_tensor(
    const std::string& device_path,
    int64_t offset,
    at::IntArrayRef shape,
    at::ScalarType dtype
) {
    // Calculate size
    int64_t num_elements = 1;
    for (auto dim : shape) {
        num_elements *= dim;
    }

    size_t element_size = at::elementSize(dtype);
    size_t total_size = num_elements * element_size;

    // Allocate tensor on GPU
    auto options = at::TensorOptions()
        .dtype(dtype)
        .device(at::kCUDA)
        .requires_grad(false);

    at::Tensor tensor = at::empty(shape, options);

    // Read data
    read_into_tensor(tensor, device_path, offset, total_size);

    return tensor;
}

/**
 * @brief Write tensor to NVMe
 *
 * @param tensor      PyTorch tensor to write
 * @param device_path Path to NVMe device/file
 * @param offset      Byte offset in device
 * @return Number of bytes written
 */
int64_t write_tensor(
    const at::Tensor& tensor,
    const std::string& device_path,
    int64_t offset
) {
    TORCH_CHECK(tensor.is_cuda(), "Tensor must be on CUDA device");
    TORCH_CHECK(tensor.is_contiguous(), "Tensor must be contiguous");

    const at::cuda::OptionalCUDAGuard device_guard(device_of(tensor));

    void* gpu_ptr = tensor.data_ptr();
    size_t size = tensor.numel() * tensor.element_size();

    // Allocate aligned host buffer
    void* host_buffer = nullptr;
    int ret = posix_memalign(&host_buffer, 4096, size);
    TORCH_CHECK(ret == 0, "Failed to allocate aligned buffer");

    // Copy from GPU to host
    cudaError_t err = cudaMemcpy(host_buffer, gpu_ptr, size, cudaMemcpyDeviceToHost);
    TORCH_CHECK(err == cudaSuccess, "CUDA memcpy failed");

    // Write to NVMe
    int fd = open(device_path.c_str(), O_WRONLY | O_DIRECT);
    TORCH_CHECK(fd >= 0, "Failed to open device for writing");

    ssize_t bytes_written = pwrite(fd, host_buffer, size, offset);
    close(fd);
    free(host_buffer);

    TORCH_CHECK(bytes_written == (ssize_t)size, "Write failed");

    return bytes_written;
}

/**
 * @brief Dictionary-based tensor loader for structured NVMe data
 *
 * Manages multiple "kinds" of data (e.g., different expert weights, layers)
 * Each kind has a base LBA, length, and can be accessed by index.
 */
class TensorNVMeReader {
private:
    std::string device_path_;

    struct KindInfo {
        int64_t start_lba;
        int64_t length;         // Number of items
        int64_t sector_size;
        int64_t item_size_bytes;  // Size of one item
        at::ScalarType dtype;
        std::vector<int64_t> item_shape;
    };

    std::map<int, KindInfo> kinds_;

public:
    /**
     * @brief Constructor
     * @param device_path Path to NVMe device
     */
    explicit TensorNVMeReader(const std::string& device_path)
        : device_path_(device_path) {}

    /**
     * @brief Add a data kind
     *
     * @param kind_id     Unique identifier for this kind
     * @param start_lba   Starting LBA for this kind
     * @param length      Number of items of this kind
     * @param sector_size Bytes per sector
     * @param item_shape  Shape of each item
     * @param dtype       Data type
     */
    void add_kind(
        int kind_id,
        int64_t start_lba,
        int64_t length,
        int64_t sector_size,
        at::IntArrayRef item_shape,
        at::ScalarType dtype
    ) {
        // Calculate item size
        int64_t num_elements = 1;
        for (auto dim : item_shape) {
            num_elements *= dim;
        }
        int64_t item_size_bytes = num_elements * at::elementSize(dtype);

        KindInfo info;
        info.start_lba = start_lba;
        info.length = length;
        info.sector_size = sector_size;
        info.item_size_bytes = item_size_bytes;
        info.dtype = dtype;
        info.item_shape = std::vector<int64_t>(item_shape.begin(), item_shape.end());

        kinds_[kind_id] = info;
    }

    /**
     * @brief Read items of a specific kind
     *
     * @param kind_id Kind identifier
     * @param idx     Starting index within kind
     * @param count   Number of items to read
     * @return Tensor [count, *item_shape]
     */
    at::Tensor read_kind(int kind_id, int64_t idx, int64_t count) {
        TORCH_CHECK(kinds_.count(kind_id), "Unknown kind_id: ", kind_id);

        const auto& info = kinds_[kind_id];
        TORCH_CHECK(idx >= 0 && idx + count <= info.length,
                    "Index out of range: idx=", idx, ", count=", count,
                    ", length=", info.length);

        // Calculate offset
        int64_t item_offset_lba = info.start_lba + (idx * info.item_size_bytes) / info.sector_size;
        int64_t byte_offset = item_offset_lba * info.sector_size;
        int64_t read_size = count * info.item_size_bytes;

        // Build output shape: [count, *item_shape]
        std::vector<int64_t> output_shape;
        output_shape.push_back(count);
        output_shape.insert(output_shape.end(), info.item_shape.begin(), info.item_shape.end());

        // Read tensor
        return read_tensor(device_path_, byte_offset, output_shape, info.dtype);
    }

    /**
     * @brief Get number of items for a kind
     */
    int64_t get_kind_length(int kind_id) const {
        TORCH_CHECK(kinds_.count(kind_id), "Unknown kind_id: ", kind_id);
        return kinds_.at(kind_id).length;
    }
};

//
// Python bindings
//

PYBIND11_MODULE(TORCH_EXTENSION_NAME, m) {
    m.doc() = "NVMe tensor loading utilities for PyTorch";

    // Standalone functions
    m.def("read_tensor", &read_tensor,
          "Read NVMe data into new tensor",
          py::arg("device_path"),
          py::arg("offset"),
          py::arg("shape"),
          py::arg("dtype") = at::kFloat);

    m.def("read_into_tensor", &read_into_tensor,
          "Read NVMe data into existing tensor",
          py::arg("tensor"),
          py::arg("device_path"),
          py::arg("offset"),
          py::arg("size"));

    m.def("write_tensor", &write_tensor,
          "Write tensor to NVMe",
          py::arg("tensor"),
          py::arg("device_path"),
          py::arg("offset"));

    // TensorNVMeReader class
    py::class_<TensorNVMeReader>(m, "TensorNVMeReader")
        .def(py::init<const std::string&>(),
             py::arg("device_path"))
        .def("add_kind", &TensorNVMeReader::add_kind,
             "Add a data kind",
             py::arg("kind_id"),
             py::arg("start_lba"),
             py::arg("length"),
             py::arg("sector_size"),
             py::arg("item_shape"),
             py::arg("dtype") = at::kFloat)
        .def("read_kind", &TensorNVMeReader::read_kind,
             "Read items of a specific kind",
             py::arg("kind_id"),
             py::arg("idx"),
             py::arg("count"))
        .def("get_kind_length", &TensorNVMeReader::get_kind_length,
             "Get number of items for a kind",
             py::arg("kind_id"));
}

} // namespace attention_expert
