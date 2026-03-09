/**
 * @file nvme_tensor_loader_proper.cpp
 * @brief PROPER NVMe tensor loading using Module 58 filesystem API
 *
 * This implementation correctly uses Module 58's filesystem API instead of
 * bypassing it with direct POSIX I/O. It demonstrates the proper architectural
 * layering where Module 59 builds on top of Module 58.
 *
 * @author Proper Implementation
 * @date 2025-11-20
 */

#include <torch/extension.h>
#include <c10/cuda/CUDAGuard.h>
#include <cuda_runtime.h>

// Module 58: Filesystem API
#include "nvme_simple_fs.h"
#include "nvme_simple_fs_c_api.h"

// Module 53: Device management (for initialization)
#include "mapper/mapper_host.h"
#include "device/device_detector.h"
#include "utils/nvme_config.h"

#include <memory>
#include <map>
#include <string>
#include <sstream>
#include <vector>

namespace attention_expert_proper {

/**
 * @brief Tensor storage backend using Module 58 filesystem
 *
 * This class properly uses Module 58's filesystem API to store and retrieve
 * tensors as files, instead of bypassing the filesystem with raw device I/O.
 */
class TensorFilesystemStorage {
private:
    std::unique_ptr<nvme_fs::NvmeSimpleFilesystem> fs_;
    NvmeDevice* nvme_device_;
    std::string mount_point_;

    /**
     * @brief Generate filename for tensor storage
     */
    std::string tensor_filename(const std::string& name, int index = -1) {
        std::stringstream ss;
        ss << "tensor_" << name;
        if (index >= 0) {
            ss << "_" << index;
        }
        ss << ".bin";
        return ss.str();
    }

public:
    /**
     * @brief Constructor using Module 58 filesystem
     *
     * @param device_config NVMe device configuration from Module 53
     * @param fs_size_lbas Size of filesystem in logical blocks
     */
    TensorFilesystemStorage(
        const nvme::DeviceConfig& device_config,
        uint64_t fs_size_lbas = 100000
    ) : mount_point_("nvme_tensors") {

        // Step 1: Open NVMe device using Module 53
        nvme_device_ = nvme_open(
            device_config.bdf.c_str(),
            16,  // Queue depth
            64,  // Completion queue size
            device_config.lba_size
        );

        if (!nvme_device_) {
            throw std::runtime_error("Failed to open NVMe device: " + device_config.bdf);
        }

        // Step 2: Create filesystem using Module 58
        uint64_t start_lba = device_config.slba + 1000;  // Reserve first 1000 LBAs

        fs_ = nvme_fs::create_filesystem(
            nvme_device_,
            start_lba,
            fs_size_lbas,
            device_config.lba_size
        );

        if (!fs_) {
            nvme_close(nvme_device_);
            throw std::runtime_error("Failed to create filesystem on NVMe device");
        }

        // Log filesystem info
        uint64_t total, used, free;
        fs_->get_stats(total, used, free);
        std::cout << "[TensorFS] Initialized: Total=" << total
                  << " Used=" << used << " Free=" << free << " bytes" << std::endl;
    }

    /**
     * @brief Destructor - cleanup filesystem and device
     */
    ~TensorFilesystemStorage() {
        if (fs_) {
            fs_.reset();
        }
        if (nvme_device_) {
            nvme_close(nvme_device_);
        }
    }

    /**
     * @brief Save tensor to filesystem using Module 58
     *
     * @param tensor PyTorch tensor to save
     * @param name Name for the tensor file
     * @param index Optional index for tensor arrays
     * @return File ID from Module 58
     */
    uint32_t save_tensor(
        const at::Tensor& tensor,
        const std::string& name,
        int index = -1
    ) {
        TORCH_CHECK(tensor.is_contiguous(), "Tensor must be contiguous");

        std::string filename = tensor_filename(name, index);
        size_t size_bytes = tensor.numel() * tensor.element_size();

        // Handle CUDA tensors
        void* data_ptr = nullptr;
        std::unique_ptr<uint8_t[]> host_buffer;

        if (tensor.is_cuda()) {
            // Copy from GPU to host
            host_buffer = std::make_unique<uint8_t[]>(size_bytes);
            cudaError_t err = cudaMemcpy(
                host_buffer.get(),
                tensor.data_ptr(),
                size_bytes,
                cudaMemcpyDeviceToHost
            );
            TORCH_CHECK(err == cudaSuccess, "CUDA memcpy failed: ", cudaGetErrorString(err));
            data_ptr = host_buffer.get();
        } else {
            // CPU tensor - use directly
            data_ptr = tensor.data_ptr();
        }

        // Use Module 58's filesystem API to save the file
        uint32_t file_id = fs_->save_file(filename, data_ptr, size_bytes);

        if (file_id == 0) {
            throw std::runtime_error("Failed to save tensor to filesystem: " + filename);
        }

        // Store metadata
        nvme_fs::FileMetadata metadata;
        metadata.name = filename;
        metadata.id = file_id;
        metadata.size_bytes = size_bytes;
        metadata.user_data1 = static_cast<uint64_t>(tensor.scalar_type());
        metadata.user_data2 = tensor.dim();

        std::cout << "[TensorFS] Saved tensor '" << name
                  << "' as file " << filename
                  << " (ID=" << file_id << ", size=" << size_bytes << ")" << std::endl;

        return file_id;
    }

    /**
     * @brief Load tensor from filesystem using Module 58
     *
     * @param name Name of the tensor file
     * @param index Optional index for tensor arrays
     * @param dtype Expected data type
     * @param shape Expected tensor shape
     * @param device Target device (CPU or CUDA)
     * @return Loaded tensor
     */
    at::Tensor load_tensor(
        const std::string& name,
        int index,
        at::ScalarType dtype,
        at::IntArrayRef shape,
        at::Device device = at::kCUDA
    ) {
        std::string filename = tensor_filename(name, index);

        // Get file info
        auto files = fs_->list_files();
        nvme_fs::FileMetadata* file_meta = nullptr;

        for (auto& file : files) {
            if (file.name == filename) {
                file_meta = &file;
                break;
            }
        }

        if (!file_meta) {
            throw std::runtime_error("Tensor file not found: " + filename);
        }

        // Calculate expected size
        int64_t num_elements = 1;
        for (auto dim : shape) {
            num_elements *= dim;
        }
        size_t expected_size = num_elements * at::elementSize(dtype);

        TORCH_CHECK(file_meta->size_bytes == expected_size,
                    "Size mismatch: file has ", file_meta->size_bytes,
                    " bytes, expected ", expected_size);

        // Allocate host buffer for reading
        std::unique_ptr<uint8_t[]> host_buffer = std::make_unique<uint8_t[]>(expected_size);

        // Use Module 58's filesystem API to read the file
        size_t bytes_read = fs_->read_file(
            filename,
            host_buffer.get(),
            expected_size
        );

        TORCH_CHECK(bytes_read == expected_size,
                    "Read size mismatch: got ", bytes_read,
                    " bytes, expected ", expected_size);

        // Create tensor
        auto options = at::TensorOptions()
            .dtype(dtype)
            .device(device)
            .requires_grad(false);

        at::Tensor tensor = at::empty(shape, options);

        // Copy data to tensor
        if (device.is_cuda()) {
            // Copy from host to GPU
            cudaError_t err = cudaMemcpy(
                tensor.data_ptr(),
                host_buffer.get(),
                expected_size,
                cudaMemcpyHostToDevice
            );
            TORCH_CHECK(err == cudaSuccess, "CUDA memcpy failed: ", cudaGetErrorString(err));
        } else {
            // CPU tensor - copy directly
            std::memcpy(tensor.data_ptr(), host_buffer.get(), expected_size);
        }

        std::cout << "[TensorFS] Loaded tensor '" << name
                  << "' from file " << filename
                  << " (" << bytes_read << " bytes)" << std::endl;

        return tensor;
    }

    /**
     * @brief Delete tensor from filesystem
     *
     * @param name Name of the tensor file
     * @param index Optional index for tensor arrays
     */
    void delete_tensor(const std::string& name, int index = -1) {
        std::string filename = tensor_filename(name, index);
        fs_->delete_file(filename);
        std::cout << "[TensorFS] Deleted tensor file: " << filename << std::endl;
    }

    /**
     * @brief List all stored tensors
     *
     * @return Vector of tensor filenames
     */
    std::vector<std::string> list_tensors() {
        auto files = fs_->list_files();
        std::vector<std::string> tensor_files;

        for (const auto& file : files) {
            if (file.name.find("tensor_") == 0) {
                tensor_files.push_back(file.name);
            }
        }

        return tensor_files;
    }

    /**
     * @brief Get filesystem statistics
     */
    void print_stats() {
        uint64_t total, used, free;
        fs_->get_stats(total, used, free);

        std::cout << "[TensorFS] Statistics:" << std::endl;
        std::cout << "  Total: " << total << " bytes" << std::endl;
        std::cout << "  Used:  " << used << " bytes" << std::endl;
        std::cout << "  Free:  " << free << " bytes" << std::endl;

        auto files = list_tensors();
        std::cout << "  Tensors: " << files.size() << " files" << std::endl;
    }
};

/**
 * @brief Expert weight manager using Module 58 filesystem
 *
 * This class demonstrates how to properly manage expert weights in a mixture
 * of experts model using Module 58's filesystem for storage and retrieval.
 */
class ExpertWeightManager {
private:
    std::shared_ptr<TensorFilesystemStorage> storage_;
    int num_experts_;
    std::vector<int64_t> weight_shape_;
    at::ScalarType dtype_;

public:
    /**
     * @brief Constructor
     *
     * @param storage Tensor filesystem storage backend
     * @param num_experts Number of experts
     * @param weight_shape Shape of each expert's weights
     * @param dtype Data type for weights
     */
    ExpertWeightManager(
        std::shared_ptr<TensorFilesystemStorage> storage,
        int num_experts,
        at::IntArrayRef weight_shape,
        at::ScalarType dtype = at::kFloat
    ) : storage_(storage),
        num_experts_(num_experts),
        weight_shape_(weight_shape.begin(), weight_shape.end()),
        dtype_(dtype) {}

    /**
     * @brief Save expert weights to filesystem
     *
     * @param expert_id Expert index
     * @param weights Weight tensor
     */
    void save_expert_weights(int expert_id, const at::Tensor& weights) {
        TORCH_CHECK(expert_id >= 0 && expert_id < num_experts_,
                    "Invalid expert_id: ", expert_id);

        storage_->save_tensor(weights, "expert_weights", expert_id);
    }

    /**
     * @brief Load expert weights from filesystem
     *
     * @param expert_id Expert index
     * @param device Target device
     * @return Weight tensor
     */
    at::Tensor load_expert_weights(int expert_id, at::Device device = at::kCUDA) {
        TORCH_CHECK(expert_id >= 0 && expert_id < num_experts_,
                    "Invalid expert_id: ", expert_id);

        return storage_->load_tensor(
            "expert_weights",
            expert_id,
            dtype_,
            weight_shape_,
            device
        );
    }

    /**
     * @brief Load multiple experts in batch
     *
     * @param expert_ids Vector of expert indices
     * @param device Target device
     * @return Stacked tensor [num_experts, *weight_shape]
     */
    at::Tensor load_expert_batch(
        const std::vector<int>& expert_ids,
        at::Device device = at::kCUDA
    ) {
        std::vector<at::Tensor> weights;
        weights.reserve(expert_ids.size());

        for (int expert_id : expert_ids) {
            weights.push_back(load_expert_weights(expert_id, device));
        }

        return at::stack(weights, 0);
    }
};

//
// Python bindings using Module 58 properly
//

PYBIND11_MODULE(TORCH_EXTENSION_NAME, m) {
    m.doc() = "PROPER NVMe tensor loading using Module 58 filesystem API";

    // TensorFilesystemStorage class
    py::class_<TensorFilesystemStorage, std::shared_ptr<TensorFilesystemStorage>>(
        m, "TensorFilesystemStorage"
    )
        .def(py::init([](const std::string& bdf, uint32_t nsid,
                         uint32_t lba_size, uint64_t slba, uint64_t fs_size) {
            nvme::DeviceConfig config;
            config.bdf = bdf;
            config.nsid = nsid;
            config.lba_size = lba_size;
            config.slba = slba;
            return std::make_shared<TensorFilesystemStorage>(config, fs_size);
        }),
            "Create tensor storage using Module 58 filesystem",
            py::arg("bdf"),
            py::arg("nsid") = 1,
            py::arg("lba_size") = 512,
            py::arg("slba") = 0,
            py::arg("fs_size_lbas") = 100000)

        .def("save_tensor", &TensorFilesystemStorage::save_tensor,
            "Save tensor to filesystem",
            py::arg("tensor"),
            py::arg("name"),
            py::arg("index") = -1)

        .def("load_tensor",
            [](TensorFilesystemStorage& self,
               const std::string& name,
               int index,
               at::ScalarType dtype,
               py::tuple shape,
               const std::string& device_str) {
                std::vector<int64_t> shape_vec;
                for (auto item : shape) {
                    shape_vec.push_back(item.cast<int64_t>());
                }
                at::Device device(device_str);
                return self.load_tensor(name, index, dtype, shape_vec, device);
            },
            "Load tensor from filesystem",
            py::arg("name"),
            py::arg("index") = -1,
            py::arg("dtype") = at::kFloat,
            py::arg("shape"),
            py::arg("device") = "cuda")

        .def("delete_tensor", &TensorFilesystemStorage::delete_tensor,
            "Delete tensor from filesystem",
            py::arg("name"),
            py::arg("index") = -1)

        .def("list_tensors", &TensorFilesystemStorage::list_tensors,
            "List all stored tensors")

        .def("print_stats", &TensorFilesystemStorage::print_stats,
            "Print filesystem statistics");

    // ExpertWeightManager class
    py::class_<ExpertWeightManager>(m, "ExpertWeightManager")
        .def(py::init<std::shared_ptr<TensorFilesystemStorage>, int,
                      at::IntArrayRef, at::ScalarType>(),
            "Create expert weight manager",
            py::arg("storage"),
            py::arg("num_experts"),
            py::arg("weight_shape"),
            py::arg("dtype") = at::kFloat)

        .def("save_expert_weights", &ExpertWeightManager::save_expert_weights,
            "Save expert weights",
            py::arg("expert_id"),
            py::arg("weights"))

        .def("load_expert_weights",
            [](ExpertWeightManager& self, int expert_id, const std::string& device_str) {
                at::Device device(device_str);
                return self.load_expert_weights(expert_id, device);
            },
            "Load expert weights",
            py::arg("expert_id"),
            py::arg("device") = "cuda")

        .def("load_expert_batch",
            [](ExpertWeightManager& self,
               const std::vector<int>& expert_ids,
               const std::string& device_str) {
                at::Device device(device_str);
                return self.load_expert_batch(expert_ids, device);
            },
            "Load multiple experts",
            py::arg("expert_ids"),
            py::arg("device") = "cuda");
}

} // namespace attention_expert_proper
