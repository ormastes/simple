/**
 * @file safetensors.h
 * @brief SafeTensors format parser for loading HuggingFace models
 *
 * Implements parsing of the SafeTensors file format used by HuggingFace
 * for model distribution. SafeTensors uses a JSON header followed by
 * memory-mapped tensor data for zero-copy loading.
 *
 * Format: [8-byte header_size][JSON header][tensor data...]
 */

#ifndef SAFETENSORS_H
#define SAFETENSORS_H

#include <string>
#include <vector>
#include <unordered_map>
#include <cstdint>

namespace llm {

/**
 * @brief Data types supported by SafeTensors format
 */
enum class SafeTensorsDtype {
    F16,    ///< 16-bit floating point (half precision)
    BF16,   ///< Brain floating point 16
    F32,    ///< 32-bit floating point (single precision)
    F64,    ///< 64-bit floating point (double precision)
    I32,    ///< 32-bit integer
    I64,    ///< 64-bit integer
    BOOL,   ///< Boolean
    U8      ///< Unsigned 8-bit integer
};

/**
 * @brief Metadata for a single tensor in a SafeTensors file
 *
 * Parsed from the JSON header, contains the tensor name, data type,
 * shape, and byte offsets into the data section.
 */
struct SafeTensorInfo {
    std::string name;              ///< Tensor name (e.g., "model.layers.0.self_attn.q_proj.weight")
    SafeTensorsDtype dtype;        ///< Data type
    std::vector<int64_t> shape;    ///< Tensor dimensions
    int64_t data_offset_begin;     ///< Start byte offset into data section
    int64_t data_offset_end;       ///< End byte offset into data section

    /**
     * @brief Get the size of this tensor's data in bytes
     * @return data_offset_end - data_offset_begin
     */
    int64_t byte_size() const {
        return data_offset_end - data_offset_begin;
    }

    /**
     * @brief Get the number of elements in this tensor
     * @return Product of all shape dimensions
     */
    int64_t num_elements() const {
        int64_t n = 1;
        for (auto dim : shape) n *= dim;
        return n;
    }
};

/**
 * @brief Parsed SafeTensors file header
 *
 * Contains metadata for all tensors plus any file-level metadata
 * (e.g., model format version).
 */
struct SafeTensorsHeader {
    int64_t header_size;                           ///< Size of JSON header in bytes
    std::vector<SafeTensorInfo> tensors;            ///< Tensor metadata list
    std::unordered_map<std::string, std::string> metadata;  ///< File-level metadata
};

/**
 * @brief Parse a SafeTensors file header
 *
 * Reads the 8-byte header size prefix, then parses the JSON header
 * to extract tensor metadata. Does not read tensor data.
 *
 * @param filepath  Path to .safetensors file
 * @param header    Output: parsed header with tensor metadata
 * @return true on success, false on parse error
 *
 * @note This only reads the header; tensor data is loaded separately
 *       via load_safetensor_data() or memory mapping
 */
bool parse_safetensors(const std::string& filepath, SafeTensorsHeader& header);

/**
 * @brief Load a specific tensor from a SafeTensors file into device memory
 *
 * Reads the raw bytes for the specified tensor and copies them to GPU.
 * Handles dtype conversion from F16/BF16 to F32 if needed.
 *
 * @param filepath    Path to .safetensors file
 * @param header      Parsed header (from parse_safetensors)
 * @param tensor_name Name of the tensor to load
 * @param d_output    Device buffer for the loaded tensor data (F32)
 * @return true on success, false if tensor not found or I/O error
 */
bool load_safetensor_data(const std::string& filepath,
                          const SafeTensorsHeader& header,
                          const std::string& tensor_name,
                          float* d_output);

/**
 * @brief Memory-map a SafeTensors file for zero-copy tensor access
 *
 * Maps the entire file into memory using mmap for efficient tensor
 * loading without explicit read operations.
 *
 * @param filepath  Path to .safetensors file
 * @param addr      Output: mmap base address
 * @param length    Output: total file size
 * @return true on success, false on mmap error
 */
bool mmap_safetensors(const std::string& filepath, void*& addr, size_t& length);

/**
 * @brief Unmap a previously memory-mapped SafeTensors file
 *
 * @param addr    mmap base address
 * @param length  Total file size
 */
void munmap_safetensors(void* addr, size_t length);

/**
 * @brief Convert SafeTensorsDtype enum to string representation
 * @param dtype Data type
 * @return String name (e.g., "F32", "F16", "BF16")
 */
const char* dtype_to_string(SafeTensorsDtype dtype);

/**
 * @brief Get byte size per element for a given dtype
 * @param dtype Data type
 * @return Bytes per element
 */
int dtype_byte_size(SafeTensorsDtype dtype);

} // namespace llm

#endif // SAFETENSORS_H
