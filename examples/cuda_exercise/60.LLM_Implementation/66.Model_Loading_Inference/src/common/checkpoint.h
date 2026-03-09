/**
 * @file checkpoint.h
 * @brief Checkpoint save/load interface for LLM model persistence
 *
 * Provides binary checkpoint serialization for saving and restoring
 * model weights during training. The binary format stores a header
 * with tensor metadata followed by raw float data for fast I/O.
 */

#ifndef CHECKPOINT_H
#define CHECKPOINT_H

#include <cuda_runtime.h>
#include <string>
#include <vector>
#include <cstdint>

namespace llm {

/**
 * @brief Metadata for a single tensor in a checkpoint
 *
 * Stores the name, shape, and data offset for locating tensor data
 * within a binary checkpoint file.
 */
struct TensorMeta {
    std::string name;              ///< Tensor name (e.g., "layer.0.attention.W_Q")
    std::vector<int64_t> shape;    ///< Tensor dimensions
    int64_t offset;                ///< Byte offset into data section
    int64_t num_elements;          ///< Total number of float elements

    /**
     * @brief Compute total number of elements from shape
     * @return Product of all dimensions
     */
    int64_t compute_num_elements() const {
        int64_t n = 1;
        for (auto dim : shape) n *= dim;
        return n;
    }
};

/**
 * @brief Checkpoint header containing all tensor metadata
 *
 * Stored at the beginning of a checkpoint file, followed by
 * contiguous tensor data in the order listed.
 */
struct CheckpointHeader {
    uint32_t magic;                  ///< Magic number for format validation (0x4C4C4D43 = "LLMC")
    uint32_t version;                ///< Format version number
    uint32_t num_tensors;            ///< Number of tensors in checkpoint
    int64_t total_bytes;             ///< Total size of tensor data in bytes
    std::vector<TensorMeta> tensors; ///< Metadata for each tensor
};

/**
 * @brief Save model weights to a binary checkpoint file
 *
 * Writes a checkpoint header followed by contiguous tensor data.
 * Tensors are copied from device to host before writing. The format
 * is simple and fast but not portable across architectures.
 *
 * @param filepath     Output file path
 * @param d_params     Device pointer to flat parameter buffer [total_params]
 * @param tensors      Tensor metadata describing the parameter layout
 * @return true on success, false on I/O error
 */
bool save_checkpoint(const std::string& filepath,
                     const float* d_params,
                     const std::vector<TensorMeta>& tensors);

/**
 * @brief Load model weights from a binary checkpoint file
 *
 * Reads the checkpoint header, validates it, then loads tensor data
 * into the provided device buffer. The caller must ensure the buffer
 * is large enough to hold all tensor data.
 *
 * @param filepath     Input file path
 * @param d_params     Device pointer to flat parameter buffer [total_params]
 * @param tensors      Output: populated tensor metadata
 * @return true on success, false on I/O or validation error
 */
bool load_checkpoint(const std::string& filepath,
                     float* d_params,
                     std::vector<TensorMeta>& tensors);

/**
 * @brief Get total parameter count from checkpoint file without loading data
 *
 * Reads only the header to determine the total number of float parameters.
 *
 * @param filepath  Checkpoint file path
 * @return Total number of float parameters, or -1 on error
 */
int64_t get_checkpoint_param_count(const std::string& filepath);

} // namespace llm

#endif // CHECKPOINT_H
