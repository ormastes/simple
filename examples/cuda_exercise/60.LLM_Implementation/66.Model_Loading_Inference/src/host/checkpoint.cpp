/**
 * @file checkpoint.cpp
 * @brief Binary checkpoint save/load for LLM model persistence
 *
 * Implements a simple binary checkpoint format for saving and restoring
 * model weights. The format stores a magic number, version, tensor count,
 * tensor metadata, and raw float data for fast sequential I/O.
 *
 * File layout:
 *   [4B magic][4B version][4B num_tensors][8B total_bytes]
 *   [tensor metadata (name_len, name, ndims, shape, offset, num_elements) x N]
 *   [contiguous float data]
 */

#include "common/checkpoint.h"
#include <cuda_runtime.h>
#include <cstdio>
#include <cstring>

namespace llm {

/// Magic number identifying LLMC checkpoint files
static constexpr uint32_t CHECKPOINT_MAGIC = 0x4C4C4D43;  // "LLMC"
/// Current checkpoint format version
static constexpr uint32_t CHECKPOINT_VERSION = 1;

/**
 * @brief Save model weights to a binary checkpoint file
 *
 * Copies all parameters from device to host, then writes the header
 * and data to disk in a single sequential pass.
 */
bool save_checkpoint(const std::string& filepath,
                     const float* d_params,
                     const std::vector<TensorMeta>& tensors) {
    FILE* fp = fopen(filepath.c_str(), "wb");
    if (!fp) {
        fprintf(stderr, "Error: Cannot open %s for writing\n", filepath.c_str());
        return false;
    }

    // Compute total parameter count
    int64_t total_elements = 0;
    for (const auto& t : tensors) {
        total_elements += t.num_elements;
    }
    int64_t total_bytes = total_elements * sizeof(float);

    // Write header
    uint32_t magic = CHECKPOINT_MAGIC;
    uint32_t version = CHECKPOINT_VERSION;
    uint32_t num_tensors = static_cast<uint32_t>(tensors.size());

    fwrite(&magic, sizeof(uint32_t), 1, fp);
    fwrite(&version, sizeof(uint32_t), 1, fp);
    fwrite(&num_tensors, sizeof(uint32_t), 1, fp);
    fwrite(&total_bytes, sizeof(int64_t), 1, fp);

    // Write tensor metadata
    for (const auto& t : tensors) {
        uint32_t name_len = static_cast<uint32_t>(t.name.size());
        fwrite(&name_len, sizeof(uint32_t), 1, fp);
        fwrite(t.name.c_str(), 1, name_len, fp);

        uint32_t ndims = static_cast<uint32_t>(t.shape.size());
        fwrite(&ndims, sizeof(uint32_t), 1, fp);
        fwrite(t.shape.data(), sizeof(int64_t), ndims, fp);

        fwrite(&t.offset, sizeof(int64_t), 1, fp);
        fwrite(&t.num_elements, sizeof(int64_t), 1, fp);
    }

    // Copy parameters from device to host and write
    std::vector<float> h_params(total_elements);
    cudaMemcpy(h_params.data(), d_params, total_bytes, cudaMemcpyDeviceToHost);

    size_t written = fwrite(h_params.data(), sizeof(float), total_elements, fp);
    fclose(fp);

    return (written == static_cast<size_t>(total_elements));
}

/**
 * @brief Load model weights from a binary checkpoint file
 *
 * Reads and validates the header, parses tensor metadata, then loads
 * the float data into the device buffer.
 */
bool load_checkpoint(const std::string& filepath,
                     float* d_params,
                     std::vector<TensorMeta>& tensors) {
    FILE* fp = fopen(filepath.c_str(), "rb");
    if (!fp) {
        fprintf(stderr, "Error: Cannot open %s for reading\n", filepath.c_str());
        return false;
    }

    // Read and validate header
    uint32_t magic, version, num_tensors;
    int64_t total_bytes;

    fread(&magic, sizeof(uint32_t), 1, fp);
    if (magic != CHECKPOINT_MAGIC) {
        fprintf(stderr, "Error: Invalid checkpoint magic number\n");
        fclose(fp);
        return false;
    }

    fread(&version, sizeof(uint32_t), 1, fp);
    if (version != CHECKPOINT_VERSION) {
        fprintf(stderr, "Error: Unsupported checkpoint version %u\n", version);
        fclose(fp);
        return false;
    }

    fread(&num_tensors, sizeof(uint32_t), 1, fp);
    fread(&total_bytes, sizeof(int64_t), 1, fp);

    // Read tensor metadata
    tensors.resize(num_tensors);
    for (uint32_t i = 0; i < num_tensors; i++) {
        uint32_t name_len;
        fread(&name_len, sizeof(uint32_t), 1, fp);

        std::vector<char> name_buf(name_len + 1, 0);
        fread(name_buf.data(), 1, name_len, fp);
        tensors[i].name = std::string(name_buf.data(), name_len);

        uint32_t ndims;
        fread(&ndims, sizeof(uint32_t), 1, fp);
        tensors[i].shape.resize(ndims);
        fread(tensors[i].shape.data(), sizeof(int64_t), ndims, fp);

        fread(&tensors[i].offset, sizeof(int64_t), 1, fp);
        fread(&tensors[i].num_elements, sizeof(int64_t), 1, fp);
    }

    // Read tensor data to host then copy to device
    int64_t total_elements = total_bytes / sizeof(float);
    std::vector<float> h_params(total_elements);
    size_t read_count = fread(h_params.data(), sizeof(float), total_elements, fp);
    fclose(fp);

    if (read_count != static_cast<size_t>(total_elements)) {
        fprintf(stderr, "Error: Incomplete read (%zu / %lld elements)\n",
                read_count, static_cast<long long>(total_elements));
        return false;
    }

    cudaMemcpy(d_params, h_params.data(), total_bytes, cudaMemcpyHostToDevice);
    return true;
}

/**
 * @brief Get total parameter count without loading data
 */
int64_t get_checkpoint_param_count(const std::string& filepath) {
    FILE* fp = fopen(filepath.c_str(), "rb");
    if (!fp) return -1;

    uint32_t magic, version, num_tensors;
    int64_t total_bytes;

    fread(&magic, sizeof(uint32_t), 1, fp);
    if (magic != CHECKPOINT_MAGIC) {
        fclose(fp);
        return -1;
    }

    fread(&version, sizeof(uint32_t), 1, fp);
    fread(&num_tensors, sizeof(uint32_t), 1, fp);
    fread(&total_bytes, sizeof(int64_t), 1, fp);
    fclose(fp);

    return total_bytes / sizeof(float);
}

} // namespace llm
