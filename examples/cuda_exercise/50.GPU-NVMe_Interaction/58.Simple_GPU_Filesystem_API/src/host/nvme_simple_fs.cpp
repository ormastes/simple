/**
 * @file nvme_simple_fs.cpp
 * @brief Implementation of simple NVMe filesystem
 *
 * @author Module 58 Developer
 * @date 2025-10-25
 */

#include "nvme_simple_fs.h"
#include "mapper/mapper_host.h"
#include "io/host_io_host_mem.h"
#include <algorithm>
#include <cstring>
#include <chrono>
#include <sstream>
#include <iostream>

namespace nvme_fs {

// Forward declarations for block I/O functions
// These are provided either by:
// 1. Mock implementation in tests (mock_nvme_device.h)
// 2. Real implementation using Module 53 API
void read_blocks(void* nvme_device, std::uint64_t lba, std::uint64_t count, void* buffer);
void write_blocks(void* nvme_device, std::uint64_t lba, std::uint64_t count, const void* buffer);

// ---- Helper functions ----

static std::uint64_t get_current_timestamp() {
    auto now = std::chrono::system_clock::now();
    return std::chrono::duration_cast<std::chrono::seconds>(
        now.time_since_epoch()).count();
}

static std::uint32_t calculate_crc32(const void* data, std::size_t size) {
    // Simple CRC32 implementation; replace with hardware-accelerated CRC if needed
    const std::uint8_t* bytes = static_cast<const std::uint8_t*>(data);
    std::uint32_t crc = 0xFFFFFFFF;
    for (std::size_t i = 0; i < size; ++i) {
        crc ^= bytes[i];
        for (int j = 0; j < 8; ++j) {
            crc = (crc >> 1) ^ (0xEDB88320 & -(crc & 1));
        }
    }
    return ~crc;
}

// ---- NvmeSimpleFilesystem implementation ----

NvmeSimpleFilesystem::NvmeSimpleFilesystem(void* nvme_device,
                                           std::uint64_t start_lba,
                                           std::uint64_t total_blocks,
                                           std::uint64_t block_size)
    : nvme_device_(nvme_device),
      start_lba_(start_lba) {

    superblock_.magic = 0x4E564653;
    superblock_.version = 1;
    superblock_.total_blocks = total_blocks;
    superblock_.block_size = block_size;
    superblock_.metadata_blocks = 64;
    superblock_.default_item_size = block_size;  // Default to block size
    superblock_.next_file_id = 1;
    superblock_.num_files = 0;
    superblock_.num_nodes = 1;

    // Try to read existing magic number first
    std::vector<std::uint8_t> test_buffer(block_size);
    try {
        nvme_fs::read_blocks(nvme_device, start_lba, 1, test_buffer.data());
        std::uint32_t magic;
        std::memcpy(&magic, test_buffer.data(), sizeof(std::uint32_t));

        if (magic == 0x4E564653) {
            // Valid filesystem exists, load it
            load_metadata();
        } else {
            // No valid filesystem, format new one
            std::cerr << "No valid filesystem found, formatting...\n";
            format();
        }
    } catch (const std::exception& e) {
        // Error reading, format new filesystem
        std::cerr << "Error reading device, formatting...\n";
        format();
    }
}

NvmeSimpleFilesystem::~NvmeSimpleFilesystem() {
    try {
        flush_metadata();
    } catch (...) {
        // Ignore errors in destructor
    }
}

void NvmeSimpleFilesystem::format() {
    file_table_.clear();
    node_map_.clear();
    free_list_.clear();

    superblock_.next_file_id = 1;
    superblock_.num_files = 0;
    superblock_.num_nodes = 1;

    // Create one large free node covering entire filesystem
    // (excluding metadata region)
    LbaNode free_node;
    free_node.start_lba = start_lba_ + superblock_.metadata_blocks;
    free_node.length = superblock_.total_blocks - superblock_.metadata_blocks;
    free_node.file_id = 0;
    free_list_.push_back(free_node);

    save_metadata();
}

void NvmeSimpleFilesystem::load_metadata() {
    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device_);

    // Read superblock from first LBA
    std::vector<std::uint8_t> sb_buffer(superblock_.block_size);

    nvme_fs::read_blocks(dev, start_lba_, 1, sb_buffer.data());

    std::memcpy(&superblock_, sb_buffer.data(), sizeof(Superblock));

    // Validate magic number
    if (superblock_.magic != 0x4E564653) {
        throw std::runtime_error("Invalid filesystem magic number");
    }

    // Read file table and node map from subsequent metadata blocks
    std::size_t metadata_size = (superblock_.metadata_blocks - 1) * superblock_.block_size;
    std::vector<std::uint8_t> metadata_buffer(metadata_size);

    nvme_fs::read_blocks(dev, start_lba_ + 1,
                          superblock_.metadata_blocks - 1,
                          metadata_buffer.data());

    // Deserialize file table and nodes (simple serialization)
    // Format: [num_files][FileEntry...][ num_nodes][LbaNode...]
    std::size_t offset = 0;

    std::uint32_t num_files;
    std::memcpy(&num_files, metadata_buffer.data() + offset, sizeof(std::uint32_t));
    offset += sizeof(std::uint32_t);

    for (std::uint32_t i = 0; i < num_files && offset < metadata_size; ++i) {
        FileEntry entry;

        // Read name length
        std::uint16_t name_len;
        std::memcpy(&name_len, metadata_buffer.data() + offset, sizeof(std::uint16_t));
        offset += sizeof(std::uint16_t);

        // Read name
        entry.name.resize(name_len);
        std::memcpy(entry.name.data(), metadata_buffer.data() + offset, name_len);
        offset += name_len;

        // Read entry fields
        std::memcpy(&entry.file_id, metadata_buffer.data() + offset, sizeof(std::uint32_t));
        offset += sizeof(std::uint32_t);
        std::memcpy(&entry.size_bytes, metadata_buffer.data() + offset, sizeof(std::uint64_t));
        offset += sizeof(std::uint64_t);
        std::memcpy(&entry.item_size, metadata_buffer.data() + offset, sizeof(std::uint64_t));
        offset += sizeof(std::uint64_t);
        std::memcpy(&entry.created_time, metadata_buffer.data() + offset, sizeof(std::uint64_t));
        offset += sizeof(std::uint64_t);
        std::memcpy(&entry.modified_time, metadata_buffer.data() + offset, sizeof(std::uint64_t));
        offset += sizeof(std::uint64_t);
        std::memcpy(&entry.checksum, metadata_buffer.data() + offset, sizeof(std::uint32_t));
        offset += sizeof(std::uint32_t);

        file_table_[entry.name] = entry;
    }

    // Read LBA nodes
    std::uint32_t num_nodes;
    std::memcpy(&num_nodes, metadata_buffer.data() + offset, sizeof(std::uint32_t));
    offset += sizeof(std::uint32_t);

    for (std::uint32_t i = 0; i < num_nodes && offset < metadata_size; ++i) {
        LbaNode node;
        std::memcpy(&node, metadata_buffer.data() + offset, sizeof(LbaNode));
        offset += sizeof(LbaNode);

        if (node.is_free()) {
            free_list_.push_back(node);
        } else {
            node_map_[node.file_id] = node;
        }
    }
}

void NvmeSimpleFilesystem::save_metadata() {
    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device_);

    // Sanity check
    if (superblock_.block_size == 0) {
        throw std::runtime_error("Invalid block_size: 0");
    }

    // Write superblock
    std::vector<std::uint8_t> sb_buffer(superblock_.block_size, 0);
    superblock_.num_files = file_table_.size();
    superblock_.num_nodes = node_map_.size() + free_list_.size();
    std::memcpy(sb_buffer.data(), &superblock_, sizeof(Superblock));

    nvme_fs::write_blocks(dev, start_lba_, 1, sb_buffer.data());

    // Serialize file table and nodes
    std::size_t metadata_size = (superblock_.metadata_blocks - 1) * superblock_.block_size;
    std::vector<std::uint8_t> metadata_buffer(metadata_size, 0);
    std::size_t offset = 0;

    // Write file table
    std::uint32_t num_files = file_table_.size();
    std::memcpy(metadata_buffer.data() + offset, &num_files, sizeof(std::uint32_t));
    offset += sizeof(std::uint32_t);

    for (const auto& [name, entry] : file_table_) {
        std::uint16_t name_len = entry.name.size();
        std::memcpy(metadata_buffer.data() + offset, &name_len, sizeof(std::uint16_t));
        offset += sizeof(std::uint16_t);

        std::memcpy(metadata_buffer.data() + offset, entry.name.data(), name_len);
        offset += name_len;

        std::memcpy(metadata_buffer.data() + offset, &entry.file_id, sizeof(std::uint32_t));
        offset += sizeof(std::uint32_t);
        std::memcpy(metadata_buffer.data() + offset, &entry.size_bytes, sizeof(std::uint64_t));
        offset += sizeof(std::uint64_t);
        std::memcpy(metadata_buffer.data() + offset, &entry.item_size, sizeof(std::uint64_t));
        offset += sizeof(std::uint64_t);
        std::memcpy(metadata_buffer.data() + offset, &entry.created_time, sizeof(std::uint64_t));
        offset += sizeof(std::uint64_t);
        std::memcpy(metadata_buffer.data() + offset, &entry.modified_time, sizeof(std::uint64_t));
        offset += sizeof(std::uint64_t);
        std::memcpy(metadata_buffer.data() + offset, &entry.checksum, sizeof(std::uint32_t));
        offset += sizeof(std::uint32_t);
    }

    // Write LBA nodes
    std::uint32_t num_nodes = node_map_.size() + free_list_.size();
    std::memcpy(metadata_buffer.data() + offset, &num_nodes, sizeof(std::uint32_t));
    offset += sizeof(std::uint32_t);

    for (const auto& [file_id, node] : node_map_) {
        std::memcpy(metadata_buffer.data() + offset, &node, sizeof(LbaNode));
        offset += sizeof(LbaNode);
    }

    for (const auto& node : free_list_) {
        std::memcpy(metadata_buffer.data() + offset, &node, sizeof(LbaNode));
        offset += sizeof(LbaNode);
    }

    nvme_fs::write_blocks(dev, start_lba_ + 1,
                           superblock_.metadata_blocks - 1,
                           metadata_buffer.data());
}

void NvmeSimpleFilesystem::flush_metadata() {
    save_metadata();
}

LbaNode NvmeSimpleFilesystem::allocate_space(std::uint64_t size_bytes) {
    // Calculate required blocks
    std::uint64_t required_blocks =
        (size_bytes + superblock_.block_size - 1) / superblock_.block_size;

    // Find first-fit free node
    for (auto it = free_list_.begin(); it != free_list_.end(); ++it) {
        if (it->length >= required_blocks) {
            LbaNode allocated;
            allocated.start_lba = it->start_lba;
            allocated.length = required_blocks;
            allocated.file_id = superblock_.next_file_id++;

            // Update or remove free node
            if (it->length == required_blocks) {
                free_list_.erase(it);
            } else {
                it->start_lba += required_blocks;
                it->length -= required_blocks;
            }

            return allocated;
        }
    }

    throw OutOfSpaceError("Insufficient consecutive space for allocation");
}

void NvmeSimpleFilesystem::free_space(const LbaNode& node) {
    LbaNode free_node = node;
    free_node.file_id = 0;
    free_list_.push_back(free_node);

    // Simple merge: just add to list, garbage_collect() will merge
}

void NvmeSimpleFilesystem::check_bounds(const LbaNode& node,
                                        std::uint64_t offset,
                                        std::size_t size) const {
    std::uint64_t node_size_bytes = node.length * superblock_.block_size;

    if (offset + size > node_size_bytes) {
        std::ostringstream oss;
        oss << "Access violation: trying to access " << size
            << " bytes at offset " << offset
            << " in node of size " << node_size_bytes << " bytes";
        throw AccessViolationError(oss.str());
    }
}

std::uint32_t NvmeSimpleFilesystem::save_file(const std::string& filename,
                                              const void* data,
                                              std::size_t size_bytes,
                                              std::uint64_t item_size) {
    // Check if file already exists
    if (file_table_.find(filename) != file_table_.end()) {
        throw std::runtime_error("File already exists: " + filename);
    }

    // Use default item size if not specified
    if (item_size == 0) {
        item_size = superblock_.default_item_size;
    }

    // Allocate space (rounded to full block granularity)
    LbaNode node = allocate_space(size_bytes);

    const std::uint64_t block_bytes =
        node.length * superblock_.block_size;

    // Prepare aligned buffer for NVMe write. We cannot pass the caller's
    // buffer directly when size_bytes is not block-aligned, otherwise the
    // lower layers would read past the valid range.
    std::vector<std::uint8_t> aligned_buffer(block_bytes, 0);
    std::memcpy(aligned_buffer.data(), data, size_bytes);

    // Write data to NVMe
    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device_);
    nvme_fs::write_blocks(dev, node.start_lba, node.length, aligned_buffer.data());

    // Create file entry
    FileEntry entry;
    entry.name = filename;
    entry.file_id = node.file_id;
    entry.size_bytes = size_bytes;
    entry.item_size = item_size;
    entry.created_time = get_current_timestamp();
    entry.modified_time = entry.created_time;
    entry.checksum = calculate_crc32(data, size_bytes);

    file_table_[filename] = entry;
    node_map_[node.file_id] = node;

    save_metadata();

    return node.file_id;
}

std::size_t NvmeSimpleFilesystem::read_file(const std::string& filename,
                                            void* buffer,
                                            std::size_t buffer_size) {
    auto it = file_table_.find(filename);
    if (it == file_table_.end()) {
        throw FileNotFoundError("File not found: " + filename);
    }

    const FileEntry& entry = it->second;
    if (buffer_size < entry.size_bytes) {
        throw std::runtime_error("Buffer too small for file");
    }

    LbaNode node = node_map_.at(entry.file_id);

    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device_);
    nvme_fs::read_blocks(dev, node.start_lba, node.length, buffer);

    return entry.size_bytes;
}

void NvmeSimpleFilesystem::write_file(const std::string& filename,
                                      std::uint64_t offset,
                                      const void* data,
                                      std::size_t size_bytes) {
    auto it = file_table_.find(filename);
    if (it == file_table_.end()) {
        throw FileNotFoundError("File not found: " + filename);
    }

    FileEntry& entry = it->second;
    if (offset + size_bytes > entry.size_bytes) {
        throw AccessViolationError("Write exceeds file size");
    }

    LbaNode node = node_map_.at(entry.file_id);

    // Calculate LBA offset
    std::uint64_t lba_offset = offset / superblock_.block_size;
    std::uint64_t byte_offset_in_block = offset % superblock_.block_size;

    // For simplicity, read-modify-write if not block-aligned
    // In production, optimize for aligned writes
    std::uint64_t write_blocks =
        (byte_offset_in_block + size_bytes + superblock_.block_size - 1)
        / superblock_.block_size;

    std::vector<std::uint8_t> temp_buffer(write_blocks * superblock_.block_size);

    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device_);

    // Read existing data
    nvme_fs::read_blocks(dev, node.start_lba + lba_offset,
                          write_blocks, temp_buffer.data());

    // Modify
    std::memcpy(temp_buffer.data() + byte_offset_in_block, data, size_bytes);

    // Write back
    nvme_fs::write_blocks(dev, node.start_lba + lba_offset,
                           write_blocks, temp_buffer.data());

    entry.modified_time = get_current_timestamp();
    save_metadata();
}

bool NvmeSimpleFilesystem::delete_file(const std::string& filename) {
    auto it = file_table_.find(filename);
    if (it == file_table_.end()) {
        return false;
    }

    std::uint32_t file_id = it->second.file_id;
    LbaNode node = node_map_.at(file_id);

    file_table_.erase(it);
    node_map_.erase(file_id);
    free_space(node);

    save_metadata();
    return true;
}

LbaNode NvmeSimpleFilesystem::get_file_node(const std::string& filename) const {
    auto it = file_table_.find(filename);
    if (it == file_table_.end()) {
        throw FileNotFoundError("File not found: " + filename);
    }

    return node_map_.at(it->second.file_id);
}

FileEntry NvmeSimpleFilesystem::get_file_info(const std::string& filename) const {
    auto it = file_table_.find(filename);
    if (it == file_table_.end()) {
        throw FileNotFoundError("File not found: " + filename);
    }

    return it->second;
}

// ---- Item-based I/O operations ----

std::size_t NvmeSimpleFilesystem::read_items(const std::string& filename,
                                             std::uint64_t item_offset,
                                             std::uint64_t num_items,
                                             void* buffer) {
    auto it = file_table_.find(filename);
    if (it == file_table_.end()) {
        throw FileNotFoundError("File not found: " + filename);
    }

    const FileEntry& entry = it->second;
    const std::uint64_t total_items = entry.num_items();

    // Check bounds
    if (item_offset >= total_items) {
        throw AccessViolationError("Item offset exceeds file size");
    }

    // Adjust num_items if it exceeds file size
    num_items = std::min(num_items, total_items - item_offset);

    const std::uint64_t byte_offset = item_offset * entry.item_size;
    const std::size_t read_size = num_items * entry.item_size;

    LbaNode node = node_map_.at(entry.file_id);
    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device_);

    // Calculate block-aligned read parameters
    const std::uint64_t start_block = byte_offset / superblock_.block_size;
    const std::uint64_t byte_offset_in_block = byte_offset % superblock_.block_size;
    const std::uint64_t blocks_needed =
        (byte_offset_in_block + read_size + superblock_.block_size - 1) / superblock_.block_size;

    // For small items or unaligned reads, use temporary buffer
    if (byte_offset_in_block != 0 || read_size < superblock_.block_size) {
        std::vector<std::uint8_t> temp_buffer(blocks_needed * superblock_.block_size);
        nvme_fs::read_blocks(dev, node.start_lba + start_block, blocks_needed, temp_buffer.data());
        std::memcpy(buffer, temp_buffer.data() + byte_offset_in_block, read_size);
    } else {
        // Direct read for block-aligned access
        nvme_fs::read_blocks(dev, node.start_lba + start_block, blocks_needed, buffer);
    }

    return num_items;
}

void NvmeSimpleFilesystem::write_items(const std::string& filename,
                                       std::uint64_t item_offset,
                                       std::uint64_t num_items,
                                       const void* data) {
    auto it = file_table_.find(filename);
    if (it == file_table_.end()) {
        throw FileNotFoundError("File not found: " + filename);
    }

    FileEntry& entry = it->second;
    const std::uint64_t total_items = entry.num_items();

    // Check bounds
    if (item_offset + num_items > total_items) {
        throw AccessViolationError("Write exceeds file size");
    }

    const std::uint64_t byte_offset = item_offset * entry.item_size;
    const std::size_t write_size = num_items * entry.item_size;

    LbaNode node = node_map_.at(entry.file_id);
    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device_);

    // Calculate block-aligned write parameters
    const std::uint64_t start_block = byte_offset / superblock_.block_size;
    const std::uint64_t byte_offset_in_block = byte_offset % superblock_.block_size;
    const std::uint64_t blocks_needed =
        (byte_offset_in_block + write_size + superblock_.block_size - 1) / superblock_.block_size;

    // For small items or unaligned writes, use read-modify-write
    if (byte_offset_in_block != 0 ||
        (write_size % superblock_.block_size) != 0 ||
        write_size < superblock_.block_size) {

        std::vector<std::uint8_t> temp_buffer(blocks_needed * superblock_.block_size);

        // Read existing data
        nvme_fs::read_blocks(dev, node.start_lba + start_block, blocks_needed, temp_buffer.data());

        // Modify
        std::memcpy(temp_buffer.data() + byte_offset_in_block, data, write_size);

        // Write back
        nvme_fs::write_blocks(dev, node.start_lba + start_block, blocks_needed, temp_buffer.data());
    } else {
        // Direct write for block-aligned access
        nvme_fs::write_blocks(dev, node.start_lba + start_block, blocks_needed, data);
    }

    entry.modified_time = get_current_timestamp();
    save_metadata();
}

std::vector<FileEntry> NvmeSimpleFilesystem::list_files() const {
    std::vector<FileEntry> files;
    for (const auto& [name, entry] : file_table_) {
        files.push_back(entry);
    }
    return files;
}

// Template read/write implementations
template<typename T>
void NvmeSimpleFilesystem::read_node_template(const LbaNode& node,
                                              std::uint64_t offset_bytes,
                                              T* buffer,
                                              std::size_t count) {
    std::size_t size_bytes = count * sizeof(T);
    check_bounds(node, offset_bytes, size_bytes);
    read_node(node, offset_bytes, buffer, size_bytes);
}

template<typename T>
void NvmeSimpleFilesystem::write_node_template(const LbaNode& node,
                                               std::uint64_t offset_bytes,
                                               const T* data,
                                               std::size_t count) {
    std::size_t size_bytes = count * sizeof(T);
    check_bounds(node, offset_bytes, size_bytes);
    write_node(node, offset_bytes, data, size_bytes);
}

// Explicit template instantiations for common types
template void NvmeSimpleFilesystem::read_node_template<std::uint8_t>(
    const LbaNode&, std::uint64_t, std::uint8_t*, std::size_t);
template void NvmeSimpleFilesystem::read_node_template<std::uint32_t>(
    const LbaNode&, std::uint64_t, std::uint32_t*, std::size_t);
template void NvmeSimpleFilesystem::read_node_template<std::uint64_t>(
    const LbaNode&, std::uint64_t, std::uint64_t*, std::size_t);
template void NvmeSimpleFilesystem::read_node_template<float>(
    const LbaNode&, std::uint64_t, float*, std::size_t);
template void NvmeSimpleFilesystem::read_node_template<double>(
    const LbaNode&, std::uint64_t, double*, std::size_t);

template void NvmeSimpleFilesystem::write_node_template<std::uint8_t>(
    const LbaNode&, std::uint64_t, const std::uint8_t*, std::size_t);
template void NvmeSimpleFilesystem::write_node_template<std::uint32_t>(
    const LbaNode&, std::uint64_t, const std::uint32_t*, std::size_t);
template void NvmeSimpleFilesystem::write_node_template<std::uint64_t>(
    const LbaNode&, std::uint64_t, const std::uint64_t*, std::size_t);
template void NvmeSimpleFilesystem::write_node_template<float>(
    const LbaNode&, std::uint64_t, const float*, std::size_t);
template void NvmeSimpleFilesystem::write_node_template<double>(
    const LbaNode&, std::uint64_t, const double*, std::size_t);

void NvmeSimpleFilesystem::read_node(const LbaNode& node,
                                     std::uint64_t offset_bytes,
                                     void* buffer,
                                     std::size_t size_bytes) {
    check_bounds(node, offset_bytes, size_bytes);

    // Calculate LBA range
    std::uint64_t lba_offset = offset_bytes / superblock_.block_size;
    std::uint64_t byte_offset_in_block = offset_bytes % superblock_.block_size;
    std::uint64_t read_blocks =
        (byte_offset_in_block + size_bytes + superblock_.block_size - 1)
        / superblock_.block_size;

    std::vector<std::uint8_t> temp_buffer(read_blocks * superblock_.block_size);

    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device_);
    nvme_fs::read_blocks(dev, node.start_lba + lba_offset,
                          read_blocks, temp_buffer.data());

    std::memcpy(buffer, temp_buffer.data() + byte_offset_in_block, size_bytes);
}

void NvmeSimpleFilesystem::write_node(const LbaNode& node,
                                      std::uint64_t offset_bytes,
                                      const void* data,
                                      std::size_t size_bytes) {
    check_bounds(node, offset_bytes, size_bytes);

    // Calculate LBA range
    std::uint64_t lba_offset = offset_bytes / superblock_.block_size;
    std::uint64_t byte_offset_in_block = offset_bytes % superblock_.block_size;
    std::uint64_t write_blocks =
        (byte_offset_in_block + size_bytes + superblock_.block_size - 1)
        / superblock_.block_size;

    std::vector<std::uint8_t> temp_buffer(write_blocks * superblock_.block_size);

    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device_);

    // Read-modify-write for unaligned access
    nvme_fs::read_blocks(dev, node.start_lba + lba_offset,
                          write_blocks, temp_buffer.data());

    std::memcpy(temp_buffer.data() + byte_offset_in_block, data, size_bytes);

    nvme_fs::write_blocks(dev, node.start_lba + lba_offset,
                           write_blocks, temp_buffer.data());
}

std::size_t NvmeSimpleFilesystem::garbage_collect() {
    // Sort free list by start_lba
    std::sort(free_list_.begin(), free_list_.end(),
              [](const LbaNode& a, const LbaNode& b) {
                  return a.start_lba < b.start_lba;
              });

    // Merge adjacent free nodes
    std::size_t merged_count = 0;
    for (std::size_t i = 0; i + 1 < free_list_.size(); ) {
        if (free_list_[i].end_lba() == free_list_[i+1].start_lba) {
            free_list_[i].length += free_list_[i+1].length;
            free_list_.erase(free_list_.begin() + i + 1);
            merged_count++;
        } else {
            i++;
        }
    }

    if (merged_count > 0) {
        save_metadata();
    }

    return merged_count;
}

void NvmeSimpleFilesystem::get_stats(std::uint64_t& total_bytes,
                                     std::uint64_t& used_bytes,
                                     std::uint64_t& free_bytes) const {
    total_bytes = (superblock_.total_blocks - superblock_.metadata_blocks)
                  * superblock_.block_size;

    free_bytes = 0;
    for (const auto& node : free_list_) {
        free_bytes += node.length * superblock_.block_size;
    }

    used_bytes = total_bytes - free_bytes;
}

// Factory functions
std::unique_ptr<NvmeSimpleFilesystem> create_filesystem(
    void* nvme_device,
    std::uint64_t start_lba,
    std::uint64_t total_blocks,
    std::uint64_t block_size) {

    auto fs = std::make_unique<NvmeSimpleFilesystem>(
        nvme_device, start_lba, total_blocks, block_size);
    fs->format();
    return fs;
}

std::unique_ptr<NvmeSimpleFilesystem> open_filesystem(
    void* nvme_device,
    std::uint64_t start_lba) {

    return std::make_unique<NvmeSimpleFilesystem>(
        nvme_device, start_lba, 0, 512);
}

} // namespace nvme_fs
