/**
 * @file nvme_simple_fs.h
 * @brief Simple filesystem layer for NVMe with node-based LBA management
 */

#pragma once

#include <cstdint>
#include <cstddef>
#include <string>
#include <vector>
#include <map>
#include <memory>
#include <stdexcept>

namespace nvme_fs {

/**
 * @brief LBA node representing a contiguous range of logical blocks
 *
 * Each node represents a file or free space region with a starting LBA
 * and length in blocks.
 */
struct LbaNode {
    std::uint64_t start_lba{0};  ///< Starting logical block address
    std::uint64_t length{0};     ///< Number of blocks in this node
    std::uint32_t file_id{0};    ///< File ID (0 = free space)
    std::uint32_t flags{0};      ///< Node flags (reserved for future use)

    /// @brief Check if this node is free
    bool is_free() const { return file_id == 0; }

    /// @brief Get end LBA (exclusive)
    std::uint64_t end_lba() const { return start_lba + length; }
};

/**
 * @brief File metadata entry
 *
 * Maps file names to their LBA nodes and stores file attributes.
 */
struct FileEntry {
    std::string   name;          ///< File name (max 255 chars)
    std::uint32_t file_id{0};    ///< Unique file identifier
    std::uint64_t size_bytes{0}; ///< File size in bytes
    std::uint64_t item_size{1};  ///< Size of each item/record in bytes (default 1)
    std::uint64_t created_time{0}; ///< Creation timestamp
    std::uint64_t modified_time{0}; ///< Last modification timestamp
    std::uint32_t checksum{0};   ///< CRC32 checksum (optional)

    /// @brief Get number of items in file
    std::uint64_t num_items() const { return size_bytes / item_size; }
};

/**
 * @brief Filesystem superblock metadata
 *
 * Stored in the first LBA of the filesystem region.
 */
struct Superblock {
    std::uint32_t magic{0x4E564653};  ///< Magic number "NVFS"
    std::uint32_t version{1};         ///< Filesystem version
    std::uint64_t total_blocks{0};    ///< Total number of blocks
    std::uint64_t block_size{512};    ///< Block size in bytes (typically 512)
    std::uint64_t metadata_blocks{64}; ///< Blocks reserved for metadata
    std::uint64_t default_item_size{512}; ///< Default item size for new files
    std::uint64_t next_file_id{1};    ///< Next available file ID
    std::uint32_t num_files{0};       ///< Number of files currently stored
    std::uint32_t num_nodes{0};       ///< Number of LBA nodes (files + free)
};

/**
 * @brief Access violation exception
 *
 * Thrown when attempting to read/write outside of node boundaries.
 */
class AccessViolationError : public std::runtime_error {
public:
    AccessViolationError(const std::string& msg) : std::runtime_error(msg) {}
};

/**
 * @brief File not found exception
 */
class FileNotFoundError : public std::runtime_error {
public:
    FileNotFoundError(const std::string& msg) : std::runtime_error(msg) {}
};

/**
 * @brief Out of space exception
 */
class OutOfSpaceError : public std::runtime_error {
public:
    OutOfSpaceError(const std::string& msg) : std::runtime_error(msg) {}
};

// Forward declaration
class NvmeSimpleFilesystem;

/**
 * @brief Simple filesystem implementation for NVMe with node-based LBA management
 */
class NvmeSimpleFilesystem {
public:
    /**
     * @brief Construct filesystem instance
     *
     * @param nvme_device NVMe device handle (from Module 53)
     * @param start_lba Starting LBA for filesystem region
     * @param total_blocks Total number of blocks available
     * @param block_size Block size in bytes (default 512)
     */
    NvmeSimpleFilesystem(void* nvme_device,
                         std::uint64_t start_lba,
                         std::uint64_t total_blocks,
                         std::uint64_t block_size = 512);

    ~NvmeSimpleFilesystem();

    // ---- File operations ----

    /**
     * @brief Save file to filesystem
     * @param filename File name
     * @param data File data buffer
     * @param size_bytes File size in bytes
     * @param item_size Size of each item/record (default: use filesystem default)
     * @return File ID of created file
     */
    std::uint32_t save_file(const std::string& filename,
                            const void* data,
                            std::size_t size_bytes,
                            std::uint64_t item_size = 0);

    /**
     * @brief Read entire file into buffer
     * @param filename File name
     * @param[out] buffer Output buffer (must be >= file size)
     * @param buffer_size Buffer size in bytes
     * @return Number of bytes read
     */
    std::size_t read_file(const std::string& filename,
                          void* buffer,
                          std::size_t buffer_size);

    /**
     * @brief Write data to file at offset
     * @param filename File name
     * @param offset Offset in bytes from file start
     * @param data Data to write
     * @param size_bytes Number of bytes to write
     */
    void write_file(const std::string& filename,
                    std::uint64_t offset,
                    const void* data,
                    std::size_t size_bytes);

    /**
     * @brief Delete file and mark space as free
     *
     * @param filename File name
     * @return true if deleted, false if file not found
     */
    bool delete_file(const std::string& filename);

    /**
     * @brief Get LBA node for a file
     * @param filename File name
     * @return LBA node information
     */
    LbaNode get_file_node(const std::string& filename) const;

    /**
     * @brief Get file metadata
     * @param filename File name
     * @return File entry with metadata
     */
    FileEntry get_file_info(const std::string& filename) const;

    /**
     * @brief List all files in filesystem
     *
     * @return Vector of file entries
     */
    std::vector<FileEntry> list_files() const;

    // ---- Item-based I/O operations ----

    /**
     * @brief Read items from file
     * @param filename File name
     * @param item_offset Starting item index
     * @param num_items Number of items to read
     * @param buffer Output buffer (must be >= num_items * item_size)
     * @return Number of items actually read
     */
    std::size_t read_items(const std::string& filename,
                          std::uint64_t item_offset,
                          std::uint64_t num_items,
                          void* buffer);

    /**
     * @brief Write items to file
     * @param filename File name
     * @param item_offset Starting item index
     * @param num_items Number of items to write
     * @param data Input data buffer
     */
    void write_items(const std::string& filename,
                    std::uint64_t item_offset,
                    std::uint64_t num_items,
                    const void* data);

    /**
     * @brief Read single item from file
     * @tparam T Item type
     * @param filename File name
     * @param item_index Item index
     * @param[out] item Output item
     */
    template<typename T>
    void read_item(const std::string& filename, std::uint64_t item_index, T& item);

    /**
     * @brief Write single item to file
     * @tparam T Item type
     * @param filename File name
     * @param item_index Item index
     * @param item Input item
     */
    template<typename T>
    void write_item(const std::string& filename, std::uint64_t item_index, const T& item);

    // ---- Node-based I/O (template version) ----

    /**
     * @brief Template read from node with compile-time bounds checking
     * @tparam T Data type to read
     * @param node LBA node to read from
     * @param offset_bytes Offset in bytes from node start
     * @param buffer Output buffer
     * @param count Number of elements of type T to read
     */
    template<typename T>
    void read_node_template(const LbaNode& node,
                           std::uint64_t offset_bytes,
                           T* buffer,
                           std::size_t count);

    /**
     * @brief Template write to node with compile-time bounds checking
     * @tparam T Data type to write
     * @param node LBA node to write to
     * @param offset_bytes Offset in bytes from node start
     * @param data Input data buffer
     * @param count Number of elements of type T to write
     */
    template<typename T>
    void write_node_template(const LbaNode& node,
                            std::uint64_t offset_bytes,
                            const T* data,
                            std::size_t count);

    // ---- Node-based I/O (runtime version) ----

    /**
     * @brief Read from node with runtime bounds checking
     * @param node LBA node to read from
     * @param offset_bytes Offset in bytes from node start
     * @param buffer Output buffer
     * @param size_bytes Number of bytes to read
     */
    void read_node(const LbaNode& node,
                   std::uint64_t offset_bytes,
                   void* buffer,
                   std::size_t size_bytes);

    /**
     * @brief Write to node with runtime bounds checking
     * @param node LBA node to write to
     * @param offset_bytes Offset in bytes from node start
     * @param data Input data buffer
     * @param size_bytes Number of bytes to write
     */
    void write_node(const LbaNode& node,
                    std::uint64_t offset_bytes,
                    const void* data,
                    std::size_t size_bytes);

    // ---- Space management ----

    /**
     * @brief Merge adjacent free nodes to reduce fragmentation
     * @return Number of nodes merged
     */
    std::size_t garbage_collect();

    /**
     * @brief Get filesystem statistics
     *
     * @param[out] total_bytes Total filesystem size
     * @param[out] used_bytes Bytes currently in use
     * @param[out] free_bytes Bytes available
     */
    void get_stats(std::uint64_t& total_bytes,
                   std::uint64_t& used_bytes,
                   std::uint64_t& free_bytes) const;

    /**
     * @brief Flush metadata to NVMe
     *
     * Writes superblock and file metadata to reserved LBAs.
     * Call after modifications to persist changes.
     */
    void flush_metadata();

    /**
     * @brief Format filesystem (erase all files)
     *
     * @warning Destroys all data
     */
    void format();

private:
    void* nvme_device_;           ///< NVMe device handle
    std::uint64_t start_lba_;     ///< Filesystem start LBA
    Superblock superblock_;       ///< Filesystem metadata

    std::map<std::string, FileEntry> file_table_;  ///< Name -> File entry
    std::map<std::uint32_t, LbaNode> node_map_;    ///< File ID -> LBA node
    std::vector<LbaNode> free_list_;               ///< Free LBA nodes

    void load_metadata();         ///< Load metadata from NVMe
    void save_metadata();         ///< Save metadata to NVMe
    LbaNode allocate_space(std::uint64_t size_bytes); ///< Allocate LBA range
    void free_space(const LbaNode& node);  ///< Mark node as free
    void check_bounds(const LbaNode& node, std::uint64_t offset, std::size_t size) const;
};

// ---- Template implementations ----

template<typename T>
void NvmeSimpleFilesystem::read_item(const std::string& filename,
                                     std::uint64_t item_index,
                                     T& item) {
    auto it = file_table_.find(filename);
    if (it == file_table_.end()) {
        throw FileNotFoundError("File not found: " + filename);
    }

    const FileEntry& entry = it->second;
    if (sizeof(T) != entry.item_size) {
        throw std::runtime_error("Item type size mismatch with file item_size");
    }

    if (item_index >= entry.num_items()) {
        throw AccessViolationError("Item index out of bounds");
    }

    read_items(filename, item_index, 1, &item);
}

template<typename T>
void NvmeSimpleFilesystem::write_item(const std::string& filename,
                                      std::uint64_t item_index,
                                      const T& item) {
    auto it = file_table_.find(filename);
    if (it == file_table_.end()) {
        throw FileNotFoundError("File not found: " + filename);
    }

    const FileEntry& entry = it->second;
    if (sizeof(T) != entry.item_size) {
        throw std::runtime_error("Item type size mismatch with file item_size");
    }

    if (item_index >= entry.num_items()) {
        throw AccessViolationError("Item index out of bounds");
    }

    write_items(filename, item_index, 1, &item);
}

/**
 * @brief Create or open existing filesystem on NVMe device
 *
 * @param nvme_device NVMe device handle
 * @param start_lba Starting LBA for filesystem
 * @param total_blocks Total blocks for filesystem
 * @param block_size Block size in bytes
 * @return Filesystem instance
 */
std::unique_ptr<NvmeSimpleFilesystem> create_filesystem(
    void* nvme_device,
    std::uint64_t start_lba,
    std::uint64_t total_blocks,
    std::uint64_t block_size = 512);

/**
 * @brief Open existing filesystem
 *
 * @param nvme_device NVMe device handle
 * @param start_lba Starting LBA where filesystem is located
 * @return Filesystem instance
 *
 * @throws std::runtime_error if no valid filesystem found
 */
std::unique_ptr<NvmeSimpleFilesystem> open_filesystem(
    void* nvme_device,
    std::uint64_t start_lba);

} // namespace nvme_fs
