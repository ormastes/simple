/**
 * @file nvme_simple_fs_c_api.h
 * @brief C API wrapper for NVMe simple filesystem
 */

#pragma once

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Opaque filesystem handle
 */
typedef struct nvme_fs_handle nvme_fs_handle_t;

/**
 * @brief LBA node descriptor (C-compatible)
 */
typedef struct {
    uint64_t start_lba;
    uint64_t length;
    uint32_t file_id;
    uint32_t flags;
} nvme_fs_node_t;

/**
 * @brief File information structure (C-compatible)
 */
typedef struct {
    char     name[256];
    uint32_t file_id;
    uint64_t size_bytes;
    uint64_t created_time;
    uint64_t modified_time;
    uint32_t checksum;
} nvme_fs_file_info_t;

/**
 * @brief Filesystem statistics
 */
typedef struct {
    uint64_t total_bytes;
    uint64_t used_bytes;
    uint64_t free_bytes;
    uint32_t num_files;
} nvme_fs_stats_t;

// ---- Filesystem lifecycle ----

/**
 * @brief Create new filesystem on NVMe device
 *
 * @param nvme_device NVMe device handle
 * @param start_lba Starting LBA
 * @param total_blocks Total blocks for filesystem
 * @param block_size Block size in bytes
 * @return Filesystem handle or NULL on error
 */
nvme_fs_handle_t* nvme_fs_create(void* nvme_device,
                                 uint64_t start_lba,
                                 uint64_t total_blocks,
                                 uint64_t block_size);

/**
 * @brief Open existing filesystem
 *
 * @param nvme_device NVMe device handle
 * @param start_lba Starting LBA
 * @return Filesystem handle or NULL on error
 */
nvme_fs_handle_t* nvme_fs_open(void* nvme_device, uint64_t start_lba);

/**
 * @brief Close filesystem and flush metadata
 *
 * @param fs Filesystem handle
 */
void nvme_fs_close(nvme_fs_handle_t* fs);

/**
 * @brief Format filesystem (erase all files)
 *
 * @param fs Filesystem handle
 * @return 0 on success, negative on error
 */
int nvme_fs_format(nvme_fs_handle_t* fs);

// ---- File operations ----

/**
 * @brief Save file to filesystem
 *
 * @param fs Filesystem handle
 * @param filename File name (null-terminated)
 * @param data File data
 * @param size_bytes File size in bytes
 * @return File ID on success, 0 on error
 */
uint32_t nvme_fs_save_file(nvme_fs_handle_t* fs,
                           const char* filename,
                           const void* data,
                           size_t size_bytes);

/**
 * @brief Read entire file
 *
 * @param fs Filesystem handle
 * @param filename File name
 * @param buffer Output buffer
 * @param buffer_size Buffer size in bytes
 * @return Number of bytes read, or 0 on error
 */
size_t nvme_fs_read_file(nvme_fs_handle_t* fs,
                         const char* filename,
                         void* buffer,
                         size_t buffer_size);

/**
 * @brief Write data to file at offset
 *
 * @param fs Filesystem handle
 * @param filename File name
 * @param offset Offset in bytes
 * @param data Data to write
 * @param size_bytes Number of bytes to write
 * @return 0 on success, negative on error
 */
int nvme_fs_write_file(nvme_fs_handle_t* fs,
                       const char* filename,
                       uint64_t offset,
                       const void* data,
                       size_t size_bytes);

/**
 * @brief Delete file
 *
 * @param fs Filesystem handle
 * @param filename File name
 * @return 1 if deleted, 0 if not found, negative on error
 */
int nvme_fs_delete_file(nvme_fs_handle_t* fs, const char* filename);

/**
 * @brief Get file information
 *
 * @param fs Filesystem handle
 * @param filename File name
 * @param[out] info File information structure
 * @return 0 on success, negative on error
 */
int nvme_fs_get_file_info(nvme_fs_handle_t* fs,
                          const char* filename,
                          nvme_fs_file_info_t* info);

/**
 * @brief Get LBA node for file
 *
 * @param fs Filesystem handle
 * @param filename File name
 * @param[out] node LBA node structure
 * @return 0 on success, negative on error
 */
int nvme_fs_get_file_node(nvme_fs_handle_t* fs,
                          const char* filename,
                          nvme_fs_node_t* node);

/**
 * @brief List all files
 *
 * @param fs Filesystem handle
 * @param[out] files Array of file info structures (caller allocates)
 * @param max_files Maximum number of files to return
 * @return Number of files returned
 */
size_t nvme_fs_list_files(nvme_fs_handle_t* fs,
                          nvme_fs_file_info_t* files,
                          size_t max_files);

// ---- Node-based I/O ----

/**
 * @brief Read from LBA node at offset
 *
 * @param fs Filesystem handle
 * @param node LBA node
 * @param offset_bytes Offset in bytes
 * @param buffer Output buffer
 * @param size_bytes Number of bytes to read
 * @return 0 on success, negative on error
 */
int nvme_fs_read_node(nvme_fs_handle_t* fs,
                      const nvme_fs_node_t* node,
                      uint64_t offset_bytes,
                      void* buffer,
                      size_t size_bytes);

/**
 * @brief Write to LBA node at offset
 *
 * @param fs Filesystem handle
 * @param node LBA node
 * @param offset_bytes Offset in bytes
 * @param data Data to write
 * @param size_bytes Number of bytes to write
 * @return 0 on success, negative on error
 */
int nvme_fs_write_node(nvme_fs_handle_t* fs,
                       const nvme_fs_node_t* node,
                       uint64_t offset_bytes,
                       const void* data,
                       size_t size_bytes);

// ---- Space management ----

/**
 * @brief Run garbage collection
 *
 * @param fs Filesystem handle
 * @return Number of nodes merged
 */
size_t nvme_fs_garbage_collect(nvme_fs_handle_t* fs);

/**
 * @brief Get filesystem statistics
 *
 * @param fs Filesystem handle
 * @param[out] stats Statistics structure
 * @return 0 on success, negative on error
 */
int nvme_fs_get_stats(nvme_fs_handle_t* fs, nvme_fs_stats_t* stats);

/**
 * @brief Flush metadata to NVMe
 *
 * @param fs Filesystem handle
 * @return 0 on success, negative on error
 */
int nvme_fs_flush(nvme_fs_handle_t* fs);

// ---- Error handling ----

/**
 * @brief Get last error message
 *
 * @return Error message string (valid until next API call)
 */
const char* nvme_fs_get_last_error(void);

#ifdef __cplusplus
}
#endif
