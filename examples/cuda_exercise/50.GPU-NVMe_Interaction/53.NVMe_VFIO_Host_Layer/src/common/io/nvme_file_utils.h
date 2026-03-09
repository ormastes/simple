/**
 * @file nvme_file_utils.h
 * @brief Utilities for file LBA mapping and physical block operations
 *
 * Provides functions for mapping files to their physical block addresses
 * on NVMe devices. Useful for optimizing direct I/O operations and
 * understanding file fragmentation.
 *
 * Migrated from test/helper/nvme_test_file_utils.h to src/common/io/
 * for production use.
 */

#pragma once

#include <cstdint>
#include <cstddef>
#include <vector>
#include <string>

namespace nvme {
namespace io {

/**
 * @brief Get logical block addresses (LBAs) for a file
 *
 * Retrieves the physical LBAs on the block device that correspond to a file's
 * logical byte offsets using the FIEMAP ioctl. This is useful for:
 * - Direct I/O optimization
 * - Understanding file fragmentation
 * - Targeting specific physical blocks in NVMe commands
 *
 * @param path File path
 * @param sector_size Sector size in bytes (typically 512 or 4096)
 * @param[out] lbas Output vector for LBAs (optional)
 * @return Number of LBAs on success, negative error code on failure
 *
 * @note Requires Linux FIEMAP support (FS_IOC_FIEMAP ioctl)
 */
int64_t get_file_lbas(const std::string& path,
                      uint32_t sector_size = 512,
                      std::vector<uint64_t>* lbas = nullptr);

/**
 * @brief Check if file has consecutive LBA mapping
 *
 * Verifies that a file's physical blocks are consecutive on the underlying
 * block device, which is optimal for sequential NVMe I/O operations.
 *
 * @param path File path
 * @param sector_size Sector size in bytes (typically 512 or 4096)
 * @param[out] total_lbas Optional output for total number of LBAs
 * @param[out] break_index Optional output for index of first non-consecutive LBA
 * @return true if consecutive, false if not consecutive
 * @throws std::runtime_error on I/O errors
 */
bool is_file_consecutive(const std::string& path,
                         uint32_t sector_size = 512,
                         size_t* total_lbas = nullptr,
                         size_t* break_index = nullptr);

/**
 * @brief File extent information
 */
struct FileExtent {
    uint64_t logical_offset;   ///< Logical byte offset in file
    uint64_t physical_offset;  ///< Physical byte offset on device
    uint64_t length;          ///< Length in bytes
    uint64_t start_lba;       ///< Starting LBA
    uint64_t lba_count;       ///< Number of LBAs
};

/**
 * @brief Get detailed extent information for a file
 *
 * Provides more detailed information about file extents than get_file_lbas.
 * Useful for understanding file fragmentation patterns.
 *
 * @param path File path
 * @param sector_size Sector size in bytes
 * @return Vector of file extents
 * @throws std::runtime_error on I/O errors
 */
std::vector<FileExtent> get_file_extents(const std::string& path,
                                         uint32_t sector_size = 512);

/**
 * @brief Calculate file fragmentation ratio
 *
 * Returns a fragmentation score between 0.0 (perfectly consecutive)
 * and 1.0 (highly fragmented).
 *
 * @param path File path
 * @param sector_size Sector size in bytes
 * @return Fragmentation ratio (0.0 = no fragmentation, 1.0 = maximum)
 * @throws std::runtime_error on I/O errors
 */
double get_fragmentation_ratio(const std::string& path,
                               uint32_t sector_size = 512);

/**
 * @brief Result structure for LBA analysis
 */
struct LBAAnalysis {
    size_t total_lbas;        ///< Total number of LBAs
    size_t extent_count;      ///< Number of extents
    bool is_consecutive;      ///< Whether all LBAs are consecutive
    double fragmentation;     ///< Fragmentation ratio
    uint64_t first_lba;       ///< First LBA
    uint64_t last_lba;        ///< Last LBA
};

/**
 * @brief Perform comprehensive LBA analysis on a file
 *
 * Combines multiple analysis functions into a single call for efficiency.
 *
 * @param path File path
 * @param sector_size Sector size in bytes
 * @return LBA analysis results
 * @throws std::runtime_error on I/O errors
 */
LBAAnalysis analyze_file_lbas(const std::string& path,
                              uint32_t sector_size = 512);

} // namespace io
} // namespace nvme