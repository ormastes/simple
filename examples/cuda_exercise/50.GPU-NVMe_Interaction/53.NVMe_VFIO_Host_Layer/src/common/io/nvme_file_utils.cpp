/**
 * @file nvme_file_utils.cpp
 * @brief Implementation of utilities for file LBA mapping
 *
 * Migrated from test/helper/nvme_test_file_utils.cpp to src/common/io/
 * Test-specific functions removed, converted to C++ style.
 *
 * @date 2025-11-20
 */

#include "common/io/nvme_file_utils.h"
#include <fcntl.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <linux/fiemap.h>
#include <linux/fs.h>
#include <cstring>
#include <cerrno>
#include <memory>
#include <stdexcept>

namespace nvme {
namespace io {

namespace {

/// RAII wrapper for FILE*
struct FileCloser {
    void operator()(FILE* f) const {
        if (f) std::fclose(f);
    }
};
using FilePtr = std::unique_ptr<FILE, FileCloser>;

/**
 * @brief Helper to fetch file extent mappings via FIEMAP ioctl
 */
bool fiemap_batch(int fd, uint64_t start, uint64_t len,
                 std::vector<fiemap_extent>& out, bool& last) {
    constexpr size_t kBatch = 256;
    size_t bytes = sizeof(fiemap) + kBatch * sizeof(fiemap_extent);
    std::vector<unsigned char> tmp(bytes, 0);

    auto* fm = reinterpret_cast<fiemap*>(tmp.data());
    fm->fm_start = start;
    fm->fm_length = len;
    fm->fm_flags = 0;
    fm->fm_extent_count = kBatch;

    if (ioctl(fd, FS_IOC_FIEMAP, fm) < 0) {
        return false;
    }

    if (fm->fm_mapped_extents == 0) {
        last = true;
        return true;
    }

    auto* ex = fm->fm_extents;
    for (uint32_t i = 0; i < fm->fm_mapped_extents; i++) {
        out.push_back(ex[i]);
    }

    last = (ex[fm->fm_mapped_extents - 1].fe_flags & FIEMAP_EXTENT_LAST) != 0;
    return true;
}

} // anonymous namespace

int64_t get_file_lbas(const std::string& path, uint32_t sector_size,
                     std::vector<uint64_t>* lbas) {
    if (path.empty()) {
        throw std::invalid_argument("Empty file path");
    }
    if (sector_size == 0) {
        sector_size = 512;
    }

    FilePtr f(std::fopen(path.c_str(), "rb"));
    if (!f) {
        throw std::runtime_error("Failed to open file: " + std::string(strerror(errno)));
    }

    int fd = fileno(f.get());
    struct stat st{};
    if (fstat(fd, &st) != 0) {
        throw std::runtime_error("Failed to stat file: " + std::string(strerror(errno)));
    }

    uint64_t file_bytes = static_cast<uint64_t>(st.st_size);
    uint64_t next = 0;
    size_t total = 0;
    std::vector<uint64_t> temp_lbas;

    while (next < file_bytes) {
        std::vector<fiemap_extent> batch;
        bool fin = false;

        if (!fiemap_batch(fd, next, ~0ULL, batch, fin)) {
            throw std::runtime_error("FIEMAP ioctl failed: " + std::string(strerror(errno)));
        }

        if (batch.empty()) break;

        for (const auto& e : batch) {
            uint64_t L = e.fe_logical;
            uint64_t B = e.fe_length;

            if (L >= file_bytes) continue;
            if (L + B > file_bytes) B = file_bytes - L;

            uint64_t P = e.fe_physical;
            uint64_t N = B / sector_size;
            if (B % sector_size) N += 1;

            for (uint64_t s = 0; s < N; s++) {
                uint64_t lba = (P / sector_size) + s;
                temp_lbas.push_back(lba);
                total++;
            }

            next = L + e.fe_length;
        }

        if (fin) break;
    }

    if (lbas) {
        *lbas = std::move(temp_lbas);
    }

    return static_cast<int64_t>(total);
}

bool is_file_consecutive(const std::string& path, uint32_t sector_size,
                         size_t* total_lbas, size_t* break_index) {
    std::vector<uint64_t> lbas;
    int64_t count = get_file_lbas(path, sector_size, &lbas);

    if (count < 0) {
        throw std::runtime_error("Failed to get file LBAs");
    }

    if (total_lbas) {
        *total_lbas = static_cast<size_t>(count);
    }

    // Check consecutiveness
    for (size_t i = 0; i + 1 < lbas.size(); i++) {
        if (lbas[i + 1] != lbas[i] + 1) {
            if (break_index) {
                *break_index = i;
            }
            return false;  // Not consecutive
        }
    }

    if (break_index) {
        *break_index = static_cast<size_t>(-1);
    }
    return true;  // Consecutive
}

std::vector<FileExtent> get_file_extents(const std::string& path, uint32_t sector_size) {
    if (path.empty()) {
        throw std::invalid_argument("Empty file path");
    }
    if (sector_size == 0) {
        sector_size = 512;
    }

    FilePtr f(std::fopen(path.c_str(), "rb"));
    if (!f) {
        throw std::runtime_error("Failed to open file: " + std::string(strerror(errno)));
    }

    int fd = fileno(f.get());
    struct stat st{};
    if (fstat(fd, &st) != 0) {
        throw std::runtime_error("Failed to stat file: " + std::string(strerror(errno)));
    }

    uint64_t file_bytes = static_cast<uint64_t>(st.st_size);
    uint64_t next = 0;
    std::vector<FileExtent> extents;

    while (next < file_bytes) {
        std::vector<fiemap_extent> batch;
        bool fin = false;

        if (!fiemap_batch(fd, next, ~0ULL, batch, fin)) {
            throw std::runtime_error("FIEMAP ioctl failed: " + std::string(strerror(errno)));
        }

        if (batch.empty()) break;

        for (const auto& e : batch) {
            uint64_t L = e.fe_logical;
            uint64_t B = e.fe_length;

            if (L >= file_bytes) continue;
            if (L + B > file_bytes) B = file_bytes - L;

            FileExtent ext;
            ext.logical_offset = L;
            ext.physical_offset = e.fe_physical;
            ext.length = B;
            ext.start_lba = e.fe_physical / sector_size;
            ext.lba_count = (B + sector_size - 1) / sector_size;

            extents.push_back(ext);
            next = L + e.fe_length;
        }

        if (fin) break;
    }

    return extents;
}

double get_fragmentation_ratio(const std::string& path, uint32_t sector_size) {
    auto extents = get_file_extents(path, sector_size);

    if (extents.empty() || extents.size() == 1) {
        return 0.0;  // No fragmentation
    }

    // Calculate fragmentation as (extent_count - 1) / total_lbas
    uint64_t total_lbas = 0;
    for (const auto& ext : extents) {
        total_lbas += ext.lba_count;
    }

    if (total_lbas <= 1) {
        return 0.0;
    }

    // More extents = more fragmentation
    // Perfect file has 1 extent, worst case has total_lbas extents
    double fragmentation = static_cast<double>(extents.size() - 1) /
                          static_cast<double>(total_lbas - 1);

    return std::min(1.0, fragmentation);
}

LBAAnalysis analyze_file_lbas(const std::string& path, uint32_t sector_size) {
    LBAAnalysis result{};

    // Get LBAs
    std::vector<uint64_t> lbas;
    int64_t count = get_file_lbas(path, sector_size, &lbas);

    if (count <= 0) {
        throw std::runtime_error("No LBAs found for file");
    }

    result.total_lbas = static_cast<size_t>(count);

    // Get extents
    auto extents = get_file_extents(path, sector_size);
    result.extent_count = extents.size();

    // Check consecutiveness
    size_t break_idx = 0;
    result.is_consecutive = is_file_consecutive(path, sector_size, nullptr, &break_idx);

    // Calculate fragmentation
    result.fragmentation = get_fragmentation_ratio(path, sector_size);

    // Get first and last LBA
    if (!lbas.empty()) {
        result.first_lba = lbas.front();
        result.last_lba = lbas.back();
    }

    return result;
}

} // namespace io
} // namespace nvme