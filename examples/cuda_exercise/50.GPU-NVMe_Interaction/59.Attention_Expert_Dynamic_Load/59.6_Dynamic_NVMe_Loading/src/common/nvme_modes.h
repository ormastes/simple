/**
 * @file nvme_modes.h
 * @brief Module 59.6 NVMe loading modes
 */

#pragma once

#include "dispatcher_checks.h"

#include <string>
#include <vector>

namespace nvme59 {

/**
 * @brief NVMe loading mode entry
 */
struct NvmeModeEntry {
    std::string name;
    std::string description;
    std::string staging_buffer;
    torch59::DispatcherCheck validation_check;
};

/**
 * @brief Collection of NVMe modes
 */
struct NvmeModeMatrix {
    std::vector<NvmeModeEntry> modes;

    [[nodiscard]] std::size_t modeCount() const noexcept {
        return modes.size();
    }
};

/**
 * @brief Build NVMe mode matrix
 * @return NVMe mode matrix with default modes
 */
NvmeModeMatrix buildNvmeModes();

/**
 * @brief Format modes for display
 * @param modes NVMe mode matrix to format
 * @return Formatted string
 */
std::string formatModes(const NvmeModeMatrix& modes);

/**
 * @brief Populate device memory with mode count
 * @param device_ptr Device memory pointer
 * @param mode_count Number of modes
 */
void populateDeviceModeCount(int* device_ptr, int mode_count);

}  // namespace nvme59
