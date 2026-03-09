/**
 * @file system_test_config.cpp
 * @brief Implementation of test configuration helpers
 */

#include "system_test_config.h"
#include "device/device_detector.h"
#include <cstring>

namespace nvme_test {

bool select_test_devices(
    SystemFeatures& out_features,
    SelectedDevices& out_devices,
    std::string& out_skip_reason,
    const char* optional_bdf) {

    // Detect all system devices
    out_features = SystemFeatures::detect_all();
    auto requirements = DeviceRequirements::for_host_dma();

    // Add specific BDF if provided
    if (optional_bdf && strlen(optional_bdf) > 0) {
        requirements.specific_nvme_bdf = optional_bdf;
    }

    // Select devices
    out_devices = out_features.select_devices(requirements);

    // Validate host selection
    if (!out_devices.host) {
        out_skip_reason += out_devices.host_log;
        return false;
    }

    // Validate NVMe selection
    if (!out_devices.nvme) {
        out_skip_reason += out_devices.nvme_log;
        return false;
    }

    // Success - NvmeSetupTask will handle VFIO binding automatically
    out_skip_reason.clear();
    return true;
}

}  // namespace nvme_test
