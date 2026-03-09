/**
 * @file device_selection.h
 * @brief Benchmark helper for selecting NVMe devices via SystemFeatures/device_chooser.
 *
 * Priority:
 * 1) Explicit NVME_BDF override (honored for VFIO-bound cases)
 * 2) Device chooser preference (DBC-capable when requested)
 * 3) First safe NVMe (non-OS) as fallback
 */

#pragma once

#include <optional>
#include <string>
#include "device/device_detector.h"

namespace benchmark_helper {

enum class NvmePreference {
    kAnySafe,          ///< Any non-OS NVMe
    kPreferDbc,        ///< Prefer DBC/shadow-doorbell capable if present
    kRequireDbc        ///< Must have FULL shadow doorbell support
};

struct NvmeSelection {
    std::string bdf;
    bool dbc_supported{false};
};

/**
 * @brief Select an NVMe BDF for benchmarks.
 *
 * @param preference How strongly to require DBC/shadow doorbell
 * @return Optional selection with BDF and DBC capability flag
 */
inline std::optional<NvmeSelection> select_nvme(NvmePreference preference) {
    // 1) Env override (honor explicit selection)
    if (const char* env_bdf = std::getenv("NVME_BDF")) {
        if (env_bdf[0] != '\0') {
            return NvmeSelection{env_bdf, false};
        }
    }

    // 2) Device chooser
    SystemFeatures features = SystemFeatures::detect_all();

    DeviceRequirements req;
    req.require_nvme = true;
    if (preference != NvmePreference::kAnySafe) {
        req.require_shadow_doorbell = true;
        req.require_full_shadow_doorbell = (preference == NvmePreference::kRequireDbc);
    }

    auto selection = features.select_devices(req, /*enable_log=*/false);
    if (selection.nvme) {
        return NvmeSelection{
            selection.nvme->get_pci_bus_id(),
            selection.nvme->get_shadow_doorbell_support() == SupportLevel::FULL};
    }

    // 3) Fallback: any safe NVMe (non-OS, available)
    for (const auto& nvme : features.nvme_devs) {
        if (!nvme.is_available() || nvme.is_os_live()) continue;
        return NvmeSelection{
            nvme.get_pci_bus_id(),
            nvme.get_shadow_doorbell_support() == SupportLevel::FULL};
    }

    return std::nullopt;
}

}  // namespace benchmark_helper
