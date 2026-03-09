#include "nvme_modes.h"

namespace nvme59 {
namespace {

NvmeModeEntry make_mode(const std::string& name,
                        const std::string& description,
                        const std::string& staging,
                        const torch59::DispatcherCheck& check) {
    return NvmeModeEntry{name, description, staging, check};
}

}  // namespace

NvmeModeMatrix buildNvmeModes() {
    const auto matrix = torch59::buildDispatcherMatrix();
    NvmeModeMatrix modes;
    modes.modes = {
        make_mode("ALL_IN_MEMORY",
                  "Everything preloaded into VRAM; fastest path.",
                  "GPU Tensor Cache",
                  matrix.checks[0]),
        make_mode("DYNAMIC_FFN_ONLY",
                  "Stream only expert FFN weights per batch.",
                  "Pinned host buffer + cudaMemcpyAsync",
                  matrix.checks[2]),
        make_mode("DYNAMIC_ALL",
                  "Stream QKV + FFN from NVMe each iteration.",
                  "TensorNVMeReader direct-to-device",
                  matrix.checks.back()),
    };
    return modes;
}

}  // namespace nvme59
