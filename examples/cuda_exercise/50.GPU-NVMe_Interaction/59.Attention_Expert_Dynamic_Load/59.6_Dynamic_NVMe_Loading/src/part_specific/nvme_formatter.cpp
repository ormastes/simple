#include "nvme_modes.h"

#include <sstream>

namespace nvme59 {

std::string formatModes(const NvmeModeMatrix& modes) {
    std::ostringstream oss;
    oss << "NVMe Loading Modes (" << modes.modeCount() << " entries)\n";
    std::size_t idx = 1;
    for (const auto& mode : modes.modes) {
        oss << "  [" << idx++ << "] " << mode.name << "\n"
            << "      Desc: " << mode.description << "\n"
            << "      Staging: " << mode.staging_buffer << "\n"
            << "      Validated via: " << mode.validation_check.name << '\n';
    }
    return oss.str();
}

}  // namespace nvme59
