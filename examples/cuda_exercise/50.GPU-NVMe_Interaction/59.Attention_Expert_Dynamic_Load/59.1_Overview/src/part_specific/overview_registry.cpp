#include "overview_data.h"

#include <sstream>

namespace overview59 {

std::string formatOverview(const OverviewSummary& summary) {
    std::ostringstream oss;
    oss << summary.module_name << " contains " << summary.layerCount()
        << " architectural layers:\n";
    for (std::size_t i = 0; i < summary.components.size(); ++i) {
        const auto& component = summary.components[i];
        oss << "  [" << (i + 1) << "] " << component.name << ": "
            << component.description << '\n';
    }
    return oss.str();
}

}  // namespace overview59
