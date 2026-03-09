#include "dataset_routes.h"

#include <sstream>

namespace dataset59 {

std::string formatPlan(const DatasetPlan& plan) {
    std::ostringstream oss;
    oss << "NVMe Dataset Routes (" << plan.routeCount() << " entries)\n";
    std::size_t idx = 1;
    for (const auto& route : plan.routes) {
        oss << "  [" << idx++ << "] " << route.name << "\n"
            << "      Device: " << route.nvme_device << "\n"
            << "      Shape: " << route.tensor_shape << "\n"
            << "      Validated by: " << route.validating_test.name << '\n';
    }
    return oss.str();
}

}  // namespace dataset59
