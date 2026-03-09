#include "perf_scenarios.h"

#include <sstream>

namespace perf59 {

std::string formatPlan(const PerfPlan& plan) {
    std::ostringstream oss;
    oss << "Performance Plan (" << plan.scenarioCount() << " scenarios)\n";
    std::size_t idx = 1;
    for (const auto& scenario : plan.scenarios) {
        oss << "  [" << idx++ << "] " << scenario.name << "\n"
            << "      Command: " << scenario.profiler_command << "\n"
            << "      Metric: " << scenario.metric << "\n"
            << "      NVMe Mode: " << scenario.nvme_mode.name << '\n';
    }
    return oss.str();
}

}  // namespace perf59
