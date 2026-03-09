#include "perf_scenarios.h"

namespace perf59 {
namespace {

PerfScenario make_scenario(const std::string& name,
                           const std::string& command,
                           const std::string& metric,
                           const nvme59::NvmeModeEntry& mode) {
    return PerfScenario{name, command, metric, mode};
}

}  // namespace

PerfPlan buildPerfPlan() {
    const auto modes = nvme59::buildNvmeModes();
    PerfPlan plan;
    plan.scenarios = {
        make_scenario("Nsight Systems Attention Hotloop",
                      "nsys profile -o attn_profile python python/examples/training_with_nvme.py",
                      "Kernel duration + NVTX ranges",
                      modes.modes[0]),
        make_scenario("Nsight Compute MoE Profiling",
                      "ncu --set full python python/examples/training_with_nvme.py --experts",
                      "SM occupancy, memory throughput",
                      modes.modes[1]),
        make_scenario("NVMe Streaming Benchmark",
                      "python python/examples/training_with_nvme.py --nvme-throughput",
                      "GB/s read rate vs GPU utilization",
                      modes.modes[2]),
    };
    return plan;
}

}  // namespace perf59
