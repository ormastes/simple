#include "test_matrix.h"

namespace testing59 {
namespace {

TestEntry make_entry(const std::string& name,
                     const std::string& command,
                     const std::string& type,
                     const perf59::PerfScenario& scenario) {
    return TestEntry{name, command, type, scenario};
}

}  // namespace

TestMatrix buildTestMatrix() {
    const auto perf_plan = perf59::buildPerfPlan();
    TestMatrix matrix;
    matrix.entries = {
        make_entry("Metadata Unit Tests",
                   "ctest -R 59_Attention_Expert_Dynamic_Load_unit_common",
                   "Unit",
                   perf_plan.scenarios[0]),
        make_entry("PyTorch Integration",
                   "ctest -R 59_Attention_PyTorchIntegration",
                   "Integration",
                   perf_plan.scenarios[0]),
        make_entry("NVMe Loading Test",
                   "ctest -R 59_Attention_NvmeLoading",
                   "Integration",
                   perf_plan.scenarios[2]),
        make_entry("CLI Smoke",
                   "./59_4_Usage_Examples_cli",
                   "Manual",
                   perf_plan.scenarios[1]),
    };
    return matrix;
}

}  // namespace testing59
