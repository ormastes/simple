#include "perf_scenarios.h"

#include <cuda_runtime.h>
#include <iostream>

int main() {
    const auto plan = perf59::buildPerfPlan();
    std::cout << perf59::formatPlan(plan) << std::endl;

    int* device_value = nullptr;
    cudaMalloc(&device_value, sizeof(int));
    perf59::populateDeviceScenarioCount(device_value,
                                        static_cast<int>(plan.scenarioCount()));
    int host_value = 0;
    cudaMemcpy(&host_value, device_value, sizeof(int), cudaMemcpyDeviceToHost);
    cudaFree(device_value);

    std::cout << "Kernel reported " << host_value << " performance scenarios."
              << std::endl;
    return 0;
}
