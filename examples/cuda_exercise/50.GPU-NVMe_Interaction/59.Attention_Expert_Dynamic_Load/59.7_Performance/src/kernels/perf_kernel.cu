#include "perf_scenarios.h"

#include <cuda_runtime.h>

namespace perf59 {
namespace {

__global__ void write_scenario_count(int* device_ptr, int scenario_count) {
    if (threadIdx.x == 0 && blockIdx.x == 0) {
        *device_ptr = scenario_count;
    }
}

}  // namespace

void populateDeviceScenarioCount(int* device_ptr, int scenario_count) {
    if (device_ptr == nullptr) {
        return;
    }
    write_scenario_count<<<1, 1>>>(device_ptr, scenario_count);
    cudaDeviceSynchronize();
}

}  // namespace perf59
