#include "dataset_routes.h"

#include <cuda_runtime.h>
#include <iostream>

int main() {
    const auto plan = dataset59::buildDatasetPlan();
    std::cout << dataset59::formatPlan(plan) << std::endl;

    int* device_value = nullptr;
    cudaMalloc(&device_value, sizeof(int));
    dataset59::populateDeviceRouteCount(device_value,
                                        static_cast<int>(plan.routeCount()));
    int host_value = 0;
    cudaMemcpy(&host_value, device_value, sizeof(int), cudaMemcpyDeviceToHost);
    cudaFree(device_value);

    std::cout << "Kernel reported " << host_value << " dataset routes."
              << std::endl;
    return 0;
}
