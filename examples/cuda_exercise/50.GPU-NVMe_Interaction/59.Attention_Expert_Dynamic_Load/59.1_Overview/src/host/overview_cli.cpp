#include "overview_data.h"

#include <cuda_runtime.h>
#include <iostream>
#include <vector>

int main() {
    const overview59::OverviewSummary summary = overview59::buildDefaultOverview();
    std::cout << overview59::formatOverview(summary) << std::endl;

    int* device_value = nullptr;
    cudaMalloc(&device_value, sizeof(int));
    overview59::populateDeviceLayerCount(device_value, static_cast<int>(summary.layerCount()));

    int host_value = 0;
    cudaMemcpy(&host_value, device_value, sizeof(int), cudaMemcpyDeviceToHost);
    cudaFree(device_value);

    std::cout << "Kernel reported " << host_value << " layers." << std::endl;
    return 0;
}
