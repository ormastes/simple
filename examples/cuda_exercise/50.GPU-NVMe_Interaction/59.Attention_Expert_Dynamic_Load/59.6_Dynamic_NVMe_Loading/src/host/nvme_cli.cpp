#include "nvme_modes.h"

#include <cuda_runtime.h>
#include <iostream>

int main() {
    const auto modes = nvme59::buildNvmeModes();
    std::cout << nvme59::formatModes(modes) << std::endl;

    int* device_value = nullptr;
    cudaMalloc(&device_value, sizeof(int));
    nvme59::populateDeviceModeCount(device_value,
                                    static_cast<int>(modes.modeCount()));
    int host_value = 0;
    cudaMemcpy(&host_value, device_value, sizeof(int), cudaMemcpyDeviceToHost);
    cudaFree(device_value);

    std::cout << "Kernel reported " << host_value << " NVMe modes." << std::endl;
    return 0;
}
