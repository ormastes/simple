#include "dispatcher_checks.h"

#include <cuda_runtime.h>
#include <iostream>

int main() {
    const auto matrix = torch59::buildDispatcherMatrix();
    std::cout << torch59::formatMatrix(matrix) << std::endl;

    int* device_value = nullptr;
    cudaMalloc(&device_value, sizeof(int));
    torch59::populateDeviceCheckCount(device_value,
                                      static_cast<int>(matrix.checkCount()));
    int host_value = 0;
    cudaMemcpy(&host_value, device_value, sizeof(int), cudaMemcpyDeviceToHost);
    cudaFree(device_value);

    std::cout << "Kernel reported " << host_value << " PyTorch checks."
              << std::endl;
    return 0;
}
