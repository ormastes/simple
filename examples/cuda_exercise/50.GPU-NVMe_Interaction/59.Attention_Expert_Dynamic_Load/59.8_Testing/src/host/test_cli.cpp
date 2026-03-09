#include "test_matrix.h"

#include <cuda_runtime.h>
#include <iostream>

int main() {
    const auto matrix = testing59::buildTestMatrix();
    std::cout << testing59::formatMatrix(matrix) << std::endl;

    int* device_value = nullptr;
    cudaMalloc(&device_value, sizeof(int));
    testing59::populateDeviceTestCount(device_value,
                                       static_cast<int>(matrix.testCount()));
    int host_value = 0;
    cudaMemcpy(&host_value, device_value, sizeof(int), cudaMemcpyDeviceToHost);
    cudaFree(device_value);

    std::cout << "Kernel reported " << host_value << " tests." << std::endl;
    return 0;
}
