#include "feature_matrix.h"

#include <cuda_runtime.h>
#include <iostream>

int main() {
    const auto matrix = features59::buildDefaultMatrix();
    std::cout << features59::formatMatrix(matrix) << std::endl;

    int* device_value = nullptr;
    cudaMalloc(&device_value, sizeof(int));
    features59::populateDeviceFeatureCount(device_value,
                                           static_cast<int>(matrix.featureCount()));

    int host_value = 0;
    cudaMemcpy(&host_value, device_value, sizeof(int), cudaMemcpyDeviceToHost);
    cudaFree(device_value);

    std::cout << "Kernel reported " << host_value << " features." << std::endl;
    return 0;
}
