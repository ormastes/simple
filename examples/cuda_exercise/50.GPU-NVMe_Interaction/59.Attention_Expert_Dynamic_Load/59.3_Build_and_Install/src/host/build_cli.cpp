#include "build_recipe.h"

#include <cuda_runtime.h>
#include <iostream>

int main() {
    const auto recipe = build59::buildDefaultRecipe();
    std::cout << build59::formatRecipe(recipe) << std::endl;

    int* device_value = nullptr;
    cudaMalloc(&device_value, sizeof(int));
    build59::populateDeviceStepCount(device_value,
                                     static_cast<int>(recipe.stepCount()));
    int host_value = 0;
    cudaMemcpy(&host_value, device_value, sizeof(int), cudaMemcpyDeviceToHost);
    cudaFree(device_value);

    std::cout << "Kernel reported " << host_value << " build steps." << std::endl;
    return 0;
}
