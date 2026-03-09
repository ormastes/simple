#include "example_registry.h"

#include <cuda_runtime.h>
#include <iostream>

int main() {
    const auto catalog = examples59::buildExampleCatalog();
    std::cout << examples59::formatCatalog(catalog) << std::endl;

    int* device_value = nullptr;
    cudaMalloc(&device_value, sizeof(int));
    examples59::populateDeviceSnippetCount(
        device_value, static_cast<int>(catalog.snippetCount()));
    int host_value = 0;
    cudaMemcpy(&host_value, device_value, sizeof(int), cudaMemcpyDeviceToHost);
    cudaFree(device_value);

    std::cout << "Kernel reported " << host_value << " usage snippets."
              << std::endl;
    return 0;
}
