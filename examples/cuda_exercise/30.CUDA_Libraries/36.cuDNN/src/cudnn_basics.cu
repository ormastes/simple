#include <cudnn.h>
#include <iostream>

int main() {
    std::cout << "=== cuDNN Basics Demo ===\n";

    cudnnHandle_t handle;
    cudnnStatus_t status = cudnnCreate(&handle);
    
    if (status == CUDNN_STATUS_SUCCESS) {
        std::cout << "cuDNN handle created successfully\n";
        
        size_t version = cudnnGetVersion();
        std::cout << "cuDNN version: " << version << "\n";
        
        cudnnDestroy(handle);
        std::cout << "Demo completed successfully!\n";
        return 0;
    } else {
        std::cerr << "Failed to create cuDNN handle\n";
        return 1;
    }
}
