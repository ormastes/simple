#include <thrust/device_vector.h>
#include <thrust/host_vector.h>
#include <thrust/fill.h>
#include <thrust/copy.h>
#include <iostream>

int main() {
    std::cout << "=== Thrust Basics Demo ===\n";

    const int N = 1000;
    
    // Create device vector
    thrust::device_vector<float> d_vec(N);
    thrust::fill(d_vec.begin(), d_vec.end(), 3.14f);

    // Create host vector and copy
    thrust::host_vector<float> h_vec(N, 2.71f);
    thrust::device_vector<float> d_vec2 = h_vec;

    // Copy back to host
    thrust::host_vector<float> result = d_vec;

    std::cout << "Device vector size: " << d_vec.size() << "\n";
    std::cout << "First element: " << result[0] << "\n";
    std::cout << "Last element: " << result[N-1] << "\n";

    std::cout << "Demo completed successfully!\n";
    return 0;
}
