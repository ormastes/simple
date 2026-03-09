#include <thrust/device_vector.h>
#include <thrust/transform.h>
#include <thrust/reduce.h>
#include <thrust/functional.h>
#include <thrust/sort.h>
#include <iostream>

int main() {
    std::cout << "=== Thrust Algorithms Demo ===\n";

    const int N = 1000;
    
    thrust::device_vector<int> vec(N);
    thrust::sequence(vec.begin(), vec.end(), 1);

    // Reduce (sum)
    int sum = thrust::reduce(vec.begin(), vec.end(), 0, thrust::plus<int>());
    std::cout << "Sum of 1 to " << N << " = " << sum << "\n";

    // Transform (square each element)
    thrust::device_vector<int> squared(N);
    thrust::transform(vec.begin(), vec.end(), squared.begin(),
                      thrust::square<int>());

    // Sort
    thrust::device_vector<int> to_sort = {5, 2, 8, 1, 9, 3};
    thrust::sort(to_sort.begin(), to_sort.end());

    std::cout << "Sorted: [";
    for (size_t i = 0; i < to_sort.size(); i++) {
        std::cout << to_sort[i] << " ";
    }
    std::cout << "]\n";

    std::cout << "Demo completed successfully!\n";
    return 0;
}
