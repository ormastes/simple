# 🎯 Part 35: Thrust - High-Level Parallel Algorithms

**Goal**: Utilize C++ STL-like parallel algorithms for rapid GPU development with minimal code.

## Project Structure

```
35.Thrust/
├── README.md
├── CMakeLists.txt
├── src/
│   ├── CMakeLists.txt
│   ├── thrust_basics.cu
│   └── thrust_algorithms.cu
└── test/
    ├── CMakeLists.txt
    └── unit/
        └── test_thrust.cu
```

## Quick Navigation

- [35.1 Introduction](#351-introduction-to-thrust)
- [35.2 Device Vectors](#352-device-vectors)
- [35.3 Parallel Algorithms](#353-parallel-algorithms)
- [35.4 Transformations](#354-transformations)
- [35.5 Reductions](#355-reductions)
- [35.6 Sorting and Searching](#356-sorting-and-searching)
- [35.7 Testing](#357-testing)
- [Build & Run](#build--run)
- [Summary](#summary)

---

## **35.1 Introduction to Thrust**

Thrust is a C++ template library for CUDA providing high-level interface to GPU parallel algorithms. It resembles the C++ Standard Template Library (STL).

**Why use Thrust:**
- **Productivity**: Write less code, focus on algorithms
- **Performance**: Highly optimized implementations
- **Portability**: Code works on CPU and GPU
- **Interoperability**: Works with raw CUDA kernels

---

## **35.2 Device Vectors**

Thrust provides `device_vector` for automatic GPU memory management:

```cpp
#include <thrust/device_vector.h>
#include <thrust/host_vector.h>

// Allocate and initialize
thrust::device_vector<float> d_vec(1000);
thrust::fill(d_vec.begin(), d_vec.end(), 1.0f);

// Copy from host
thrust::host_vector<float> h_vec(1000, 2.0f);
thrust::device_vector<float> d_vec2 = h_vec;  // Automatic transfer

// Access raw pointer for CUDA kernels
float* raw_ptr = thrust::raw_pointer_cast(d_vec.data());
```

---

## **35.3 Parallel Algorithms**

### **35.3.1 Transform**

Apply function to each element:

```cpp
thrust::device_vector<float> input(100, 1.0f);
thrust::device_vector<float> output(100);

// Square each element
thrust::transform(input.begin(), input.end(), output.begin(),
                  thrust::square<float>());
```

### **35.3.2 Reduce**

Sum all elements:

```cpp
thrust::device_vector<int> vec(1000, 1);
int sum = thrust::reduce(vec.begin(), vec.end(), 0, thrust::plus<int>());
// sum = 1000
```

---

## **35.4 Transformations**

```cpp
// Binary transform: add two vectors
thrust::transform(a.begin(), a.end(), b.begin(), c.begin(),
                  thrust::plus<float>());

// Custom functor
struct square_and_add {
    __host__ __device__
    float operator()(float x, float y) const {
        return x * x + y;
    }
};

thrust::transform(a.begin(), a.end(), b.begin(), c.begin(),
                  square_and_add());
```

---

## **35.5 Reductions**

```cpp
// Find maximum
int max_val = thrust::reduce(vec.begin(), vec.end(), 0, thrust::maximum<int>());

// Count elements
int count = thrust::count_if(vec.begin(), vec.end(),
                              [](int x) { return x > 5; });

// Inner product (dot product)
float dot = thrust::inner_product(a.begin(), a.end(), b.begin(), 0.0f);
```

---

## **35.6 Sorting and Searching**

```cpp
// Sort
thrust::device_vector<int> vec = {5, 2, 8, 1, 9};
thrust::sort(vec.begin(), vec.end());

// Binary search
bool found = thrust::binary_search(vec.begin(), vec.end(), 8);

// Unique elements
thrust::device_vector<int> unique_vec = {1, 1, 2, 2, 3};
auto new_end = thrust::unique(unique_vec.begin(), unique_vec.end());
unique_vec.erase(new_end, unique_vec.end());
```

---

## **35.7 Testing**

```cpp
#include <gtest/gtest.h>
#include <thrust/device_vector.h>
#include <thrust/reduce.h>

TEST(ThrustTest, BasicReduce) {
    thrust::device_vector<int> vec(1000, 1);
    int sum = thrust::reduce(vec.begin(), vec.end());
    EXPECT_EQ(sum, 1000);
}
```

---

## Build & Run

```bash
cd build
ninja
./30.CUDA_Libraries/35.Thrust/src/35_Thrust_thrust_basics
ctest -R 35_Thrust
```

---

## Summary

### **Key Takeaways**

1. **Thrust simplifies GPU programming** - STL-like interface
2. **Automatic memory management** - No manual cudaMalloc/cudaFree
3. **High performance** - Optimized implementations
4. **Composable algorithms** - Combine primitives for complex operations

### **Performance Metrics**

| Operation | Manual CUDA | Thrust | Speedup |
|-----------|-------------|--------|---------|
| Reduce (10M) | ~2.5 ms | ~2.1 ms | 1.2x |
| Sort (10M) | ~15 ms | ~12 ms | 1.25x |

### **Next Steps**

- 📚 Continue to [Part 36: cuDNN](../36.cuDNN/README.md)
- 🔧 Experiment with custom functors

### **References**

- [Thrust Documentation](https://thrust.github.io/)
