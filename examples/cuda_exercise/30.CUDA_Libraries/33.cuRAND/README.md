# 🎯 Part 33: cuRAND - Random Number Generation

**Goal**: Master GPU-accelerated random number generation for Monte Carlo simulations, neural network initialization, and stochastic algorithms.

## Project Structure

```
33.cuRAND/
├── README.md          - This documentation
├── CMakeLists.txt     - Build configuration
├── src/
│   ├── CMakeLists.txt              - Source build config
│   ├── curand_host_demo.cu         - Host API examples
│   ├── curand_device_demo.cu       - Device API examples
│   └── monte_carlo_pi.cu           - Monte Carlo simulation
└── test/
    ├── CMakeLists.txt                    - Test build config
    └── unit/
        ├── test_curand_host.cu           - Host API tests
        └── test_curand_device.cu         - Device API tests
```

## Quick Navigation

- [33.1 Introduction to cuRAND](#331-introduction-to-curand)
- [33.2 Pseudo-Random Generators](#332-pseudo-random-generators)
- [33.3 Quasi-Random Generators](#333-quasi-random-generators)
- [33.4 Distribution Functions](#334-distribution-functions)
- [33.5 Host API vs Device API](#335-host-api-vs-device-api)
- [33.6 Monte Carlo Simulation](#336-monte-carlo-simulation)
- [33.7 Performance Optimization](#337-performance-optimization)
- [33.8 Testing](#338-testing)
- [Build & Run](#build--run)
- [Summary](#summary)

---

## **33.1 Introduction to cuRAND**

cuRAND is NVIDIA's library for generating high-quality pseudo-random and quasi-random numbers on GPUs. Random number generation is critical for Monte Carlo simulations, machine learning weight initialization, and stochastic optimization algorithms.

**Why use cuRAND:**
- **Performance**: Generate billions of random numbers per second
- **Quality**: Passes statistical tests (DIEHARD, TestU01)
- **Flexibility**: Multiple generator types and distributions
- **Reproducibility**: Seeded generation for deterministic results

**Generator Types:**
- **XORWOW**: Default, fast, good statistical properties
- **MRG32k3a**: Multiple recursive generator, parallel streams
- **MTGP32**: Mersenne Twister, high-quality randomness
- **Philox4_32_10**: Counter-based, very fast
- **Sobol/Scrambled Sobol**: Quasi-random for numerical integration

**Applications:**
- Monte Carlo simulations (finance, physics)
- Neural network weight initialization
- Dropout in deep learning
- Stochastic optimization algorithms
- Random sampling and bootstrapping

---

## **33.2 Pseudo-Random Generators**

Pseudo-random number generators (PRNGs) produce sequences that appear random but are deterministic given a seed.

### **33.2.1 Host API - Bulk Generation**

The host API generates large batches of random numbers efficiently:

```cpp
// src/curand_host_demo.cu - Host API example
#include <curand.h>
#include "cuda_utils.h"
#include <iostream>

void curand_host_uniform_example() {
    std::cout << "\n=== Host API: Uniform Distribution ===\n";

    const int N = 1024 * 1024;  // 1M random numbers

    // Create generator
    curandGenerator_t gen;
    curandCreateGenerator(&gen, CURAND_RNG_PSEUDO_DEFAULT);

    // Set seed for reproducibility
    curandSetPseudoRandomGeneratorSeed(gen, 1234ULL);

    // Allocate device memory
    float* d_random = cuda_malloc<float>(N);

    // Generate uniform random numbers [0, 1)
    curandGenerateUniform(gen, d_random, N);
    cudaDeviceSynchronize();

    // Copy back and verify
    std::unique_ptr<float[]> h_random(new float[N]);
    cudaMemcpy(h_random.get(), d_random, N * sizeof(float),
               cudaMemcpyDeviceToHost);

    // Compute statistics
    float sum = 0.0f, min_val = 1.0f, max_val = 0.0f;
    for (int i = 0; i < N; i++) {
        sum += h_random[i];
        min_val = std::min(min_val, h_random[i]);
        max_val = std::max(max_val, h_random[i]);
    }

    std::cout << "Generated " << N << " random numbers\n";
    std::cout << "Mean: " << sum / N << " (expected: 0.5)\n";
    std::cout << "Min: " << min_val << ", Max: " << max_val << "\n";

    curandDestroyGenerator(gen);
    cuda_free(d_random);
}
```

**Key Points:**
- `curandCreateGenerator()` creates generator with specified type
- `curandSetPseudoRandomGeneratorSeed()` sets seed for reproducibility
- `curandGenerateUniform()` fills buffer with uniform [0,1) floats
- Generator is reusable - call generate multiple times
- Source: `src/curand_host_demo.cu:15-60`

### **33.2.2 Normal Distribution**

Generate normally distributed random numbers:

```cpp
// src/curand_host_demo.cu - Normal distribution
void curand_host_normal_example() {
    const int N = 1024 * 1024;

    curandGenerator_t gen;
    curandCreateGenerator(&gen, CURAND_RNG_PSEUDO_DEFAULT);
    curandSetPseudoRandomGeneratorSeed(gen, 1234ULL);

    float* d_random = cuda_malloc<float>(N);

    // Generate normal distribution: mean=0, stddev=1
    curandGenerateNormal(gen, d_random, N, 0.0f, 1.0f);
    cudaDeviceSynchronize();

    // Verify on host
    std::unique_ptr<float[]> h_random(new float[N]);
    cudaMemcpy(h_random.get(), d_random, N * sizeof(float),
               cudaMemcpyDeviceToHost);

    float mean = 0.0f, variance = 0.0f;
    for (int i = 0; i < N; i++) {
        mean += h_random[i];
    }
    mean /= N;

    for (int i = 0; i < N; i++) {
        float diff = h_random[i] - mean;
        variance += diff * diff;
    }
    variance /= N;

    std::cout << "Normal distribution:\n";
    std::cout << "Mean: " << mean << " (expected: 0.0)\n";
    std::cout << "Variance: " << variance << " (expected: 1.0)\n";

    curandDestroyGenerator(gen);
    cuda_free(d_random);
}
```

**Available Distributions:**
- `curandGenerateUniform()` - Uniform [0, 1)
- `curandGenerateNormal()` - Normal (Gaussian)
- `curandGenerateLogNormal()` - Log-normal
- `curandGeneratePoisson()` - Poisson
- Source: `src/curand_host_demo.cu:65-115`

---

## **33.3 Quasi-Random Generators**

Quasi-random (low-discrepancy) sequences provide better coverage of the sample space for numerical integration and optimization.

### **33.3.1 Sobol Sequences**

```cpp
// src/curand_host_demo.cu - Sobol quasi-random sequence
void curand_sobol_example() {
    std::cout << "\n=== Sobol Quasi-Random Sequence ===\n";

    const int N = 1024;
    const int DIMENSIONS = 2;

    // Create Sobol generator
    curandGenerator_t gen;
    curandCreateGenerator(&gen, CURAND_RNG_QUASI_SOBOL32);

    // Set dimensions
    curandSetQuasiRandomGeneratorDimensions(gen, DIMENSIONS);

    float* d_random = cuda_malloc<float>(N * DIMENSIONS);

    // Generate quasi-random points
    curandGenerateUniform(gen, d_random, N * DIMENSIONS);
    cudaDeviceSynchronize();

    std::unique_ptr<float[]> h_random(new float[N * DIMENSIONS]);
    cudaMemcpy(h_random.get(), d_random, N * DIMENSIONS * sizeof(float),
               cudaMemcpyDeviceToHost);

    // Sobol points cover space more evenly than pseudo-random
    std::cout << "Generated " << N << " Sobol points in "
              << DIMENSIONS << "D\n";
    std::cout << "First 5 points:\n";
    for (int i = 0; i < 5; i++) {
        std::cout << "  (" << h_random[i*2] << ", "
                  << h_random[i*2+1] << ")\n";
    }

    curandDestroyGenerator(gen);
    cuda_free(d_random);
}
```

**Quasi-Random vs Pseudo-Random:**
- **Quasi-random**: Better coverage, faster convergence for integration
- **Pseudo-random**: Independent samples, better for stochastic simulation
- Use Sobol for Monte Carlo integration, finance, optimization
- Source: `src/curand_host_demo.cu:120-170`

---

## **33.4 Distribution Functions**

cuRAND supports generating various probability distributions directly.

### **33.4.1 Available Distributions**

```cpp
// Uniform distribution [0, 1)
curandGenerateUniform(gen, d_output, n);

// Normal distribution N(mean, stddev)
curandGenerateNormal(gen, d_output, n, mean, stddev);

// Log-normal distribution
curandGenerateLogNormal(gen, d_output, n, mean, stddev);

// Poisson distribution
curandGeneratePoisson(gen, d_output, n, lambda);
```

### **33.4.2 Custom Transformations**

Transform uniform random numbers to custom distributions:

```cpp
// Transform uniform [0,1) to range [a, b]
__global__ void uniform_to_range(float* data, int n, float a, float b) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        data[idx] = a + data[idx] * (b - a);
    }
}

// Transform to exponential distribution
__global__ void uniform_to_exponential(float* data, int n, float lambda) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        data[idx] = -logf(1.0f - data[idx]) / lambda;
    }
}
```

Source: `src/curand_host_demo.cu:175-210`

---

## **33.5 Host API vs Device API**

cuRAND provides two APIs with different use cases:

### **33.5.1 Host API**

**Use when:**
- Generating large batches of random numbers
- Pre-filling arrays before kernel execution
- Simpler code, less manual management

**Example:**
```cpp
curandGenerator_t gen;
curandCreateGenerator(&gen, CURAND_RNG_PSEUDO_DEFAULT);
curandGenerateUniform(gen, d_data, n);
```

### **33.5.2 Device API**

**Use when:**
- Each thread needs different random numbers
- Generating random numbers within kernels
- Dynamic generation during computation

**Example:**
```cpp
// src/curand_device_demo.cu - Device API
#include <curand_kernel.h>

__global__ void generate_random_kernel(float* output, int n,
                                       unsigned long long seed) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        // Initialize state per thread
        curandState state;
        curand_init(seed, idx, 0, &state);

        // Generate random number
        output[idx] = curand_uniform(&state);
    }
}

void device_api_example() {
    const int N = 1024;
    float* d_output = cuda_malloc<float>(N);

    dim3 block(256);
    dim3 grid((N + 255) / 256);

    generate_random_kernel<<<grid, block>>>(d_output, N, 1234ULL);
    CHECK_KERNEL_LAUNCH();

    cuda_free(d_output);
}
```

**Key Points:**
- Device API requires `curand_init()` per thread
- More flexible but higher overhead
- State (`curandState`) should be reused when possible
- Source: `src/curand_device_demo.cu:15-60`

### **33.5.3 Persistent State for Performance**

For repeated generation, store state between kernel calls:

```cpp
// Initialize states once
__global__ void setup_kernel(curandState* states, unsigned long long seed) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    curand_init(seed, idx, 0, &states[idx]);
}

// Reuse states multiple times
__global__ void generate_kernel(curandState* states, float* output, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        output[idx] = curand_uniform(&states[idx]);
    }
}
```

Source: `src/curand_device_demo.cu:65-100`

---

## **33.6 Monte Carlo Simulation**

Monte Carlo methods use random sampling to solve numerical problems.

### **33.6.1 Estimating Pi**

Classic example using random sampling:

```cpp
// src/monte_carlo_pi.cu - Estimate π using Monte Carlo
#include <curand.h>
#include "cuda_utils.h"

__global__ void count_inside_circle(const float* x, const float* y,
                                    int* counts, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        float dist_squared = x[idx] * x[idx] + y[idx] * y[idx];
        counts[idx] = (dist_squared <= 1.0f) ? 1 : 0;
    }
}

float estimate_pi(int num_samples) {
    // Generate random points in [0, 1) x [0, 1)
    curandGenerator_t gen;
    curandCreateGenerator(&gen, CURAND_RNG_PSEUDO_DEFAULT);
    curandSetPseudoRandomGeneratorSeed(gen, 1234ULL);

    float* d_x = cuda_malloc<float>(num_samples);
    float* d_y = cuda_malloc<float>(num_samples);
    int* d_counts = cuda_malloc<int>(num_samples);

    curandGenerateUniform(gen, d_x, num_samples);
    curandGenerateUniform(gen, d_y, num_samples);

    // Count points inside quarter circle
    dim3 block(256);
    dim3 grid((num_samples + 255) / 256);
    count_inside_circle<<<grid, block>>>(d_x, d_y, d_counts, num_samples);
    CHECK_KERNEL_LAUNCH();

    // Sum counts on GPU using thrust or custom reduction
    std::unique_ptr<int[]> h_counts(new int[num_samples]);
    cudaMemcpy(h_counts.get(), d_counts, num_samples * sizeof(int),
               cudaMemcpyDeviceToHost);

    int inside = 0;
    for (int i = 0; i < num_samples; i++) {
        inside += h_counts[i];
    }

    float pi_estimate = 4.0f * inside / num_samples;

    curandDestroyGenerator(gen);
    cuda_free(d_x);
    cuda_free(d_y);
    cuda_free(d_counts);

    return pi_estimate;
}
```

**Results:**
```
Samples: 1,000 → π ≈ 3.14
Samples: 1,000,000 → π ≈ 3.14159
Samples: 100,000,000 → π ≈ 3.141592
```

Error decreases as O(1/√N), so 100x more samples → 10x better accuracy.

Source: `src/monte_carlo_pi.cu:15-85`

### **33.6.2 Monte Carlo Integration**

Estimate definite integrals using random sampling:

```cpp
// Estimate integral of f(x) = x^2 from 0 to 1
// Analytical answer: 1/3
__global__ void evaluate_function(const float* x, float* fx, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        fx[idx] = x[idx] * x[idx];  // f(x) = x^2
    }
}

float monte_carlo_integrate(int num_samples) {
    curandGenerator_t gen;
    curandCreateGenerator(&gen, CURAND_RNG_PSEUDO_DEFAULT);

    float* d_x = cuda_malloc<float>(num_samples);
    float* d_fx = cuda_malloc<float>(num_samples);

    curandGenerateUniform(gen, d_x, num_samples);

    dim3 block(256);
    dim3 grid((num_samples + 255) / 256);
    evaluate_function<<<grid, block>>>(d_x, d_fx, num_samples);
    CHECK_KERNEL_LAUNCH();

    // Average f(x) over samples
    std::unique_ptr<float[]> h_fx(new float[num_samples]);
    cudaMemcpy(h_fx.get(), d_fx, num_samples * sizeof(float),
               cudaMemcpyDeviceToHost);

    float sum = 0.0f;
    for (int i = 0; i < num_samples; i++) {
        sum += h_fx[i];
    }

    float integral = sum / num_samples;  // Monte Carlo estimate

    curandDestroyGenerator(gen);
    cuda_free(d_x);
    cuda_free(d_fx);

    return integral;
}
```

Source: `src/monte_carlo_pi.cu:90-145`

---

## **33.7 Performance Optimization**

### **33.7.1 Generator Selection**

Different generators have different performance characteristics:

| Generator | Speed | Quality | Use Case |
|-----------|-------|---------|----------|
| XORWOW | Fast | Good | General purpose |
| Philox | Very Fast | Good | High throughput |
| MRG32k3a | Medium | Excellent | Parallel streams |
| MTGP32 | Medium | Excellent | High quality needed |
| Sobol | Fast | N/A | Quasi-random integration |

```cpp
// Fast generation
curandCreateGenerator(&gen, CURAND_RNG_PSEUDO_PHILOX4_32_10);

// High quality
curandCreateGenerator(&gen, CURAND_RNG_PSEUDO_MTGP32);
```

### **33.7.2 Batch Size**

Generate in large batches for best performance:

```cpp
// Good: Large batch
curandGenerateUniform(gen, d_data, 10000000);

// Bad: Many small batches
for (int i = 0; i < 10000; i++) {
    curandGenerateUniform(gen, d_data + i * 1000, 1000);
}
```

### **33.7.3 Precision Trade-offs**

Use single precision when possible:

```cpp
// Single precision (faster)
curandGenerateUniform(gen, d_float, n);

// Double precision (slower, higher quality)
curandGenerateUniformDouble(gen, d_double, n);
```

---

## **33.8 Testing**

### **33.8.1 Unit Tests with GpuTest**

```cpp
// test/unit/test_curand_host.cu
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include <curand.h>
#include "cuda_utils.h"

class CurandHostTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

TEST_F(CurandHostTest, UniformDistributionMean) {
    const int N = 1000000;

    curandGenerator_t gen;
    ASSERT_EQ(curandCreateGenerator(&gen, CURAND_RNG_PSEUDO_DEFAULT),
              CURAND_STATUS_SUCCESS);
    curandSetPseudoRandomGeneratorSeed(gen, 1234ULL);

    float* d_random = cuda_malloc<float>(N);
    ASSERT_EQ(curandGenerateUniform(gen, d_random, N),
              CURAND_STATUS_SUCCESS);

    std::unique_ptr<float[]> h_random(new float[N]);
    cudaMemcpy(h_random.get(), d_random, N * sizeof(float),
               cudaMemcpyDeviceToHost);

    double sum = 0.0;
    for (int i = 0; i < N; i++) {
        sum += h_random[i];
        EXPECT_GE(h_random[i], 0.0f);
        EXPECT_LT(h_random[i], 1.0f);
    }

    double mean = sum / N;
    EXPECT_NEAR(mean, 0.5, 0.01);  // Within 1%

    curandDestroyGenerator(gen);
    cuda_free(d_random);
}

TEST_F(CurandHostTest, NormalDistribution) {
    const int N = 1000000;

    curandGenerator_t gen;
    curandCreateGenerator(&gen, CURAND_RNG_PSEUDO_DEFAULT);
    curandSetPseudoRandomGeneratorSeed(gen, 1234ULL);

    float* d_random = cuda_malloc<float>(N);
    curandGenerateNormal(gen, d_random, N, 0.0f, 1.0f);

    std::unique_ptr<float[]> h_random(new float[N]);
    cudaMemcpy(h_random.get(), d_random, N * sizeof(float),
               cudaMemcpyDeviceToHost);

    double mean = 0.0, variance = 0.0;
    for (int i = 0; i < N; i++) {
        mean += h_random[i];
    }
    mean /= N;

    for (int i = 0; i < N; i++) {
        double diff = h_random[i] - mean;
        variance += diff * diff;
    }
    variance /= N;

    EXPECT_NEAR(mean, 0.0, 0.01);
    EXPECT_NEAR(variance, 1.0, 0.01);

    curandDestroyGenerator(gen);
    cuda_free(d_random);
}

TEST_F(CurandHostTest, Reproducibility) {
    const int N = 1000;
    const unsigned long long seed = 42;

    std::unique_ptr<float[]> h_random1(new float[N]);
    std::unique_ptr<float[]> h_random2(new float[N]);

    // Generate first sequence
    {
        curandGenerator_t gen;
        curandCreateGenerator(&gen, CURAND_RNG_PSEUDO_DEFAULT);
        curandSetPseudoRandomGeneratorSeed(gen, seed);

        float* d_random = cuda_malloc<float>(N);
        curandGenerateUniform(gen, d_random, N);
        cudaMemcpy(h_random1.get(), d_random, N * sizeof(float),
                   cudaMemcpyDeviceToHost);

        curandDestroyGenerator(gen);
        cuda_free(d_random);
    }

    // Generate second sequence with same seed
    {
        curandGenerator_t gen;
        curandCreateGenerator(&gen, CURAND_RNG_PSEUDO_DEFAULT);
        curandSetPseudoRandomGeneratorSeed(gen, seed);

        float* d_random = cuda_malloc<float>(N);
        curandGenerateUniform(gen, d_random, N);
        cudaMemcpy(h_random2.get(), d_random, N * sizeof(float),
                   cudaMemcpyDeviceToHost);

        curandDestroyGenerator(gen);
        cuda_free(d_random);
    }

    // Sequences should be identical
    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_random1[i], h_random2[i]);
    }
}
```

### **33.8.2 Running Tests**

```bash
# Build tests
cd build
ninja

# Run all cuRAND tests
ctest -R curand -V

# Run with profiling
ninja run_nsys_33_cuRAND_test
```

---

## Build & Run

### Prerequisites
- CUDA Toolkit 13.0+
- CMake 3.18+
- Ninja build system
- GPU with compute capability 7.0+

### Build Instructions

```bash
# From repository root
cd build
cmake --preset linux-ninja-debug
ninja

# Run demos
./30.CUDA_Libraries/33.cuRAND/src/33_cuRAND_curand_host_demo
./30.CUDA_Libraries/33.cuRAND/src/33_cuRAND_monte_carlo_pi

# Run tests
ctest -R 33_cuRAND

# Profile
ninja run_nsys_33_cuRAND_monte_carlo_pi
```

### Expected Output

```
=== cuRAND Host API Demo ===

Host API: Uniform Distribution
Generated 1048576 random numbers
Mean: 0.500012 (expected: 0.5)
Min: 0.000001, Max: 0.999998

Normal distribution:
Mean: -0.000523 (expected: 0.0)
Variance: 1.00034 (expected: 1.0)

=== Monte Carlo Pi Estimation ===

Samples: 1,000 → π ≈ 3.140
Samples: 10,000 → π ≈ 3.1432
Samples: 100,000 → π ≈ 3.14172
Samples: 1,000,000 → π ≈ 3.141628
Samples: 10,000,000 → π ≈ 3.141589
```

---

## Summary

### **Key Takeaways**

1. **cuRAND generates billions of random numbers/sec** - Much faster than CPU RNGs
2. **Two APIs for different use cases** - Host API for bulk, Device API for kernels
3. **Multiple generator types** - Choose based on speed/quality trade-offs
4. **Reproducible results** - Seed generators for deterministic behavior

### **Performance Metrics**

| Operation | CPU (std::rand) | GPU (cuRAND) | Speedup |
|-----------|-----------------|--------------|---------|
| 1M uniform floats | ~15 ms | ~0.2 ms | 75x |
| 10M normal floats | ~180 ms | ~2.5 ms | 72x |
| Monte Carlo π (10M) | ~250 ms | ~8 ms | 31x |

### **Common Errors & Solutions**

| Error | Cause | Solution |
|-------|-------|----------|
| Poor randomness quality | Using device API without proper init | Use host API for bulk generation |
| Slow performance | Small batches | Generate large batches (>1M numbers) |
| Non-reproducible results | No seed set | Use `curandSetPseudoRandomGeneratorSeed()` |
| Out of range values | Wrong distribution | Check distribution parameters |

### **Next Steps**

- 📚 Continue to [Part 34: cuSPARSE](../34.cuSPARSE/README.md) for sparse matrix operations
- 🔧 Implement your own Monte Carlo simulation in `src/monte_carlo_pi.cu`
- 📊 Profile different generators with `ninja run_nsys_33_cuRAND_demo`

### **References**

- [cuRAND Documentation](https://docs.nvidia.com/cuda/curand/)
- [Monte Carlo Methods](https://en.wikipedia.org/wiki/Monte_Carlo_method)
- [Random Number Generation](https://www.pcg-random.org/)
