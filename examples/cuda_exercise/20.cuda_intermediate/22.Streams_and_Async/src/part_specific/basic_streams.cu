#include <cuda_runtime.h>
#include <stdio.h>
#include <stdlib.h>

#define N (1<<20)
#define NSTREAMS 4

__global__ void vector_add(float* a, float* b, float* c, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        c[idx] = a[idx] + b[idx];
    }
}

static void check_cuda_error(cudaError_t error, const char* function) {
    if (error != cudaSuccess) {
        fprintf(stderr, "CUDA error in %s: %s\n", function, cudaGetErrorString(error));
        exit(1);
    }
}

void init_data(float* data, int size) {
    for (int i = 0; i < size; i++) {
        data[i] = (float)(rand() % 100) / 100.0f;
    }
}

int main() {
    printf("Basic CUDA Streams Example\n");
    printf("===========================\n\n");

    // Allocate pinned host memory
    float *h_a, *h_b, *h_c;
    check_cuda_error(cudaMallocHost(&h_a, N * sizeof(float)), "cudaMallocHost h_a");
    check_cuda_error(cudaMallocHost(&h_b, N * sizeof(float)), "cudaMallocHost h_b");
    check_cuda_error(cudaMallocHost(&h_c, N * sizeof(float)), "cudaMallocHost h_c");

    // Initialize data
    init_data(h_a, N);
    init_data(h_b, N);

    // Allocate device memory
    float *d_a, *d_b, *d_c;
    check_cuda_error(cudaMalloc(&d_a, N * sizeof(float)), "cudaMalloc d_a");
    check_cuda_error(cudaMalloc(&d_b, N * sizeof(float)), "cudaMalloc d_b");
    check_cuda_error(cudaMalloc(&d_c, N * sizeof(float)), "cudaMalloc d_c");

    // Create streams
    cudaStream_t streams[NSTREAMS];
    for (int i = 0; i < NSTREAMS; i++) {
        check_cuda_error(cudaStreamCreate(&streams[i]), "cudaStreamCreate");
    }

    // Divide work among streams
    int chunk_size = N / NSTREAMS;
    int threads = 256;
    int blocks = (chunk_size + threads - 1) / threads;

    // Process data in parallel using multiple streams
    for (int i = 0; i < NSTREAMS; i++) {
        int offset = i * chunk_size;

        // Async copy H2D
        check_cuda_error(cudaMemcpyAsync(&d_a[offset], &h_a[offset],
                                        chunk_size * sizeof(float),
                                        cudaMemcpyHostToDevice, streams[i]), "cudaMemcpyAsync H2D a");
        check_cuda_error(cudaMemcpyAsync(&d_b[offset], &h_b[offset],
                                        chunk_size * sizeof(float),
                                        cudaMemcpyHostToDevice, streams[i]), "cudaMemcpyAsync H2D b");

        // Launch kernel
        vector_add<<<blocks, threads, 0, streams[i]>>>(&d_a[offset], &d_b[offset], &d_c[offset], chunk_size);

        // Async copy D2H
        check_cuda_error(cudaMemcpyAsync(&h_c[offset], &d_c[offset],
                                        chunk_size * sizeof(float),
                                        cudaMemcpyDeviceToHost, streams[i]), "cudaMemcpyAsync D2H");
    }

    // Wait for all streams to complete
    for (int i = 0; i < NSTREAMS; i++) {
        check_cuda_error(cudaStreamSynchronize(streams[i]), "cudaStreamSynchronize");
    }

    // Verify results
    bool success = true;
    for (int i = 0; i < N; i++) {
        if (fabs(h_c[i] - (h_a[i] + h_b[i])) > 1e-5) {
            printf("Error at index %d: expected %f, got %f\n", i, h_a[i] + h_b[i], h_c[i]);
            success = false;
            break;
        }
    }

    if (success) {
        printf("SUCCESS: All results verified!\n");
        printf("Processed %d elements using %d streams\n", N, NSTREAMS);
    }

    // Cleanup
    for (int i = 0; i < NSTREAMS; i++) {
        cudaStreamDestroy(streams[i]);
    }

    cudaFree(d_a);
    cudaFree(d_b);
    cudaFree(d_c);

    cudaFreeHost(h_a);
    cudaFreeHost(h_b);
    cudaFreeHost(h_c);

    return 0;
}
