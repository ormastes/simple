/**
 * Array of Structures (AoS) vs Structure of Arrays (SoA) Comparison
 *
 * Demonstrates the performance impact of data layout on memory coalescing:
 *
 * Array of Structures (AoS):
 * - Natural C/C++ representation
 * - Poor coalescing: accessing same field across instances requires strided access
 * - Example: particles[i].x, particles[i+1].x, ... requires skipping vx,vy,vz fields
 *
 * Structure of Arrays (SoA):
 * - GPU-friendly representation
 * - Perfect coalescing: all x values stored consecutively
 * - Example: x[i], x[i+1], x[i+2], ... are consecutive in memory
 *
 * Performance Impact: SoA typically 2-4x faster than AoS for GPU workloads
 */

#include <cuda_runtime.h>
#include <stdio.h>
#include "cuda_utils.h"

#define BLOCK_SIZE 256
#define NUM_PARTICLES (4 * 1024 * 1024)  // 4M particles
#define ITERATIONS 100

// ============================================================================
// Data Structure Definitions
// ============================================================================

/**
 * Array of Structures (AoS) layout
 * Memory: [x0,y0,z0,vx0,vy0,vz0, x1,y1,z1,vx1,vy1,vz1, ...]
 * Size: 24 bytes per particle (6 floats × 4 bytes)
 */
struct Particle_AoS {
    float x, y, z;     // Position
    float vx, vy, vz;  // Velocity
};

/**
 * Structure of Arrays (SoA) layout
 * Memory: [x0,x1,x2,...], [y0,y1,y2,...], [z0,z1,z2,...], ...
 * Better cache utilization and coalescing
 */
struct Particles_SoA {
    float *x, *y, *z;      // Position arrays
    float *vx, *vy, *vz;   // Velocity arrays
};

// ============================================================================
// AoS Kernels (Poor Coalescing)
// ============================================================================

/**
 * Update particle positions using AoS layout
 * Poor coalescing: Thread i accesses particles[i].x
 * - Warp accesses: p[0].x, p[1].x, ..., p[31].x
 * - Memory addresses: 0, 24, 48, ..., 744 (bytes)
 * - Strided by 24 bytes, requires multiple transactions
 */
__global__ void update_particles_aos(Particle_AoS* particles, int n, float dt) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid < n) {
        // Each field access is strided by sizeof(Particle_AoS) = 24 bytes
        particles[tid].x += particles[tid].vx * dt;
        particles[tid].y += particles[tid].vy * dt;
        particles[tid].z += particles[tid].vz * dt;
    }
}

/**
 * Apply force to particles using AoS layout
 * Demonstrates multiple strided accesses per thread
 */
__global__ void apply_force_aos(Particle_AoS* particles, int n,
                                 float fx, float fy, float fz, float dt) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid < n) {
        // Multiple strided accesses
        particles[tid].vx += fx * dt;
        particles[tid].vy += fy * dt;
        particles[tid].vz += fz * dt;
    }
}

// ============================================================================
// SoA Kernels (Perfect Coalescing)
// ============================================================================

/**
 * Update particle positions using SoA layout
 * Perfect coalescing: Thread i accesses x[i]
 * - Warp accesses: x[0], x[1], ..., x[31]
 * - Memory addresses: 0, 4, 8, ..., 124 (bytes)
 * - Consecutive access, single transaction per field
 */
__global__ void update_particles_soa(Particles_SoA particles, int n, float dt) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid < n) {
        // Each field access is perfectly coalesced
        particles.x[tid] += particles.vx[tid] * dt;
        particles.y[tid] += particles.vy[tid] * dt;
        particles.z[tid] += particles.vz[tid] * dt;
    }
}

/**
 * Apply force to particles using SoA layout
 * Demonstrates perfect coalescing for all accesses
 */
__global__ void apply_force_soa(Particles_SoA particles, int n,
                                 float fx, float fy, float fz, float dt) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid < n) {
        // All accesses perfectly coalesced
        particles.vx[tid] += fx * dt;
        particles.vy[tid] += fy * dt;
        particles.vz[tid] += fz * dt;
    }
}

// ============================================================================
// Benchmark Harness
// ============================================================================

void benchmark_aos(int n) {
    // Allocate AoS data
    Particle_AoS* d_particles_aos;
    CHECK_CUDA(cudaMalloc(&d_particles_aos, n * sizeof(Particle_AoS)));
    CHECK_CUDA(cudaMemset(d_particles_aos, 0, n * sizeof(Particle_AoS)));

    int blocks = (n + BLOCK_SIZE - 1) / BLOCK_SIZE;
    float dt = 0.01f;

    CudaTimer timer;

    // Warmup
    for (int i = 0; i < 10; i++) {
        update_particles_aos<<<blocks, BLOCK_SIZE>>>(d_particles_aos, n, dt);
        apply_force_aos<<<blocks, BLOCK_SIZE>>>(d_particles_aos, n, 1.0f, 1.0f, 1.0f, dt);
    }
    CHECK_CUDA(cudaDeviceSynchronize());

    // Benchmark
    timer.start();
    for (int i = 0; i < ITERATIONS; i++) {
        update_particles_aos<<<blocks, BLOCK_SIZE>>>(d_particles_aos, n, dt);
        apply_force_aos<<<blocks, BLOCK_SIZE>>>(d_particles_aos, n, 1.0f, 1.0f, 1.0f, dt);
    }
    timer.stop();

    float time_ms = timer.elapsed_ms() / ITERATIONS;
    // Each iteration: 2 kernels × (6 reads + 6 writes) = 24 float accesses
    float bandwidth = (24 * n * sizeof(float) / 1e9) / (time_ms / 1000.0f);

    printf("%-30s: %.3f ms, %.2f GB/s\n", "AoS Layout", time_ms, bandwidth);

    CHECK_CUDA(cudaFree(d_particles_aos));
}

void benchmark_soa(int n) {
    // Allocate SoA data
    Particles_SoA h_particles_soa, d_particles_soa;

    CHECK_CUDA(cudaMalloc(&d_particles_soa.x, n * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_particles_soa.y, n * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_particles_soa.z, n * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_particles_soa.vx, n * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_particles_soa.vy, n * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_particles_soa.vz, n * sizeof(float)));

    CHECK_CUDA(cudaMemset(d_particles_soa.x, 0, n * sizeof(float)));
    CHECK_CUDA(cudaMemset(d_particles_soa.y, 0, n * sizeof(float)));
    CHECK_CUDA(cudaMemset(d_particles_soa.z, 0, n * sizeof(float)));
    CHECK_CUDA(cudaMemset(d_particles_soa.vx, 0, n * sizeof(float)));
    CHECK_CUDA(cudaMemset(d_particles_soa.vy, 0, n * sizeof(float)));
    CHECK_CUDA(cudaMemset(d_particles_soa.vz, 0, n * sizeof(float)));

    int blocks = (n + BLOCK_SIZE - 1) / BLOCK_SIZE;
    float dt = 0.01f;

    CudaTimer timer;

    // Warmup
    for (int i = 0; i < 10; i++) {
        update_particles_soa<<<blocks, BLOCK_SIZE>>>(d_particles_soa, n, dt);
        apply_force_soa<<<blocks, BLOCK_SIZE>>>(d_particles_soa, n, 1.0f, 1.0f, 1.0f, dt);
    }
    CHECK_CUDA(cudaDeviceSynchronize());

    // Benchmark
    timer.start();
    for (int i = 0; i < ITERATIONS; i++) {
        update_particles_soa<<<blocks, BLOCK_SIZE>>>(d_particles_soa, n, dt);
        apply_force_soa<<<blocks, BLOCK_SIZE>>>(d_particles_soa, n, 1.0f, 1.0f, 1.0f, dt);
    }
    timer.stop();

    float time_ms = timer.elapsed_ms() / ITERATIONS;
    float bandwidth = (24 * n * sizeof(float) / 1e9) / (time_ms / 1000.0f);

    printf("%-30s: %.3f ms, %.2f GB/s\n", "SoA Layout", time_ms, bandwidth);

    CHECK_CUDA(cudaFree(d_particles_soa.x));
    CHECK_CUDA(cudaFree(d_particles_soa.y));
    CHECK_CUDA(cudaFree(d_particles_soa.z));
    CHECK_CUDA(cudaFree(d_particles_soa.vx));
    CHECK_CUDA(cudaFree(d_particles_soa.vy));
    CHECK_CUDA(cudaFree(d_particles_soa.vz));
}

// ============================================================================
// Main Demonstration
// ============================================================================

int main() {
    cudaDeviceProp prop;
    CHECK_CUDA(cudaGetDeviceProperties(&prop, 0));

    printf("=== Array of Structures (AoS) vs Structure of Arrays (SoA) ===\n");
    printf("Device: %s\n", prop.name);
    printf("Particles: %d (%.2f MB per layout)\n",
           NUM_PARTICLES, NUM_PARTICLES * 6 * sizeof(float) / 1e6);
    printf("\n");

    printf("Data Layout Comparison:\n");
    printf("%-30s  %s  %s\n", "Layout", "Time(ms)", "Bandwidth(GB/s)");
    printf("%-30s  %s  %s\n", "------", "--------", "---------------");

    benchmark_aos(NUM_PARTICLES);
    benchmark_soa(NUM_PARTICLES);

    printf("\n✓ AoS vs SoA comparison complete!\n");

    printf("\nMemory Access Pattern Analysis:\n");
    printf("  AoS (Array of Structures):\n");
    printf("    - Natural C++ representation: Particle p; p.x, p.vx\n");
    printf("    - Strided access: Thread i accesses p[i].x (stride = 24 bytes)\n");
    printf("    - Poor coalescing: Warp needs 6x more transactions\n");
    printf("    - Cache-friendly for single particle operations\n");
    printf("\n");
    printf("  SoA (Structure of Arrays):\n");
    printf("    - GPU-optimized representation: float *x, *vx\n");
    printf("    - Sequential access: Thread i accesses x[i] (stride = 4 bytes)\n");
    printf("    - Perfect coalescing: Warp uses minimal transactions\n");
    printf("    - Typical speedup: 2-4x over AoS\n");

    printf("\nRecommendations:\n");
    printf("  - Use SoA for GPU-intensive computations\n");
    printf("  - Consider AoS for CPU/GPU hybrid algorithms\n");
    printf("  - Convert AoS → SoA before GPU upload if needed\n");
    printf("  - Profile with: ncu --metrics gld_transactions,gld_efficiency\n");

    return 0;
}
