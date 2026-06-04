# 00. Demo - Hello GPU

## Concept
Introduction to GPU programming in Simple. Demonstrates device detection and a minimal kernel launch.

## C/CUDA vs Simple
| C/CUDA | Simple |
|--------|--------|
| `__global__ void kernel()` | `@gpu_kernel fn kernel():` |
| `kernel<<<1, 1>>>()` | `kernel<<<grid: (1,1,1), block: (1,1,1)>>>()` |
| `cudaGetDeviceCount(&count)` | `gpu_device_count()` |
| `cudaDeviceSynchronize()` | `gpu_sync()?` |

## Run
```bash
bin/simple examples/simple_cuda_example/00.demo/main.spl
```
