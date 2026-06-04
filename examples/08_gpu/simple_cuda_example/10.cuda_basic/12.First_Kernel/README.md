# 12. First Kernel - Vector Add 2D

## Concept

A classic first GPU program: element-wise addition of two vectors using a
2D grid of thread blocks. Demonstrates kernel declaration, thread indexing,
memory allocation, host-device transfers, and result verification.

## C/CUDA vs Simple

```c
// C/CUDA
__device__ int flat_index(void) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;
    return row * gridDim.x * blockDim.x + col;
}

__global__ void vector_add(float *a, float *b, float *c, int n) {
    int i = flat_index();
    if (i < n) c[i] = a[i] + b[i];
}

// Host
float *d_a, *d_b, *d_c;
cudaMalloc(&d_a, n * sizeof(float));
cudaMemcpy(d_a, h_a, n * sizeof(float), cudaMemcpyHostToDevice);
dim3 block(16, 16);
dim3 grid((width + 15) / 16, (height + 15) / 16);
vector_add<<<grid, block>>>(d_a, d_b, d_c, n);
cudaDeviceSynchronize();
cudaMemcpy(h_c, d_c, n * sizeof(float), cudaMemcpyDeviceToHost);
```

```simple
# Simple
@gpu_device
fn flat_index() -> i64:
    val row = gpu_block_id_y() * gpu_block_dim_y() + gpu_local_id_y()
    val col = gpu_block_id_x() * gpu_block_dim_x() + gpu_local_id_x()
    row * gpu_grid_dim_x() * gpu_block_dim_x() + col

@gpu_kernel
fn vector_add(a: GpuPtr, b: GpuPtr, c: GpuPtr, n: i64):
    val i = flat_index()
    if i < n:
        val va = gpu_load_f32(a, i)
        val vb = gpu_load_f32(b, i)
        gpu_store_f32(c, i, va + vb)

# Host
val d_a = gpu_alloc(n * 4)?
gpu_upload(d_a, host_a_ptr, n * 4)?
val bx = 16; val by = 16
val gx = (width + bx - 1) / bx
val gy = (height + by - 1) / by
vector_add<<<grid: (gx, gy, 1), block: (bx, by, 1)>>>(d_a, d_b, d_c, n)
gpu_sync()?
gpu_download(d_c, host_c_ptr, n * 4)?
```

## Run
```bash
bin/simple examples/simple_cuda_example/10.cuda_basic/12.First_Kernel/main.spl
```
