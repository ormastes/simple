# Exercise 18: Thread Hierarchy

## GPU Thread Organization

CUDA organizes threads into a two-level hierarchy: **grids** of **blocks**.
Simple exposes the same model through built-in intrinsics.

### Hierarchy

```
Grid (all blocks)
 +-- Block (0,0)     Block (1,0)     Block (2,0)
 |    +-- Thread 0    +-- Thread 0    +-- Thread 0
 |    +-- Thread 1    +-- Thread 1    +-- Thread 1
 |    +-- ...         +-- ...         +-- ...
 +-- Block (0,1)     Block (1,1)     Block (2,1)
      +-- Thread 0    +-- Thread 0    +-- Thread 0
      ...             ...             ...
```

### Simple Intrinsics

| Simple | CUDA | Description |
|--------|------|-------------|
| `gpu_block_id_x()` | `blockIdx.x` | Block index in grid (x) |
| `gpu_block_id_y()` | `blockIdx.y` | Block index in grid (y) |
| `gpu_block_dim_x()` | `blockDim.x` | Threads per block (x) |
| `gpu_block_dim_y()` | `blockDim.y` | Threads per block (y) |
| `gpu_local_id_x()` | `threadIdx.x` | Thread index in block (x) |
| `gpu_local_id_y()` | `threadIdx.y` | Thread index in block (y) |
| `gpu_grid_dim_x()` | `gridDim.x` | Blocks per grid (x) |
| `gpu_grid_dim_y()` | `gridDim.y` | Blocks per grid (y) |

### Global Thread ID Calculation

```simple
val global_x = gpu_block_id_x() * gpu_block_dim_x() + gpu_local_id_x()
val global_y = gpu_block_id_y() * gpu_block_dim_y() + gpu_local_id_y()
```

### Launch Configuration

```simple
# 1D launch: N elements with 256 threads per block
val block = (256, 1, 1)
val grid = ((n + 255) / 256, 1, 1)
kernel<<<grid: grid, block: block>>>(args)

# 2D launch: NxM matrix with 16x16 thread blocks
val block = (16, 16, 1)
val grid = ((cols + 15) / 16, (rows + 15) / 16, 1)
kernel<<<grid: grid, block: block>>>(args)
```

### Choosing Block Size

- Must be a multiple of warp size (32) for full utilization
- Common choices: 128, 256, 512 threads per block
- Max 1024 threads per block on most hardware
- 2D blocks: 16x16=256 or 32x32=1024

## Files

- `main.spl` - Multiple kernel variants with different grid/block configurations
- `spec.spl` - Tests verifying all configurations produce correct results

## Learning Goals

- Map thread IDs to data indices
- Choose appropriate block and grid dimensions
- Handle boundary conditions when data size is not a multiple of block size
- Understand 1D vs 2D thread layouts
