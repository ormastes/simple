# Vulkan GPU Examples

This directory contains example programs demonstrating GPU computing with the Vulkan backend in Simple language.

## Prerequisites

1. **Vulkan Drivers**: Install Vulkan drivers for your GPU
   - **Linux**: `sudo apt install mesa-vulkan-drivers vulkan-tools` (or vendor-specific)
   - **Windows**: Included with GPU drivers (NVIDIA/AMD/Intel)
   - **macOS**: Install MoltenVK: `brew install molten-vk`

2. **Verify Installation**:
   ```bash
   vulkaninfo | head -20  # Should show GPU details
   ```

3. **Build Simple with Vulkan Support**:
   ```bash
   cargo build --release --features vulkan
   ```

## Examples

### 1. Vector Addition (`vector_add.spl`)

**Difficulty**: Beginner
**Concepts**: Basic GPU kernel, 1D work groups, device management

The "Hello World" of GPU computing - adds two arrays element-wise.

**Run**:
```bash
./target/release/simple examples/gpu/vulkan/vector_add.spl
```

**Expected Output**:
```
Vector Addition Example
Size: 1024 elements

Verification:
  [0] 0.0 + 0.0 = 0.0 (expected 0.0) ✓
  [1] 1.0 + 2.0 = 3.0 (expected 3.0) ✓
  ...

✓ All results correct!
```

**What You'll Learn**:
- Creating GPU device contexts
- Allocating and transferring buffers
- Launching 1D kernels
- Downloading results
- Resource cleanup

---

### 2. Matrix Multiplication (`matrix_multiply.spl`)

**Difficulty**: Intermediate
**Concepts**: 2D work groups, shared memory, tiled algorithms

Multiplies two 512×512 matrices using both naive and optimized approaches.

**Run**:
```bash
./target/release/simple examples/gpu/vulkan/matrix_multiply.spl
```

**Expected Output**:
```
Matrix Multiplication Example
Dimensions: (512×512) × (512×512)

Running naive kernel...
Naive kernel: 25.3 ms

Running optimized kernel...
Optimized kernel: 2.8 ms

Verification:
✓ Results match (max diff: 0.00001)
✓ Speedup: 9.0×

Performance:
  Operations: 0.268 GFLOP
  Performance: 95.7 GFLOP/s
```

**What You'll Learn**:
- 2D work group configuration
- Shared memory for caching
- Tiled algorithm design
- Performance optimization techniques
- Memory access patterns

---

### 3. Parallel Reduction (`reduction.spl`)

**Difficulty**: Advanced
**Concepts**: Shared memory, tree reduction, atomic operations

Demonstrates two methods for computing sum and maximum: tree-based reduction and atomic operations.

**Run**:
```bash
./target/release/simple examples/gpu/vulkan/reduction.spl
```

**Expected Output**:
```
Sum Reduction Example
Array size: 1000000 elements

CPU reference sum: 5000234.5

Method 1: Tree Reduction
  Result: 5000234.5
  Error: 0.0
  Time: 0.82 ms
  Throughput: 4.88 GB/s

Method 2: Atomic Operations
  Result: 5000234.5
  Error: 0.0
  Time: 3.45 ms
  Speedup vs atomics: 4.2×

===================================================
Max Reduction Example
Array size: 1000000 elements

CPU reference max: 999.9

GPU Result: 999.9
Error: 0.0
Time: 0.75 ms
✓ Correct!
```

**What You'll Learn**:
- Parallel reduction patterns
- Shared memory synchronization
- Atomic operations
- Multi-pass algorithms
- Performance trade-offs

---

### 4. Image Blur (`image_blur.spl`)

**Difficulty**: Advanced
**Concepts**: 2D image processing, separable filters, shared memory caching

Applies Gaussian blur to a 1920×1080 image using separable horizontal and vertical passes.

**Run**:
```bash
./target/release/simple examples/gpu/vulkan/image_blur.spl
```

**Expected Output**:
```
Image Blur Example
Resolution: 1920×1080
Blur radius: 2

Creating test image...
Running naive blur...
Naive blur: 5.2 ms

Running optimized blur...
Optimized blur: 1.8 ms

Verification:
  Max difference: 0.0
  ✓ Results match
  Speedup: 2.9×

Performance:
  Image size: 2.07 megapixels
  Throughput: 1150.0 MP/s

Image preview (1920×1080):
[ASCII art rendering]
```

**What You'll Learn**:
- 2D image processing patterns
- Separable filter optimization
- Row/column caching with shared memory
- Halo regions and boundary handling
- Throughput measurement

---

## Common Patterns

### Basic GPU Workflow

```simple
# 1. Check availability
if !gpu.device_available():
    error("Vulkan not available")

# 2. Create device
device = gpu.Device()

# 3. Allocate and upload buffers
buf_input = device.alloc_buffer(input_data)
buf_output = device.alloc_buffer<f32>(output_size)

# 4. Launch kernel
device.launch_1d(my_kernel, [buf_input, buf_output], size)

# 5. Download results
device.sync()
result = device.download(buf_output)

# 6. Cleanup (automatic on device destruction)
```

### Error Handling

```simple
device = gpu.Device()
if device.handle == 0:
    error("Failed to create GPU device")

buffer = device.alloc_buffer(data)
if buffer.handle == 0:
    error("Failed to allocate buffer")
```

### Performance Measurement

```simple
start = time.now()

# GPU operations
device.launch_kernel(...)

device.sync()  # Wait for completion
elapsed = time.now() - start

print("Time: " + str(elapsed * 1000.0) + " ms")
```

## Troubleshooting

### "Vulkan not available"

**Problem**: GPU or drivers not detected

**Solutions**:
1. Verify drivers: `vulkaninfo`
2. Check permissions (Linux): Add user to `video` group
3. Install correct drivers for your GPU

### Kernel Compilation Fails

**Problem**: SPIR-V generation or validation error

**Solutions**:
1. Check kernel syntax matches Simple GPU syntax
2. Ensure all array accesses are bounds-checked
3. Verify shared memory size is within limits

### Incorrect Results

**Problem**: Output doesn't match expected values

**Solutions**:
1. Add bounds checks to all array accesses
2. Verify work group size divides global size evenly
3. Check for race conditions (use `gpu.barrier()` in shared memory code)
4. Compare with CPU reference implementation

### Poor Performance

**Problem**: GPU slower than expected

**Solutions**:
1. Use shared memory to cache frequently accessed data
2. Ensure work group size is multiple of 32 (warp size)
3. Minimize CPU-GPU transfers (batch operations)
4. Profile with Vulkan tools to find bottlenecks

## Performance Tips

1. **Work Group Size**:
   - Use 256 for 1D kernels
   - Use 16×16 for 2D kernels
   - Must be power of 2 on some GPUs

2. **Memory Access**:
   - Coalesced access (consecutive threads access consecutive memory)
   - Cache in shared memory when reusing data
   - Minimize global memory round trips

3. **Synchronization**:
   - Use `gpu.barrier()` only when necessary
   - Avoid atomics if possible (tree reduction is faster)
   - Batch kernel launches to amortize overhead

4. **Data Transfer**:
   - Transfer large batches, not individual elements
   - Keep data on GPU between kernels
   - Use persistent buffers for repeated operations

## Next Steps

1. **Modify Examples**: Change array sizes, work group sizes, blur radius
2. **Combine Patterns**: Build a complete image processing pipeline
3. **Add Profiling**: Measure memory bandwidth, compute utilization
4. **Explore Advanced Topics**: Multi-GPU, async transfers, subgroups

## Resources

- [Vulkan Backend User Guide](../../../doc/guides/vulkan_backend.md)
- [Vulkan Backend Architecture](../../../doc/architecture/vulkan_backend.md)
- [Vulkan FFI API Reference](../../../doc/api/vulkan_ffi.md)
- [GPU Kernel Specification](../../../doc/spec/gpu_simd.md)

## License

These examples are part of the Simple language project and are provided for educational purposes.
