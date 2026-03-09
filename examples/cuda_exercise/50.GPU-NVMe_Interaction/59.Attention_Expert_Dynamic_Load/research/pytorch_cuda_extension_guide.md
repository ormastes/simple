# Implementing a Custom CUDA Extension in PyTorch (C++/CUDA) Tutorial

Implementing a custom CUDA module in PyTorch can significantly boost performance for specialized operations. In this tutorial, we will create a simple PyTorch extension step-by-step using C++ and CUDA. This includes writing a CUDA kernel, wrapping it with C++ code, building it as a Python module, and using it in PyTorch. We will also cover best practices (memory management, device synchronization) and debugging tips. By the end, you'll understand how to integrate your own CUDA kernels as if they were built-in PyTorch ops.

## Overview

We will implement a basic elementwise addition as an example custom operation. The process involves:
1. Writing a .cu CUDA kernel
2. Creating a C++ wrapper that calls the kernel
3. Exposing the function to Python via PyTorch's extension mechanism
4. Compiling and loading the extension
5. Using the custom op in Python

We'll also mention alternatives like PyCUDA/CuPy and common pitfalls to avoid.

---

## Writing a Custom CUDA Kernel (.cu File)

First, we write a CUDA kernel that performs the core computation. A CUDA kernel is a function marked with `__global__` (executed on the GPU device). The kernel will operate on raw device pointers (from PyTorch tensors) and use CUDA's grid-stride indexing to cover the input data. For our example, we'll implement a simple elementwise addition of two arrays:

```cpp
// File: my_kernel.cu
#include <cuda_runtime.h>

// CUDA kernel: adds arrays a and b into out (each of length N)
__global__ void add_kernel(const float* a, const float* b, float* out, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        out[idx] = a[idx] + b[idx];
    }
}
```

In this kernel, each thread computes one index `idx` by combining its block index and thread index. We include a boundary check `if (idx < N)` to ensure we don't read/write out of bounds. This kernel uses float arrays for simplicity, but you could template it or use `#ifdef __half` etc. for other data types. The `__global__` qualifier means it can be launched from host code. We will launch `add_kernel` with an appropriate grid and block size so that `idx` spans all elements.

> **Note**: For best performance, choose a block size (e.g. 256 threads) and compute grid size as `blocks = (N + blockDim.x - 1) / blockDim.x` to cover N elements. You could also use 2D grids for 2D data, but here 1D indexing suffices. In more complex kernels, consider memory coalescing and shared memory usage for optimization, though we won't dive into those here.

---

## Creating the C++ Interface Wrapper

Next, we create a C++ function that will be called from Python. This wrapper will accept PyTorch tensors, prepare the data for the CUDA kernel (check types, device, allocate output), and launch the kernel. We also ensure synchronization and error checking. Here's an example C++ wrapper:

```cpp
// File: my_extension.cpp
#include <torch/extension.h>
#include <c10/cuda/CUDAGuard.h>  // For device guard
#include <cuda_runtime.h>
#include <stdexcept>

// Forward declare the CUDA kernel (defined in my_kernel.cu)
__global__ void add_kernel(const float* a, const float* b, float* out, int N);

// C++ API function that wraps the CUDA kernel
torch::Tensor add_cuda(torch::Tensor a, torch::Tensor b) {
    // Input validation
    TORCH_CHECK(a.device().is_cuda() && b.device().is_cuda(),
                "Tensors must be CUDA, but got devices: ", a.device(), " and ", b.device());
    TORCH_CHECK(a.dtype() == b.dtype(), "Input tensors must have the same data type");
    TORCH_CHECK(a.sizes() == b.sizes(), "Input tensors must have the same shape");
    TORCH_CHECK(a.is_contiguous() && b.is_contiguous(), "Tensors must be contiguous");

    // Set CUDA device context to the inputs' device (important for multi-GPU)
    const at::cuda::OptionalCUDAGuard device_guard(device_of(a));

    // Ensure inputs are of type float (for this example kernel)
    TORCH_CHECK(a.scalar_type() == torch::kFloat32, "Only float32 supported in this example");
    // (If other dtypes are needed, you could dispatch or template the kernel)

    // Allocate output tensor on the same device and dtype as input
    torch::Tensor out = torch::empty_like(a);  // same shape, dtype, device as a

    // Launch CUDA kernel (1D grid)
    int N = a.numel();
    int threads = 256;
    int blocks = (N + threads - 1) / threads;
    add_kernel<<<blocks, threads>>>(a.data_ptr<float>(), b.data_ptr<float>(),
                                     out.data_ptr<float>(), N);

    // Check for any kernel launch errors
    auto err = cudaGetLastError();
    TORCH_CHECK(err == cudaSuccess, "CUDA kernel failed: ", cudaGetErrorString(err));

    return out;
}
```

In this C++ code, we use `torch::Tensor` (PyTorch's C++ tensor type) for inputs and output. We perform several checks: both tensors must be on CUDA and have the same shape/type. We ensure they are contiguous in memory; if not, one could call `a = a.contiguous()` (here we simply check/assume contiguity). We then use `at::cuda::OptionalCUDAGuard` to set the current CUDA device to the device of tensor `a`. This step is crucial if you might call the function on non-default GPUs – it ensures the kernel runs on the correct device and uses the proper CUDA stream.

We allocate an output tensor with `torch::empty_like(a)`, which uses PyTorch's memory allocator on the same device as `a`. Using PyTorch's allocator is recommended because it manages GPU memory efficiently via a caching allocator (avoiding costly cudaMalloc/free calls). The output tensor's memory will be freed or reused by PyTorch when it's no longer needed, so we don't manually free anything.

Finally, we launch the CUDA kernel with the calculated grid and block dimensions. After launching, we call `cudaGetLastError()` to catch any asynchronous launch errors. We wrap this in `TORCH_CHECK` so that any error will raise a Python RuntimeError with the CUDA error string. We do not call `cudaDeviceSynchronize()` here because that would stall the GPU; PyTorch will implicitly synchronize as needed (e.g., when copying results to CPU or during subsequent blocking operations). If an error occurs, however, it will be caught by the next synchronization or by the cudaGetLastError check we included.

> **Memory note**: By using `torch::empty_like`, the output tensor's memory is managed by PyTorch. Avoid using cudaMalloc/cudaFree inside your extension if possible; instead use PyTorch tensor factories (empty, zeros, etc.) so that memory is accounted for in PyTorch's CUDA memory manager. This also avoids device synchronization on allocation/deallocation thanks to the caching allocator.

---

## Binding the C++ Extension to Python

The next step is to expose our C++ function (`add_cuda`) to Python. PyTorch uses pybind11 under the hood for C++ extensions, and `torch/extension.h` provides a convenient macro to create the Python module. We add the following at the bottom of our C++ file:

```cpp
// Bind the C++ function to a Python module
PYBIND11_MODULE(TORCH_EXTENSION_NAME, m) {
    m.def("add_cuda", &add_cuda, "Add two tensors on CUDA (C++/CUDA extension)");
}
```

When the extension is compiled, `TORCH_EXTENSION_NAME` will be replaced with the actual module name. This code uses `m.def` to define a Python function `add_cuda` in the module, which calls our C++ `add_cuda` function. Once built and loaded, we will be able to do `import my_extension` (or whatever name we choose) in Python and call `my_extension.add_cuda(t1, t2)`.

**A few important points:**

- The module name provided in the build step (explained next) must match the name used when loading or importing. PyTorch's build utility handles `TORCH_EXTENSION_NAME` automatically.
- You can bind multiple functions or classes in one module using additional `m.def(...)` calls. In our example we expose only one function.
- The signature in `m.def` automatically converts between PyTorch Python tensors and C++ `torch::Tensor` objects. This means when you call `add_cuda` in Python with `torch.Tensor` arguments, it will call our C++ function with the corresponding `torch::Tensor` references.

---

## Building and Loading the Extension in Python

Now that we have our CUDA kernel and C++ code ready, we need to compile them into a Python module. PyTorch provides utilities to make this straightforward. There are two approaches:

### Ahead-of-Time Compilation with setup.py

For a permanent extension (for example, part of a package or a project), you can build the extension using a `setup.py` script. This leverages setuptools and PyTorch's `BuildExtension`. In our example, create a `setup.py` in the same directory:

```python
# File: setup.py
from setuptools import setup
from torch.utils.cpp_extension import CUDAExtension, BuildExtension

setup(
    name="my_extension",  # name of the package or extension
    ext_modules=[
        CUDAExtension(
            "my_extension",  # name of the resulting Python module
            ["my_extension.cpp", "my_kernel.cu"]  # our source files
        )
    ],
    cmdclass={"build_ext": BuildExtension}
)
```

Here we use `torch.utils.cpp_extension.CUDAExtension` since we have CUDA source files. This ensures NVCC is invoked for .cu files automatically. The `BuildExtension` class takes care of setting include paths (for PyTorch headers) and linking against PyTorch libraries, so we don't have to specify those manually. To compile, run in a terminal:

```bash
python setup.py build_ext --inplace
```

This will build the extension and produce a shared library (e.g., `my_extension.so` or `my_extension.pyd` depending on OS) in the current directory. The `--inplace` flag means the compiled extension is placed next to the source (useful for development). Alternatively, you can install the extension system-wide/in an environment with `pip install .` which will build and install the package.

After building, you can import the module in Python like a normal package:

```python
import my_extension
print(my_extension.add_cuda)  # should show a function available
```

**Important**: When using setuptools, make sure your .cpp and .cu files have different base names. For example, `my_extension.cpp` and `my_extension.cu` is fine, but if they were both named `my_extension.*` it can confuse the build system. In our case, we used distinct filenames. The name in `CUDAExtension("my_extension", [...])` should match the module name used in `PYBIND11_MODULE`. Here we've set it to `"my_extension"`.

### Just-In-Time Compilation (JIT) with load()

For quick experimentation or when distributing source, PyTorch allows on-the-fly compilation via `torch.utils.cpp_extension.load`. This function compiles the given sources at runtime and loads the extension module directly. You can use it in your Python code as follows:

```python
from torch.utils.cpp_extension import load
ext_module = load(name="my_extension", sources=["my_extension.cpp", "my_kernel.cu"], verbose=True)
```

The `load` function will internally invoke the compiler (using Ninja by default) to build the extension. If `verbose=True`, you'll see the build log, which can help if errors occur. Under the hood, this creates a temporary build directory (e.g., `/tmp/torch_extensions/my_extension` on Linux) and compiles the sources with the appropriate compilers (g++ for C++ files and nvcc for CUDA files). The resulting compiled module is loaded as `ext_module`. The name you provide (here `"my_extension"`) is used to name the build folder and the module.

Once loaded, you use `ext_module.add_cuda` just like any function. You can also import it via `import importlib; importlib.import_module("my_extension")` if needed, but typically you keep the returned module reference. If you run the script again without changes to the source, the cached binary will be reused (to force rebuild, you might need to delete the cache folder or use `force=True` in load).

**Which method to choose?** For development and debugging, JIT loading is very convenient (no need to manage a setup.py file manually). For deploying your extension or sharing it, an ahead-of-time build (which produces a wheel or installed module) is more suitable. In both cases, the compiled code is essentially the same and will be optimized by the compiler as usual.

---

## Best Practices for CUDA Extensions (Memory Management & Synchronization)

Integrating custom CUDA code into PyTorch requires care to ensure it works correctly and efficiently. Here are some best practices regarding memory and synchronization:

1. **Use PyTorch Tensors for memory management**: Allocate any new tensors (outputs, temporary buffers) using functions like `torch::empty` or `at::zeros` with the correct device options (e.g., `torch::empty_like(input)` as we did). This way, you leverage PyTorch's caching allocator, which recycles GPU memory without unnecessary cudaFree calls. It also means PyTorch is aware of the memory usage. Avoid using raw cudaMalloc/cudaFree in your C++ code if possible. If you must allocate device memory outside of PyTorch, make sure to free it to avoid memory leaks.

2. **Device management**: If there's a chance your code will run on different GPU devices (e.g., in a multi-GPU server), guard your kernels with the appropriate device context. Using `at::cuda::CUDAGuard` (or `OptionalCUDAGuard`) is the recommended way to ensure that the current CUDA device is set to the device of your input tensors. In our example, we use `device_of(a)` to lock to a's device. This prevents issues where kernels inadvertently run on GPU 0 or access memory on the wrong device, which can lead to crashes or incorrect results in multi-GPU setups.

3. **Tensor properties**: Check that input tensors meet any requirements your kernel assumes. Common checks:
   - **Device** (on CUDA vs CPU) – we used `TORCH_CHECK(tensor.is_cuda())`.
   - **Data type** – ensure the tensor dtype matches what your kernel expects (we checked for Float32 in our example).
   - **Contiguity** – non-contiguous tensors have disjoint memory strides. If your kernel assumes a flat memory layout, call `.contiguous()` on inputs (or enforce contiguity as we did). Otherwise, you might iterate wrong or need to handle strides in the kernel.
   - **Shapes** – verify dimensions if needed (we checked shapes of a and b are equal).

   Use `TORCH_CHECK` (or older `AT_ASSERTM`) to validate these conditions and provide clear error messages to the user. The macro will throw a Python RuntimeError if the condition fails, which is preferable to a low-level crash.

4. **Launching kernels and streams**: By default, PyTorch operations (and your extension when called from Python) run on the default CUDA stream of the current device. Unless you explicitly manage streams, you can assume sequential execution order for your kernels relative to other operations on the same device. If you need to use custom CUDA streams for concurrency, you'll have to integrate that carefully (beyond this tutorial's scope). Typically, stick to the default stream for simplicity.

5. **Device synchronization**: One advantage of writing a C++/CUDA extension is that you have control over synchronization. In general, **do not** call `cudaDeviceSynchronize()` inside your extension unless absolutely necessary for correctness or debugging. For performance, let operations run asynchronously. PyTorch will synchronize when it needs to (for example, if you copy a tensor to CPU or during backward operations if required). Unwarranted synchronization will stall the GPU pipeline and hurt throughput. Instead, use error checking like `cudaGetLastError()` as we showed to catch issues without forcing a sync. An exception is during debugging (see below) – but those measures should be removed or disabled in production code.

6. **Error handling**: Always check for CUDA errors after launching kernels. If a kernel reads/writes out of bounds or runs into an illegal memory access, it won't immediately crash your program – the error is reported when synchronizing or checking the last error. By inserting an error check (`cudaGetLastError`) and using `TORCH_CHECK`, you convert these failures into Python exceptions at the right time with a useful message. This makes debugging easier and prevents silently ignoring errors.

7. **Autograd support**: Our example focuses on a forward operation. If you need your custom op to be differentiable (i.e. used in `loss.backward()`), you have a few options. One is to implement a matching backward function in C++/CUDA and register it with PyTorch's dispatcher or use `torch::autograd` interfaces. Another simpler approach is to wrap your extension call in a custom `torch.autograd.Function` in Python and provide a `backward()` that calls either another extension or uses existing PyTorch ops. Covering autograd implementations is beyond this tutorial, but be aware that by default, a custom C++ function will not have autograd support (if you call it with tensors that require grad, PyTorch will treat it as a leaf and either won't compute gradients or will give an error if used in a differentiable context). For many use cases (e.g., custom layers in models), you may need to implement the backward pass similarly to the forward.

---

## Example Usage of the Custom Module

With the extension built (either via setup.py or JIT), using it in Python is straightforward. Below is a simple demonstration:

```python
import torch
import my_extension  # Import the built extension (after setup.py build)
# If using JIT load, use ext_module from load() instead of importing

# Prepare sample inputs
a = torch.tensor([1.0, 2.0, 3.0], device='cuda')
b = torch.tensor([4.0, 5.0, 6.0], device='cuda')
print("Input A:", a)
print("Input B:", b)

# Use the custom CUDA function
out = my_extension.add_cuda(a, b)
print("Output (A+B):", out)  # should be [5.0, 7.0, 9.0] on CUDA
```

**Output:**
```
Input A: tensor([1., 2., 3.], device='cuda:0')
Input B: tensor([4., 5., 6.], device='cuda:0')
Output (A+B): tensor([5., 7., 9.], device='cuda:0')
```

As shown, `my_extension.add_cuda` behaves like a regular PyTorch function. You can integrate this into an `nn.Module` or script it with TorchScript if needed (extensions are compatible with TorchScript as long as they're compiled in). If the extension was built properly, it will use the GPU to compute the result. You can verify that by profiling or by introducing a large input and comparing speed to an equivalent Python operation.

We can also incorporate the custom op into a `nn.Module` for use in models:

```python
class AddModule(torch.nn.Module):
    def forward(self, x, y):
        return my_extension.add_cuda(x, y)

# Example usage in a model's forward:
add_mod = AddModule().cuda()
res = add_mod(a, b)
```

This way, our custom CUDA operation can be part of larger models and trained/evaluated like standard layers (keeping in mind the autograd caveat – without a custom backward, it won't backpropagate gradients).

---

## Alternatives: PyCUDA, CuPy, and Other Approaches

Writing a C++/CUDA extension is powerful and gives high performance, but it requires working in C++/CUDA and compiling code. There are alternatives for running custom CUDA code in Python:

- **PyCUDA**: PyCUDA allows you to write CUDA kernels as strings in Python and compile them at runtime. It provides a Pythonic API to launch kernels and manage device memory. This can be more convenient for quick experimentation since you stay in Python. However, PyCUDA operates outside of PyTorch's autograd and tensor abstractions. You would typically have to convert PyTorch tensors to PyCUDA GPUArray objects (for example by using the tensor's CUDA buffer pointer) and vice versa. This involves some boilerplate and care with memory pointers. PyCUDA is great for standalone CUDA programming in Python, but integrating it with PyTorch means you lose automatic differentiation and need to manage synchronization manually. Essentially, PyCUDA gives you a raw interface to CUDA drivers from Python – you can achieve the same performance as a C++ extension since the kernel code is identical, but you don't get tight integration with PyTorch (no direct autograd support, etc.).

- **CuPy**: CuPy is a NumPy-like library that runs on CUDA. It can allocate GPU arrays and has many optimized routines. CuPy also lets you define custom CUDA kernels using Python strings or even NumPy ufunc-like elementwise kernels. You can convert between PyTorch tensors and CuPy arrays using DLPack, a protocol for sharing tensor memory across libraries. This means you could in principle write a custom operation with CuPy and then convert the result back to a PyTorch tensor, all on GPU. The advantage is you stay in Python and leverage CuPy's kernel compilation. The disadvantage is similar to PyCUDA: it's outside of PyTorch's native system, so autograd won't track operations done in CuPy unless you manually implement it. It's a viable option for certain tasks or prototyping, especially if you don't want to write C++ – but it introduces an extra dependency and integration layer.

- **Numba**: Numba's CUDA support allows you to write Python functions and JIT-compile them to CUDA kernels with the `@cuda.jit` decorator. You could use Numba to define a kernel and launch it on PyTorch data by obtaining the underlying device pointer (again via DLPack or the `.data_ptr()` method). Numba is quite handy for simpler kernels or when you want to avoid writing C++ completely. However, you'll still need to handle the interop with PyTorch manually, and Numba might not achieve the same level of optimization as nvcc for complex kernels (though it's improving). Also, like the above, any operation you do with Numba is invisible to PyTorch's autograd.

- **TorchScript/Triton**: A more recent alternative for certain types of custom ops is PyTorch Triton, which allows writing CUDA-like kernels in Python that integrate with PyTorch. Triton is especially used for matrix multiplication and fusion in PyTorch 2.x and can sometimes be used without writing full C++ extensions. It aims to offer the ease of Python with performance close to optimized CUDA. This is an advanced topic, but worth noting as an emerging option. TorchScript, on the other hand, can fuse certain operations or optimize Python code, but it doesn't let you write arbitrary new CUDA kernels – it's more about graph-level optimization.

**When to use a C++/CUDA extension vs alternatives?** If you need maximum performance and full integration (especially if you plan to distribute the custom op or use it in production), a C++/CUDA extension is the robust choice. It becomes a first-class PyTorch op (you can even register it with `torch.ops` or the dispatcher for reuse) and will work with `torch.jit`, etc., once properly set up. If you're prototyping or need a quick one-off GPU computation, using PyCUDA or CuPy might be faster to develop since you can iterate in Python. Keep in mind the maintenance: a PyTorch extension compiled for a specific PyTorch/CUDA version might need recompiling when those are upgraded, whereas something like CuPy (if it uses runtime compilation) might be more version-agnostic. In summary, **PyCUDA/CuPy offer ease of use, while C++/CUDA extensions offer better integration and possibly better performance for complex tasks**.

---

## Debugging Tips and Common Pitfalls

Developing custom CUDA code can be tricky. Here are some common pitfalls and tips to debug them:

1. **Mismatched devices or forgetting cuda()**: A very common mistake is to call the custom op with a CPU tensor by accident (or mismatched devices for inputs). This will likely trigger the check we added (`TORCH_CHECK` for `.is_cuda()`). Always ensure your tensors are on CUDA before calling the extension. If you see errors about device mismatch or a message like "expected CUDA tensor," move your data to the GPU with `tensor.to('cuda')` or `tensor.cuda()`.

2. **Multi-GPU issues**: If you run your code on a GPU other than cuda:0, ensure you're using `CUDAGuard` as shown. A symptom of not doing so is an "illegal memory access" on non-zero GPUs or all computation seeming to happen on GPU0. The fix is to use `at::cuda::CUDAGuard` with the appropriate device. If you forget this, the kernel might run on the wrong device and read invalid memory addresses.

3. **Non-contiguous tensors**: If your kernel assumes contiguous memory but you pass a non-contiguous tensor (e.g., slicing a tensor creates a view that might not be contiguous), you could get incorrect results or crashes. The solution is to call `.contiguous()` on inputs (we did a check and you could use `a = a.contiguous()` in the wrapper). A related pitfall is not accounting for strides in your kernel if you intend to support non-contiguous inputs.

4. **Data type mismatch**: Make sure the C++ side uses the correct data type when calling `data_ptr<T>()`. If `tensor.dtype` is `torch.float32` but you mistakenly use `data_ptr<double>()`, you'll read incorrect values and likely crash. Our example guarded that by checking `scalar_type()`. For generic code, you might use templates or the ATen dispatch macros to handle multiple types. A quick debugging step if you suspect type issues is to print `tensor.dtype` in Python or use `TORCH_CHECK` on `tensor.scalar_type()` in C++.

5. **Kernel launch failures**: If your kernel configuration is wrong (e.g., too many threads or using an invalid memory access), it may silently fail. Always check `cudaGetLastError()` as we did, or run your Python script with the environment variable `CUDA_LAUNCH_BLOCKING=1`. Setting this makes kernel launches synchronous, so if a kernel errors, the program will crash at the point of launch, and the stack trace will point to the extension call. This is extremely useful for debugging illegal memory accesses or launch configuration errors. Remember to remove or unset `CUDA_LAUNCH_BLOCKING` for normal runs, as it will degrade performance.

6. **Using the wrong compiler or flags**: The PyTorch build utilities usually pick the right compiler and CUDA toolkit. However, ensure that your system's CUDA toolkit version is compatible with the one PyTorch was built with. If you hit build errors, check that you have e.g. `nvcc` available and that `CUDA_HOME` is set if needed. The `verbose=True` flag in `load()` will show the compile commands, which can help pinpoint what include or library might be missing.

7. **Name collisions and imports**: If you change the extension name or have multiple extensions, be careful with naming. Importing a module with the same name as a different one can lead to confusion. Also, if you recompile an extension in place, you might need to restart your Python session or unload the old module to avoid conflicts. Using `torch.utils.cpp_extension.load`, it will reload if sources changed, but if you use `setup.py develop`, you may need to restart to pick up changes.

8. **Debugging inside kernels**: Standard debugging (like using a debugger) is harder for GPU kernels. Tools like `cuda-gdb` or Nsight can be used to step through device code if needed. A simpler approach is to use `printf` inside the kernel for small data to trace values (remember to call `cudaDeviceSynchronize()` after to flush output, and remove these after debugging). Another tool is `cuda-memcheck`, which can detect out-of-bounds memory errors in kernels. You can run your script with `cuda-memcheck python script.py` to get detailed memory error reports.

9. **Performance pitfalls**: After getting correctness, you might find your custom kernel is slower than expected. Common performance issues include non-coalesced memory access, not using shared memory or on-chip resources, and launch configuration not optimized. Profiling your kernel with Nsight Systems/Profiler or printing timing with `torch.cuda.synchronize()` can help. As a baseline, compare with equivalent PyTorch ops (if any) to see the overhead. Remember that very small kernels might be slower than PyTorch's built-in ops due to launch overhead – GPU excels with large parallel workloads. If your custom op is simple and short, consider whether the overhead is worth it or if you can fuse it with other operations.

By following this tutorial and keeping these tips in mind, you can create efficient and robust custom CUDA modules in PyTorch. This allows you to extend PyTorch's capabilities with your own high-performance code, all while interfacing seamlessly with the Python API and PyTorch's tensor ecosystem. Happy coding!

---

## Sources

1. PyTorch documentation – Custom C++/CUDA Extensions
2. PyTorch Forums – device guard necessity for multi-GPU
3. PyTorch extension tutorial (LLTM example) – input checks and module definition
4. Chris Choy's CUDA extension tutorial – example kernel and error check
5. Derek Chiou's blog – C++ wrapper example and usage of torch::empty
6. Colfax Research tutorial – notes on contiguous tensors and device checks
7. Reddit CUDA discussion – notes on PyCUDA vs CUDA C++ (host code vs kernel code)
8. DLPack documentation – sharing tensors between PyTorch and CuPy (zero-copy)
