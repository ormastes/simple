# Making Custom CUDA Extensions "Native" in PyTorch

Here's the practical checklist for making your C++/CUDA extension "feel native" in PyTorch—so it plugs into autograd, AMP, torch.compile, vmap, CUDA Graphs, memory/stream semantics, etc.

---

## 1) Register your op with the Dispatcher (not just pybind)

Don't only expose a pybind function. Declare a schema and register per-backend kernels so PyTorch's dispatcher can route calls and layer features (autograd, autocast, vmap) on top.

```cpp
// 1) Schema
TORCH_LIBRARY(myops, m) {
  m.def("myadd(Tensor a, Tensor b) -> Tensor");
}

// 2) CUDA implementation
Tensor myadd_cuda(const Tensor& a, const Tensor& b) { /* launch your kernel */ }

TORCH_LIBRARY_IMPL(myops, CUDA, m) {
  m.impl("myadd", myadd_cuda);
}
```

**Why this matters**: the dispatcher automatically handles things like Autograd → backend, Autocast, vmap, etc., when you provide the right registrations.

---

## 2) Make it autograd-aware (forward/backward)

If your op needs gradients, register an Autograd kernel that calls your inference kernel and defines a backward:

```cpp
class MyAddFn : public torch::autograd::Function<MyAddFn> {
 public:
  static Tensor forward(AutogradContext* ctx, Tensor a, Tensor b) {
    // call back into dispatcher to reach CUDA/CPU kernels
    static auto op = torch::Dispatcher::singleton()
        .findSchemaOrThrow("myops::myadd","").typed<Tensor (Tensor,Tensor)>();
    return op.call(a, b);
  }
  static tensor_list backward(AutogradContext*, tensor_list g) {
    auto grad = g[0];
    return {grad, grad}; // d(a+b)/da = 1, d/db = 1
  }
};

TORCH_LIBRARY_IMPL(myops, Autograd, m) {
  m.impl("myadd", [](const Tensor& a, const Tensor& b){
    return MyAddFn::apply(a, b)[0];
  });
}
```

This pattern ("Autograd kernel redispatches to CUDA/CPU") is the supported way to integrate with the dispatcher's autograd layering.

> If the op doesn't support gradients, still register the Autograd fallback (autogradNotImplementedFallback) so gradient flows fail clearly rather than silently dropping requires_grad.

---

## 3) Mixed precision (AMP) / autocast

To participate in `torch.cuda.amp.autocast`, register an Autocast wrapper kernel for your op that casts inputs to the preferred compute dtype (e.g., FP16/BF16) before redispatching to the backend kernel:

**Create an Autocast dispatch kernel that:**
1. checks autocast state,
2. casts inputs to a compute dtype (like `at::kHalf`/`at::kBFloat16`),
3. calls the underlying op via the dispatcher.

```cpp
TORCH_LIBRARY_IMPL(myops, Autocast, m) {
  m.impl("myadd", [](const Tensor& a, const Tensor& b) {
    c10::impl::ExcludeDispatchKeyGuard no_autocast(c10::DispatchKey::Autocast);

    // Cast to lower precision if autocast is enabled
    auto exec_type = at::autocast::get_autocast_gpu_dtype();
    auto a_casted = at::autocast::cached_cast(exec_type, a);
    auto b_casted = at::autocast::cached_cast(exec_type, b);

    // Redispatch to actual implementation
    static auto op = torch::Dispatcher::singleton()
        .findSchemaOrThrow("myops::myadd","").typed<Tensor (Tensor,Tensor)>();
    return op.call(a_casted, b_casted);
  });
}
```

The dispatcher tutorial shows that Autocast is a dispatch key you can target so your op is included in AMP graphs.

---

## 4) Play nicely with torch.compile

`torch.compile` (Dynamo→Inductor) treats registered custom ops as first-class call sites. It will compile/fuse around them; your kernel runs as an external call. (Direct "fusion inside your custom op" is not automatic—lowering into Inductor IR is possible via internal APIs but not stable/official.) Registering via `TORCH_LIBRARY(_IMPL)` is the key to being seen by the compiler stack.

**Tip**: keep signatures/pure-tensor I/O clean and avoid hidden side effects—this improves compile-ability.

---

## 5) Work with CUDA Graphs (kill launch overhead)

If users wrap their step in a `torch.cuda.CUDAGraph`, your op can be captured as long as it doesn't call `cudaMalloc`/`cudaFree` or do other non-capturable things. Use PyTorch tensor factories (`torch::empty_like`) so allocations go through the caching allocator (graph-friendly), and avoid host syncs in the hot path.

---

## 6) Streams & memory lifetime (zero surprises)

- Use `at::cuda::CUDAGuard guard(device_of(tensor));` so kernels launch on the right device.
- If your op uses a tensor on a different stream than it was allocated on, call `tensor.record_stream(stream)` so the caching allocator won't reuse its memory too early. This is crucial for multi-stream correctness.

```cpp
// Example: custom stream usage
at::cuda::CUDAStream custom_stream = at::cuda::getStreamFromPool();
{
  at::cuda::CUDAStreamGuard stream_guard(custom_stream);
  // Launch kernel on custom stream
  my_kernel<<<blocks, threads, 0, custom_stream>>>(/*...*/);

  // Record stream so memory isn't freed early
  output_tensor.record_stream(custom_stream);
}
```

---

## 7) vmap / batching rules (optional but nice)

If you want `torch.vmap` to batch over your custom op, provide a batching rule (Python-side via `torch.library`) or relevant dispatcher registrations so the system knows how to add a batch dimension. This is part of the "custom operators" guidance.

---

## 8) Dtypes, layouts, and contiguity

- Support the dtypes you need via templating or small switches, and `TORCH_CHECK` early for unsupported types/layouts.
- Consider channels-last or non-contiguous inputs: either `.contiguous()` in your wrapper or implement stride-aware kernels.
- Use `TensorIterator` when possible for elementwise patterns—it handles dtype casting, broadcasting, and parallelization for you (handy for CPU; on CUDA you can still benefit for simple ops).

```cpp
// Template example for multiple dtypes
template<typename scalar_t>
__global__ void typed_kernel(const scalar_t* a, const scalar_t* b, scalar_t* out, int N) {
  int idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx < N) out[idx] = a[idx] + b[idx];
}

// Dispatch based on dtype
Tensor my_typed_add(Tensor a, Tensor b) {
  auto out = torch::empty_like(a);
  AT_DISPATCH_FLOATING_TYPES_AND_HALF(a.scalar_type(), "my_typed_add", [&] {
    typed_kernel<scalar_t><<<blocks, threads>>>(
        a.data_ptr<scalar_t>(), b.data_ptr<scalar_t>(),
        out.data_ptr<scalar_t>(), a.numel());
  });
  return out;
}
```

---

## 9) Minimal "pro" wrapper you can copy

The common, "plays well with PyTorch" CUDA wrapper looks like:

```cpp
#include <torch/extension.h>
#include <c10/cuda/CUDAGuard.h>

__global__ void my_kernel(/*...*/){/*...*/}

at::Tensor myadd_cuda(at::Tensor a, at::Tensor b) {
  TORCH_CHECK(a.is_cuda() && b.is_cuda());
  TORCH_CHECK(a.sizes() == b.sizes());
  const at::cuda::OptionalCUDAGuard guard(device_of(a));
  auto out = at::empty_like(a);            // allocator-friendly (graphs OK)
  int N = a.numel();
  int threads = 256, blocks = (N + threads - 1) / threads;
  my_kernel<<<blocks, threads>>>(
      a.data_ptr<float>(), b.data_ptr<float>(), out.data_ptr<float>(), N);
  TORCH_CHECK(cudaGetLastError() == cudaSuccess);
  return out;
}

// Schema + impl (see §1)
TORCH_LIBRARY(myops, m) { m.def("myadd(Tensor a, Tensor b) -> Tensor"); }
TORCH_LIBRARY_IMPL(myops, CUDA, m) { m.impl("myadd", myadd_cuda); }
```

This already cooperates with `torch.compile`, CUDA Graphs, and AMP (once you add an Autocast wrapper). It also respects device routing and allocator/stream semantics.

---

## 10) Quick "feature matrix" and how to opt-in

| PyTorch feature | What you must do |
|-----------------|------------------|
| **Autograd** | Register an Autograd kernel (or Python `autograd.Function`) that redispatches to your backend kernel and implements backward. |
| **AMP / autocast** | Register an Autocast kernel (dispatch key) that casts to compute dtype then redispatches. |
| **torch.compile** | Use `TORCH_LIBRARY/_IMPL` registration; keep signatures tensor-in/tensor-out. (Inductor won't fuse your opaque kernel by default.) |
| **CUDA Graphs** | Avoid raw `cudaMalloc`/`free` & host syncs; allocate via `at::empty_like`; your op will capture & replay fine. |
| **vmap** | Provide batching rule via `torch.library` if needed. |
| **Streams/Lifetime** | Guard device with `CUDAGuard`; if using non-origin streams, call `tensor.record_stream(stream)`. |

---

## 11) Complete Example with All Features

Here's a complete minimal example that includes dispatcher registration, autograd, and autocast support:

```cpp
// my_native_op.cpp
#include <torch/extension.h>
#include <c10/cuda/CUDAGuard.h>

// Forward declaration of CUDA kernel
__global__ void add_kernel_cuda(const float* a, const float* b, float* out, int N);

// CUDA implementation (backend kernel)
at::Tensor add_cuda_impl(const at::Tensor& a, const at::Tensor& b) {
  TORCH_CHECK(a.is_cuda() && b.is_cuda(), "Inputs must be CUDA tensors");
  TORCH_CHECK(a.sizes() == b.sizes(), "Input shapes must match");
  TORCH_CHECK(a.is_contiguous() && b.is_contiguous(), "Inputs must be contiguous");

  const at::cuda::OptionalCUDAGuard device_guard(device_of(a));
  auto out = at::empty_like(a);

  int N = a.numel();
  int threads = 256;
  int blocks = (N + threads - 1) / threads;

  add_kernel_cuda<<<blocks, threads>>>(
      a.data_ptr<float>(), b.data_ptr<float>(), out.data_ptr<float>(), N);

  TORCH_CHECK(cudaGetLastError() == cudaSuccess, "Kernel launch failed");
  return out;
}

// Autograd function
class AddAutogradFunction : public torch::autograd::Function<AddAutogradFunction> {
 public:
  static at::Tensor forward(
      torch::autograd::AutogradContext* ctx,
      const at::Tensor& a,
      const at::Tensor& b) {
    // Redispatch to CUDA implementation
    static auto op = torch::Dispatcher::singleton()
        .findSchemaOrThrow("myops::add", "")
        .typed<at::Tensor(const at::Tensor&, const at::Tensor&)>();
    return op.call(a, b);
  }

  static torch::autograd::tensor_list backward(
      torch::autograd::AutogradContext* ctx,
      torch::autograd::tensor_list grad_outputs) {
    // For addition: d(a+b)/da = 1, d(a+b)/db = 1
    auto grad_out = grad_outputs[0];
    return {grad_out, grad_out};
  }
};

// Schema registration
TORCH_LIBRARY(myops, m) {
  m.def("add(Tensor a, Tensor b) -> Tensor");
}

// CUDA backend implementation
TORCH_LIBRARY_IMPL(myops, CUDA, m) {
  m.impl("add", add_cuda_impl);
}

// Autograd implementation
TORCH_LIBRARY_IMPL(myops, Autograd, m) {
  m.impl("add", [](const at::Tensor& a, const at::Tensor& b) {
    return AddAutogradFunction::apply(a, b);
  });
}

// Autocast support (AMP)
TORCH_LIBRARY_IMPL(myops, Autocast, m) {
  m.impl("add", [](const at::Tensor& a, const at::Tensor& b) {
    c10::impl::ExcludeDispatchKeyGuard no_autocast(c10::DispatchKey::Autocast);

    auto exec_type = at::autocast::get_autocast_gpu_dtype();
    auto a_casted = at::autocast::cached_cast(exec_type, a);
    auto b_casted = at::autocast::cached_cast(exec_type, b);

    static auto op = torch::Dispatcher::singleton()
        .findSchemaOrThrow("myops::add", "")
        .typed<at::Tensor(const at::Tensor&, const at::Tensor&)>();
    return op.call(a_casted, b_casted);
  });
}

// Python binding (for direct access if needed)
PYBIND11_MODULE(TORCH_EXTENSION_NAME, m) {
  m.def("add", [](const at::Tensor& a, const at::Tensor& b) {
    return torch::ops::myops::add(a, b);
  }, "Add two tensors (native PyTorch integration)");
}
```

---

## 12) Python Usage with Full Integration

```python
import torch
import my_native_op

# Basic usage
a = torch.randn(1000, device='cuda', requires_grad=True)
b = torch.randn(1000, device='cuda', requires_grad=True)

# Forward pass
c = my_native_op.add(a, b)

# Backward pass (autograd works!)
loss = c.sum()
loss.backward()
print("Gradients:", a.grad, b.grad)

# AMP support
with torch.cuda.amp.autocast():
    c_amp = my_native_op.add(a, b)
    print("AMP dtype:", c_amp.dtype)  # Will be float16 or bfloat16

# torch.compile support
@torch.compile
def compiled_fn(x, y):
    return my_native_op.add(x, y)

result = compiled_fn(a, b)

# CUDA Graphs
g = torch.cuda.CUDAGraph()
with torch.cuda.graph(g):
    out_graph = my_native_op.add(a, b)
g.replay()
```

This shows how a properly registered custom op integrates seamlessly with PyTorch's ecosystem, providing the same user experience as built-in operations.

---

## Resources

- [PyTorch Custom Operators Tutorial](https://pytorch.org/tutorials/advanced/cpp_extension.html)
- [Dispatcher Documentation](https://pytorch.org/tutorials/advanced/dispatcher.html)
- [Autograd Extension Guide](https://pytorch.org/docs/stable/notes/extending.html)
- [AMP Documentation](https://pytorch.org/docs/stable/amp.html)
- [CUDA Graphs Guide](https://pytorch.org/docs/stable/notes/cuda.html#cuda-graphs)
