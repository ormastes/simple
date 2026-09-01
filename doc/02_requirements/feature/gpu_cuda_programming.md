# Requirements: GPU/CUDA programming surface

What a developer writing GPU code in Simple must be able to do. Acceptance:
`test/03_system/acceptance/gpu_cuda_programming_acceptance_spec.spl`.
Guide: `doc/07_guide/lib/gpu_3d/cuda_gpu_programming.md`.

- `REQ-GPU-CUDA-001`: A developer can discover whether the machine has a usable CUDA driver, how
  many devices it has, and each device's name and compute capability, without installing a toolkit.
- `REQ-GPU-CUDA-002`: A developer can allocate device memory and round-trip a typed host array
  (`f32`, `f64`, `i32`, `i64`) of realistic size without corruption, including negative values.
- `REQ-GPU-CUDA-003`: A developer can compile a PTX module, look up a kernel by name, launch it
  with a chosen grid/block and real parameters, and read the results back.
- `REQ-GPU-CUDA-004`: A developer can launch work on a named stream and measure elapsed device
  time with events, rather than being limited to the default stream.
- `REQ-GPU-CUDA-005`: A developer can write and verify kernel index arithmetic in 1-D, 2-D and 3-D
  with **no GPU present**, using the same kernel body that would be lowered for the device.
- `REQ-GPU-CUDA-006`: `kernel<<<grid, block>>>(args)` executes the kernel; it must never silently
  evaluate to nil. Where it cannot run, it must raise a diagnostic naming what is missing.
- `REQ-GPU-CUDA-007`: A backend that is unavailable on the host reports an explicit, machine-
  readable `skip:<reason>`; a fake pass is a defect.
- `REQ-GPU-CUDA-008`: Every `extern` the GPU surface declares is backed by a symbol the runtime
  actually defines — an unbacked extern silently returns nil and is therefore a silent wrong answer.
