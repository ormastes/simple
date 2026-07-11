<!-- codex-research -->
# Domain research: CUDA host validation

Date: 2026-07-11

## NVIDIA guidance

- `cuInit(0)` must precede Driver API work; enumerate devices through the API
  rather than treating a missing CLI as authoritative.
  [Initialization](https://docs.nvidia.com/cuda/cuda-driver-api/group__CUDA__INITIALIZE.html)
- `cuModuleLoadData` accepts NUL-terminated PTX and returns distinct invalid
  PTX, unsupported PTX, no-binary, OOM, and JIT errors. `cuModuleLoadDataEx`
  also provides JIT diagnostic logs that CI should retain.
  [Module management](https://docs.nvidia.com/cuda/cuda-driver-api/group__CUDA__MODULE.html)
- `cuLaunchKernel` takes an array of pointers to kernel-parameter storage plus
  explicit grid, block, and dynamic shared-memory sizes. Validation must cover
  multiple pointer/scalar arguments, not only no-argument launches.
  [Execution control](https://docs.nvidia.com/cuda/cuda-driver-api/group__CUDA__EXEC.html)
- CUDA work can be asynchronous. A successful launch is not proof of kernel
  completion: synchronization and checked DtoH transfer are required.
  [Memory API](https://docs.nvidia.com/cuda/cuda-driver-api/group__CUDA__MEM.html),
  [Asynchronous execution](https://docs.nvidia.com/cuda/cuda-programming-guide/02-basics/asynchronous-execution.html)
- NVIDIA recommends checking immediately after launch, while asynchronous
  failures can surface later; evidence must identify launch versus sync versus
  readback failure.
  [CUDA error checking](https://docs.nvidia.com/cuda/cuda-programming-guide/02-basics/intro-to-cuda-cpp.html)
- PTX has distinct global, parameter, local, constant, and shared spaces. A
  shared-memory claim needs live `.shared` access and cross-thread sync, not a
  source-string check. [PTX ISA](https://docs.nvidia.com/cuda/parallel-thread-execution/contents.html)
- Container jobs explicitly select GPUs via `NVIDIA_VISIBLE_DEVICES`; `compute`
  enables CUDA and `utility` exposes tools such as `nvidia-smi`. Job policy,
  not variable presence, determines SKIP versus FAIL.
  [Container GPU enumeration](https://docs.nvidia.com/datacenter/cloud-native/container-toolkit/latest/docker-specialized.html)

## Derived validation model

Use two gates:

1. **Portable, always required:** compile Simple to PTX, verify directives and
   entries, exercise control flow/calls/memory, and assert unsupported MIR
   returns typed errors. No device is required.
2. **CUDA host, required on a labelled GPU job:** initialize and enumerate,
   load the exact generated PTX, execute and synchronize, copy back, and compare
   exact buffers and sentinels.

An optional non-CUDA host reports live `SKIP` without weakening portable tests.
A labelled GPU job must fail when it cannot initialize or enumerate a device,
otherwise CI provisioning regressions would be hidden.
