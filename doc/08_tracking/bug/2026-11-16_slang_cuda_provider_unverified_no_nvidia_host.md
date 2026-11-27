# slang CUDA provider is unverified on NVIDIA hardware

Status: open (awaiting NVIDIA host run)
Owner: slang runner lane

`gpu/cuda/cuda_compute.spl` and `pure/tensor_ops_cuda.spl` were written on an
AMD-only Windows host and reviewed against the CUDA driver API / NVRTC ABI
(no live run). Library resolution (incl. the driver-major NVRTC filter),
argument packing and launch-config layout are covered by
`test/01_unit/lib/gc_async_mut/gpu/cuda_compute_spec.spl`. Everything that
touches a device is untested: `test/03_system/lib/slang/feature/slang_pure_cuda_ops_spec.spl`
names this record. It is not tagged `@tag:in-development` (that tag is not for
missing hardware); without an NVIDIA driver each case returns early and appends
a `SKIPPED:` line to `build/probe/pure_evidence.txt`.

Exit criteria: on an NVIDIA host run that spec by explicit path
(`bin/simple test test/03_system/lib/slang/feature/slang_pure_cuda_ops_spec.spl`),
all cases green and `build/probe/pure_evidence.txt` showing a `CUDA DEVICE:`
line (not a `SKIPPED:` line) for that run; then delete this record and the
spec's `Tracks:` line.

Review focus (unverifiable here):
- Code image: CUBIN for the device's `sm_XY` (minor-version compatible), falling
  back to default-arch PTX only on `NVRTC_ERROR_INVALID_OPTION`; PTX JIT needs a
  driver at least as new as the NVRTC (rc=222 otherwise).
- NVRTC candidates newer than the driver major (`cuDriverGetVersion`) are not
  loaded; NVRTC builtins DLL/so must be findable next to the loaded NVRTC.
- cuLaunchKernelEx CUlaunchConfig layout (56 bytes), primary-context thread
  affinity (every call from the opening thread). `cuda_close` exists (modules,
  primary context, scratch, libraries; idempotent) but `compute_backend` has no
  close arm, so a Cuda `ComputeOps` lives for the process.

Static-review fixes (2026-11-23, still not run on hardware): ops validate
rank/size/position arguments before any device call; `cuda_launch` no-ops an
empty grid (zero grid dimension is CUDA_ERROR_INVALID_VALUE) and rejects block
< 1; `cuda_close` is idempotent. Covered hardware-free by an all-zero
`CudaDevice` in `cuda_compute_spec.spl`. Static-only and still open: kernel
numerics, NVRTC/CUBIN loading, cuLaunchKernelEx on a real driver, the empty-
tensor and close/reopen cases in the system spec.
