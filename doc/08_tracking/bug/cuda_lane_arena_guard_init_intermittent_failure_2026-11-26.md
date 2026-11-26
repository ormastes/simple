# CudaVmExecutor.init intermittently fails with `cuda-lane-arena-guard-init-failed`

- **Date:** 2026-11-26
- **Status:** OPEN
- **Area:** `src/lib/gc_async_mut/gpu_lane/cuda_vm_executor.spl` / `cuda_lane_session.spl`
- **Host:** Linux aarch64, NVIDIA GB10, libcuda `/usr/lib/aarch64-linux-gnu/libcuda.so.1`.
  Seed `/home/yoon/.cache/cargo-target-wr-seed1126b/release/simple` (sha256 prefix
  `fb80903917d6d5f5`).

## Symptom

The fixture runs CUDA probe, `init(svmg_cuda_kernel.ptx)` and `run_source(HELLO_PROGRAM, 1000, 0)`
under `SIMPLE_EXECUTION_MODE=interpret seed run`. Eight back-to-back runs on a shared host gave 7
clean results (`init=[]`, `ok=true exit=3 records=1 v=9`) and 1 failure:

```
cuda probe=
cuda init=[cuda-lane-arena-guard-init-failed]
cuda ok=false exit=0 records=0 v=-1
```

The CUDA lane fails closed (`ok=false`), so this is not a silent wrong answer. It is the same error
text the 2026-11-22 dlopen-routing fix removed as a deterministic failure
(`vulkan_vm_lane_returns_exit0_after_cuda_lane_same_process_2026-08-25.md`). Now it is
intermittent, which points at a resource or timing condition: a device shared with other sessions,
or the arena guard's allocation or `memcpy_htod`. Not root-caused here.

## Next step

Log the underlying CUDA driver result code in the arena-guard init path, so the failure names
itself, and loop the fixture for 50 or more runs to get a rate.
