# CudaVmExecutor.init intermittently fails with `cuda-lane-arena-guard-init-failed`

- **Date:** 2026-11-26
- **Status:** fix-implemented-verification-pending
- **Waiting For:** aarch64 GB10 CUDA verification
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

---

## 2026-11-27 Fix Applied (Wave 5 Lane W5-4, `work/w5-4-scripts-caret-font-20261127`)

- `src/lib/gc_async_mut/crypto_accel/cuda_session.spl`:
  - Validated `cuda_device_get()` non-negative handle, explicitly called `cuda_ctx_set_current(self.context)` inside `init()` (destroying context on activation failure) and before `alloc`/`upload`/`readback`/`clear`/`launch`/`sync`/`load_module*`.
  - Recorded exact negative `CUresult` codes + `cuda_get_error_string(rc)` in `last_error` across lifecycle failures instead of collapsing errors to `1`.
- `src/lib/gc_async_mut/gpu_lane/cuda_lane_session.spl`:
  - Rejected negative device ordinals in `probe()`.
  - Added `format_cuda_lane_error()` so `cuda-lane-arena-guard-init-failed:rc=<code>:<msg>` (and context/alloc/load/upload/readback/launch errors) report the underlying CUDA driver result code and string while retaining first-error guarantees.
  - Replaced `rt_cuda_memcpy_htod_array` raw `[u8]` bypass in `init()` and `arena_write()` with explicit context pinning (`_upload_with_reactivate()`), host-scratch marshaling, `self.session.clear()` zeroing, and `_cleanup_init_failure()` resource hygiene.
- `src/lib/gc_async_mut/gpu_lane/cuda_vm_executor.spl`:
  - Cleaned up `self.session.shutdown()` if `load_entry` fails in `init()`.
  - Guarded `value_ptr == 0` / `args_ptr == 0` before `rt_ptr_write_i64` in `run_source_persisting_data()`.
  - Cleared `self.entry_loaded = false` on clean `shutdown()`.
- Host verification (Windows without CUDA driver):
  - `test/01_unit/lib/gc_async_mut/gpu_lane/cuda_lane_arena_guard_error_spec.spl`: PASS (`5 passed, 0 failed`).
  - `test/02_integration/gpu_lane/cuda_lane_session_spec.spl`: PASS (`4 passed, 0 failed, 1 skipped` CUDA absent).
  - `test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl`: PASS (`2 passed, 0 failed, 2 skipped` CUDA absent).
- Remaining verification (`waiting-for: aarch64 GB10 CUDA verification`): 50+ back-to-back live runs on aarch64 GB10 (`libcuda.so.1`).
