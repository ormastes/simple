# HIP/ROCm fail-closed hardening (2026-11-23)

Scope: the "Optional Backend Hardening" HIP slice of
`doc/03_plan/release/1.0.0/robustness_completion_plan_2026-11-17.md`
(owner decision 2026-11-18: HIP in scope).

## Existing behaviour (kept)

- Compiler: `HipBackend.compile_module` (`src/plugins/backend_hip/hip_backend.spl`)
  already returns a `compileerror_backend_error(BackendKind.Hip, ...)`; no fallback.
- Runtime: `hip_compute.rocm_open_at` loads HIP/hipRTC only after a file check
  and returns `Err(text)` on every failure; nothing panics.
- Dispatch: `backend_dispatch._dispatch_reduce_hip` reports
  `gpu-backend-unavailable:hip` for a required HIP target, the same shape CUDA
  uses (`gpu-backend-unavailable:cuda`). A *suggested* target resolves to CPU
  through `resolve_exec_target` and says so in `ComputeStats.ran_on_cpu`; that is
  explicit, not silent.

## Gap closed here

Every unavailable-path `Err` was free text (`ROCm: dlopen failed ...`), so a
caller could not tell "no ROCm install" from "install present but no GPU"
without string guessing. Each runtime unavailable error now starts with a
stable, named code:

| code | when |
|------|------|
| `ROCm[hip-library-missing]` | HIP or hipRTC library file absent in the ROCm dir |
| `ROCm[hip-dlopen-failed]` | file present but libc/HIP/hipRTC fails to load |
| `ROCm[hip-symbol-missing]` | a required HIP/hipRTC/libc symbol is absent |
| `ROCm[hip-init-failed]` | `hipInit` returns non-zero (no driver / no GPU) |
| `ROCm[hip-device-query-failed]` | `hipDeviceGetName` returns non-zero |

The dispatch-level string stays `gpu-backend-unavailable:hip` (CUDA parity).

## Verification

`test/03_system/lib/gpu/hip_fail_closed_spec.spl` exercises the missing-dir and
garbage-library (dlopen) paths on every host. A real-GPU run is not claimed:
the dev host used for this slice has no ROCm install.
