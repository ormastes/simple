# Native Backend Probe Enum Comparison
## Closed 2026-09-16 — ...Probe Enum Comparison ## Status Resolved by routing comparisons through `backend_probe_ini

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

## Status

Resolved by routing comparisons through `backend_probe_initialized`, in the
module that owns `BackendStatus`.

## Evidence

A cached-Stage3, 184-module Engine2D archive links without generated stubs
against an isolated Vulkan/CUDA runtime provider. On the NVIDIA Vulkan ICD the
native probe reports `status=Initialized`, `compute=true`, and `graphics=true`.

The cached compiler originally evaluated both `probe.is_ok()` and
`probe.status == BackendStatus.Initialized` as false.
`backend_status_text(probe.status)` prints `Initialized`, proving the field is
present but the cross-module comparison ABI is wrong.

The owner-module helper returns true in the same no-stub native executable.
Strict Vulkan creation now passes and selects `backend_name=vulkan`.

The next blocker is the separate aggregate-return defect recorded in
`native_engine2d_readback_aggregate_abi_2026-07-26.md`.

