# Metal MSL Processing Backend Test Plan

| Requirement / AC | Happy | Edge | Error / unavailable |
|---|---|---|---|
| REQ-001, AC-1/4 | Deterministic shared Metal artifact and exact validation | Semantic-key changes for value/count | Unsupported ProcessingIR emits no source |
| REQ-002, AC-4/11 | Bindings 0/1/2 and exact entry points | Padded stride, 2D bounds, row-major coordinates | Out-of-bounds drawing is rejected |
| REQ-003, AC-6 | Exact artifact reaches executor | Source and entry provenance remain canonical | Mutated source/entry fail before Metal access |
| REQ-004, AC-5/7 | Prepared macOS submits FillU32 and FillRect | Stable positive identity and raw-length checks | Linux emits BLOCKED records and deliberately fails native examples |
| REQ-005, AC-5/8/10 | Resume record names target and command | Retained compiler/readback/perf artifacts | Missing native host cannot become PASS |
| REQ-006, AC-11 | Metal-to-Metal exact pixel oracle | Surface stride exceeds visible width | Unsupported/lossy operations emit invalid artifacts |

The SPipe scenario exposes all seven frozen steps. The native examples are
release-blocking on Linux via `fail_test` after their complete blocked evidence
record is validated and printed. A green system spec therefore necessarily
means both FillU32 and FillRect ran on a prepared Metal host.

## NFR performance and invalidation evidence

`test/05_perf/processing/metal_msl_generation_perf_spec.spl` maps:

- NFR-001/002: 512 identical representative FillRect generations must be
  byte/key deterministic and average below 10,000 microseconds.
- NFR-004: `/proc/self/status` `VmHWM` is sampled immediately before and after
  512 FillU32 generations; incremental process peak RSS must remain strictly
  below 8,192 KiB. Missing procfs is a failure, not a skipped measurement.
- NFR-005: value and count semantic changes must produce distinct cache keys
  while deterministic target source remains stable.

Only a pure-selfhost run is admissible NFR evidence. Rust-seed output may find
syntax defects but cannot close these rows.

## REQ-013 / REQ-015 / NFR-007 emulator evidence

`test/01_unit/lib/gc_async_mut/processing/metal_emulator_spec.spl` exercises the
same deterministic MSL artifact, bindings 0/1/2, dispatch coverage, upload, and
download contract with `evidence_class=emulator` and `native_device=false`.
It covers exact FillRect pixels including stride padding, repeated dispatch,
and fail-closed binding/source/entry/upload/dispatch errors. Environment evidence
names its in-process runtime, canonical HAL owner, emulator identity,
compiler/validator contract, memory capability, and readiness reason.

This evidence cannot satisfy REQ-005 native Metal. The semantic system scenario
continues to call `run_processing_backend_device_probe`, which routes Metal to
`processing_ir_execute_metal_artifact` on macOS and fails blocked elsewhere.
