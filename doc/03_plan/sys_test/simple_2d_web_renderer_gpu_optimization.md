# System test plan — Simple 2D/web GPU optimization

Map REQ-GPUUI-001..008 and NFR-GPUUI-001..007 to one executable scenario suite.

1. Build/dynload the Chrome ABI and reject missing/hash/version/symbol errors.
2. Render the shared showcase through device-present and prove zero readback.
3. Capture the named completed token once and prove exact CPU-oracle pixels.
4. Resize, inject device loss, and shut down; prove generation invalidation and
   retained-memory release.
5. Submit three frames, poll/retire out of CPU submission scope, and prove real
   backend fence identities plus bounded frames in flight.
6. Replay pointer/keyboard/scroll/resize events; prove order, target, generation,
   coalescing policy, and damage-only upload.
7. Exercise every hot primitive and fail if a claimed device route falls back.
8. Compare C/Simple Vulkan and Chrome/Simple records only when admission
   metadata matches; assert p95, RSS, and strict interactive thresholds.
   The artifact-only companion contract at
   `test/03_system/check/perf_comparison_admission_contract_spec.spl` covers
   11 schema/identity/viewport/checksum cases and must remain separate from
   physical renderer evidence.

Capture typed receipts under `build/test-artifacts/` and generate the mirrored
manual at
`doc/06_spec/03_system/app/ui.browser/feature/simple_2d_web_renderer_gpu_optimization_spec.md`.

## Current executable slice

The first executable system slice covers the portable lifecycle boundary at
`test/03_system/app/ui.browser/feature/simple_2d_web_renderer_gpu_optimization_spec.spl`.
It runs without an external GPU so it can reject false device claims
deterministically. It does not substitute for the live backend and comparison
lanes below.

Execution order:

1. Run retained lifecycle and event-damage unit specs.
2. Run the portable system contract in compiled mode.
3. Run physical/headless native backend evidence after production adapters use
   the contract.
4. Run admitted C Vulkan and Chrome differential benchmarks last.

Pass criteria are exact state transitions, named device tokens and fences,
zero readback during presentation, bounded allocations, damage-only byte
accounting, and fail-closed stale input. Live lanes additionally require
trusted binary provenance and matched benchmark metadata.

Manual policy: the four requirement groups and all twelve scenarios are
visible; helper source and executable SSpec are folded. Evidence is link-only
for future device traces, benchmark records, and raster captures.

## Traceability

| Requirement | Executable evidence | Cases | Status |
|---|---|---:|---|
| REQ-GPUUI-001 | Existing backend conformance suites; production integration pending | 0 new | PARTIAL |
| REQ-GPUUI-002 | `simple_2d_web_renderer_gpu_optimization_spec.spl` | 3 | PORTABLE PASS; live pending |
| REQ-GPUUI-003 | `simple_2d_web_renderer_gpu_optimization_spec.spl` | 3 | PORTABLE PASS |
| REQ-GPUUI-004 | `simple_2d_web_renderer_gpu_optimization_spec.spl` | 3 | PORTABLE PASS; real fence pending |
| REQ-GPUUI-005 | `simple_2d_web_renderer_gpu_optimization_spec.spl` | 3 | PORTABLE PASS; presenter integration pending |
| REQ-GPUUI-006 | Native primitive/backend suites | 0 new | MISSING |
| REQ-GPUUI-007 | `test/03_system/check/perf_comparison_admission_contract_spec.spl` plus live differential suites | 11 admission cases | ADMISSION POLICY ONLY; measurements missing |
| REQ-GPUUI-008 | Existing DrawIR/browser parity suites | 0 new | PARTIAL |
| NFR-GPUUI-002,003 | `test/03_system/check/perf_comparison_admission_contract_spec.spl` and live comparison receipts | 11 admission cases | ADMISSION POLICY ONLY; measurements missing |
| NFR-GPUUI-004 | `simple_2d_web_renderer_gpu_optimization_spec.spl`, capture contracts, and live renderer receipts | 1 portable zero-readback scenario | PORTABLE CONTRACT; device capture receipt missing |
| NFR-GPUUI-007 | `test/03_system/check/perf_comparison_admission_contract_spec.spl` and live renderer receipts | Shared admission schema | PARTIAL; p50/p95, RSS, upload/readback, fence, damage, and device checksum receipts missing |
| NFR-GPUUI-001,005,006 | Live performance and resource receipts | 0 admitted | MISSING |

Risk areas are backend token honesty, device-loss invalidation, hidden
presentation readback, per-frame allocation, font/image fallback, event bursts,
and mismatched timing boundaries. Any missing live receipt remains a release
failure rather than a skipped pass.
