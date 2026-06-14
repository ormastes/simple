# Host/GPU Lane System Test Plan

## Scope

This plan covers executable SSpec coverage for the host/GPU lane event-flow and
grammar contract:

- canonical `target.later(...) gpu \:` and `target.later(...) host \:` grammar
- host-owned semantic mutation
- GPU render/effect batching
- rejection diagnostic for GPU semantic mutation through the Engine2D host/GPU
  lane contract and native Rust `simple check` source lint
- per-widget GPU dispatch diagnostic through the Engine2D host/GPU lane
  contract and native Rust `simple check` source lint
- deterministic event-flow evidence for host event count, Draw IR delta count,
  packet bytes, event-to-present timing, pixel hash, and p50/p95 speedup

Compiler lowering, runtime queues, and real GPU backend execution are out of
scope for this test-lane change. The native Rust driver source carries the
`HGL-SEMANTIC` and `HGL-BATCH` diagnostics; a deployed `bin/simple` may still be
stale until rebuilt. This spec keeps parser acceptance checks on `bin/simple
check` and semantic/event-flow checks on the implemented lane contract so the
SSpec remains stable across developer worktrees.

## Execution

Run:

```bash
bin/simple test test/03_system/feature/language/host_gpu_lane_spec.spl
```

Generated/manual mirror:
`doc/06_spec/test/03_system/feature/language/host_gpu_lane_spec.md`

## Pass/Fail Criteria

- Accepted grammar and host/GPU batch scenarios must exit `0` through
  `bin/simple check`.
- GPU semantic mutation must produce a failing lane-contract result with a
  diagnostic.
- Per-widget GPU dispatch must produce a failing lane-contract result with the
  design-contract diagnostic.
- Strict-GPU event-flow evidence must preserve event order, carry a stable
  pixel hash, and report lower candidate p50/p95 timing than the host baseline.
- The spec must use `use std.spec.*`, `step("...")`, built-in matchers only, and
  no placeholder passes.

## Traceability

| ID | Contract | Test File | Test Case | Coverage |
|----|----------|-----------|-----------|----------|
| HGL-001 | Canonical `target.later(...) gpu \:` and `host \:` grammar is accepted | `test/03_system/feature/language/host_gpu_lane_spec.spl` | should accept canonical gpu and host lane markers after later | Full |
| HGL-002 | Host lane owns semantic mutation | `test/03_system/feature/language/host_gpu_lane_spec.spl` | should accept host-owned semantic mutation in a host lane | Full |
| HGL-003 | GPU lane batches render/effect work with packet bounds | `test/03_system/feature/language/host_gpu_lane_spec.spl` | should accept GPU render and effect batching with packet bounds | Full |
| HGL-004 | GPU lane semantic mutation is rejected with a diagnostic | `test/03_system/feature/language/host_gpu_lane_spec.spl`; `src/compiler_rust/driver/src/cli/check.rs` | should reject GPU semantic mutation with a diagnostic; `test_check_rejects_host_semantic_mutation_in_gpu_lane` | Full for lane contract and native driver source; deployed binary refresh pending |
| HGL-005 | Per-widget GPU dispatch inside loops emits a warning | `test/03_system/feature/language/host_gpu_lane_spec.spl`; `src/compiler_rust/driver/src/cli/check.rs` | should warn for per-widget GPU dispatch inside a loop; `test_check_warns_for_loop_local_gpu_later_dispatch` | Full for lane contract and native driver source; deployed binary refresh pending |
| HGL-006 | Strict GPU event-flow evidence records timing, pixel hash, and speedup fields | `test/03_system/feature/language/host_gpu_lane_spec.spl`; `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_lane_spec.spl` | should record faster strict GPU event-flow evidence; records event flow timings and speedup for strict GPU batches | Full for deterministic contract evidence; measured full-GPU host run pending |
| HGL-007 | Draw IR execution feeds rendered command counts and pixel readback into host/GPU event-flow evidence | `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl` | feeds rendered Draw IR command counts into host GPU event-flow evidence | Full for CPU-fallback Draw IR executor evidence; real GPU device submission pending |
| HGL-008 | Runtime/lowering queue packets have deterministic sequence, payload bounds, checksum, fallback, and host-commit fields | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_lane_spec.spl` | builds deterministic queue packets for cross-lane lowering; rejects queue packets without a positive sequence | Full for deterministic packet descriptor; compiler lowering/runtime transport pending |
| HGL-009 | Runtime queue transport drains packets in sequence and records payload, fallback, host-commit, and checksum accounting | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_lane_spec.spl` | records ordered queue transport accounting; rejects queue transport drained out of sequence order | Full for deterministic transport accounting; hardware queue submission pending |

## Evidence Policy

This is compiler-check evidence, not visual UI evidence. The SSpec runner output
and generated markdown mirror are sufficient; no screenshots are required.
