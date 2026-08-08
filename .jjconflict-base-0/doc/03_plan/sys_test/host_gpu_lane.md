# Host/GPU Lane System Test Plan

## Scope

This plan covers executable SSpec coverage for the host/GPU lane event-flow and
grammar contract:

- canonical `target.later(...) gpu \:` and `target.later(...) host \:` grammar
- host-owned semantic mutation
- GPU render/effect batching
- rejection diagnostic for GPU semantic mutation through the Engine2D host/GPU
  lane contract
- per-widget GPU dispatch diagnostic through the Engine2D host/GPU lane contract

Compiler lowering, runtime queues, and real GPU backend execution are out of
scope for this test-lane change. The production `bin/simple check` wrapper still
needs a rebuild/wiring pass before it can surface the new source-level check
lint; this spec keeps parser acceptance checks on `bin/simple check` and
semantic/event-flow checks on the implemented lane contract.

## Execution

Run:

```bash
bin/simple test test/03_system/feature/language/host_gpu_lane_spec.spl
sh scripts/check/check-native-sspec-expect-helper.shs
```

Generated/manual mirror:
`doc/06_spec/03_system/feature/language/host_gpu_lane_spec.md`

## Pass/Fail Criteria

- Accepted grammar and host/GPU batch scenarios must exit `0` through
  `bin/simple check`.
- GPU semantic mutation must produce a failing lane-contract result with a
  diagnostic.
- Per-widget GPU dispatch must produce a failing lane-contract result with the
  design-contract diagnostic.
- The spec must use `use std.spec.*`, `step("...")`, built-in matchers only, and
  no placeholder passes.
- The strict native expect-helper gate must observe one real failing assertion
  and an empty `SIMPLE_DUMP_STUBS` file; a compile/link failure is not a pass.

## Traceability

| ID | Contract | Test File | Test Case | Coverage |
|----|----------|-----------|-----------|----------|
| HGL-001 | Canonical `target.later(...) gpu \:` and `host \:` grammar is accepted | `test/03_system/feature/language/host_gpu_lane_spec.spl` | should accept canonical gpu and host lane markers after later | Full |
| HGL-002 | Host lane owns semantic mutation | `test/03_system/feature/language/host_gpu_lane_spec.spl` | should accept host-owned semantic mutation in a host lane | Full |
| HGL-003 | GPU lane batches render/effect work with packet bounds | `test/03_system/feature/language/host_gpu_lane_spec.spl` | should accept GPU render and effect batching with packet bounds | Full |
| HGL-004 | GPU lane semantic mutation is rejected with a diagnostic | `test/03_system/feature/language/host_gpu_lane_spec.spl` | should reject GPU semantic mutation with a diagnostic | Full for lane contract; compiler-check wrapper wiring pending |
| HGL-005 | Per-widget GPU dispatch inside loops emits a warning | `test/03_system/feature/language/host_gpu_lane_spec.spl` | should warn for per-widget GPU dispatch inside a loop | Full for lane contract; compiler-check wrapper wiring pending |

## Evidence Policy

This is compiler-check evidence, not visual UI evidence. The SSpec runner output
and generated markdown mirror are sufficient; no screenshots are required.
