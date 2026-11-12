# host_parent_budget_fixture_v1 costs ~46 s per example; host_service_domain_v2_spec exceeds a 240 s cap

- Date: 2026-11-13
- Severity: P3 (perf; spec passes)
- Status: open
- File: `test/fixtures/orchestration/host_parent_budget_fixture_v1.spl:18`

## Measurement
`test/01_unit/lib/nogc_sync_mut/orchestration/host_service_domain_v2_spec.spl` passes
11/11 in about 284 s on the Rust seed (interpreter lane, aarch64; 2-3 concurrent seed
runs, each under `MemoryMax=16G`).

| Examples | Time each |
|---|---|
| 1-4, 11 | 4 ms to 0.2 s |
| 5-10 (each calls `host_parent_budget_fixture_v1()`) | 45.8-49.4 s |

The fixture builds three larger fixtures (helper, execution, claim). Nobody has yet
measured which of the three is the expensive one.

## Fix direction
Profile the three sub-fixtures, then make the expensive one cheaper or build the parent
fixture once per file. Do not raise the spec's time budget without first making the
fixture cheaper.
