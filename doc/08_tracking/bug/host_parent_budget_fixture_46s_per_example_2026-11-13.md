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

The fixture builds three sub-fixtures. Measured in one probe example on the same seed
(`time_now_monotonic_ms` around each call):

| Sub-fixture | Time |
|---|---|
| `host_helper_fixture_v1()` | 37.7 s |
| `host_execution_fixture_v2("success")` | 3.6 s |
| `host_claim_fixture_v1()` | 4.4 s |

`host_helper_fixture_v1` (`test/fixtures/orchestration/host_helper_fixture_v1.spl:61`) opens
and prepares a capacity owner and builds several signed grants and approvals
(`helper_fixture_signed_v1`, `helper_fixture_approval_v1`, `verification_fixture()`). The
likely cost is signing and verification running in pure Simple on the interpreter, but this
part has not been profiled.

## Fix direction
Profile inside `host_helper_fixture_v1`. If signing dominates, compute the deterministic
signed records once per process and reuse them; temp roots and capacity owners stay per
example, so isolation does not change. Do not raise the spec's time budget without first
making the fixture cheaper.
