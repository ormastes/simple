# Original host terminal-wait retention V2

Status: **NOT_RUN** — source-authored manual. No compiler campaign, system suite,
engine command, native container or live-platform test executed while authoring.
Source: `test/03_system/app/orchestrator/feature/host_terminal_wait_spec.spl`.
Fixture: `test/fixtures/orchestration/host_terminal_wait_fixture_v2.spl`.

The fixture reuses the actual signed host executor, common Container API and
capacity/operation journal with explicitly scripted Linux native command results.
Its host root metadata is synthetic and does not claim enrollment/native host
qualification. Native commands are matched through existing provider builders
and engine policy; the collector itself uses only the shared read API.

| Scenario | Intended assertion |
| --- | --- |
| Actual shared read | Resolver consumes its recover/inspect results and common wait consumes exactly one wait result. Full command/raw output, CLI zero and workload 17 are retained with actual host time. Journal sequence and held capacity remain unchanged. |
| Original repeat/reopen | Repeated collection preserves exact canonical bytes and time. The actual host journal closes/reopens; replay succeeds with no native queries even when the fixture owner is marked destroyed and has no scripted commands. This marker is fixture data, not real cleanup/absence. |
| Native refusal | Failed CLI or malformed wait output returns the updated consumed common owner, no receipt, unchanged journal sequence and retained capacity charge. |
| Store refusal | An actual filesystem obstruction causes publication failure after wait; the returned owner remains exited with held charge and no delivered receipt. |
| Corrupt retained fact | Corrupt existing bytes reject before another native query and are not restamped or replaced. |
| Re-encoded mismatch | Canonically encoded changed runtime/provider/plan/time values reject against protected retained facts without native queries or overwriting those bytes. |

The original fact is archived in the existing host journal root. Neither the
collector nor these assertions authorizes cleanup or releases capacity. Correct
live OS/backend operation, actual container lifecycle, crash durability, latency,
RSS and runtime assertions remain unverified. No simulated platform evidence or
PASS is claimed.
