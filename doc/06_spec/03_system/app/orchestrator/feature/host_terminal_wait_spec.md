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
| Native refusal | Failed CLI or malformed wait output returns the updated consumed common owner, no receipt, unchanged journal sequence and retained capacity charge. Its immutable collection claim prevents another wait on retry. |
| Pending observation | An actual private `.write` collision causes publication failure after a qualified wait; the returned owner remains exited with held charge and `Some(receipt)` plus an error. Final publication is absent and retry cannot invent a new wait/time. |
| Corrupt retained fact | Corrupt existing bytes reject before another native query and are not restamped or replaced. |
| Re-encoded mismatch | Canonically encoded changed runtime/provider/plan/time values reject against protected retained facts without native queries or overwriting those bytes. |
| Interrupted claim | A retained collection intent without valid complete receipt/stage refuses recovery before another native query; no timestamp is fabricated. |
| Complete stage | Actual previously collected bytes model an interrupted complete-stage publication. Journal reopen with no remaining native commands promotes those original bytes/time without re-waiting. |
| Existing privacy | A final receipt deliberately made mode 0644 rejects through exact-descriptor metadata without chmod repair or another query. |

The original fact is archived in the existing host journal root. Neither the
collector nor these assertions authorizes cleanup or releases capacity. Correct
live OS/backend operation, actual container lifecycle, crash durability, latency,
RSS and runtime assertions remain unverified. No simulated platform evidence or
PASS is claimed.

These filesystem cases require the existing Linux retained-file owner. The
collector explicitly refuses unsupported Windows private persistence until
native owner/ACL capability is integrated; POSIX mode is not asserted to prove
Windows ACLs. A pending receipt with an error is never durable success. A crash
after wait but before complete stage persistence remains recovery-required.
