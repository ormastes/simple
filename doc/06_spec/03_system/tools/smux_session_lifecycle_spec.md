# smux session lifecycle SSpec

Source: `test/03_system/tools/smux_session_lifecycle_spec.spl`.
Status: TEST_BLOCKED — authored manual, not generated execution evidence.

| Scenario | Production operation and required oracle |
| --- | --- |
| Remote lifecycle targets | Actual dispatch lists IDs, probes existence, renames by ID, rejects the old name, removes only the empty target and preserves the other session's pane. This does not prove native child cleanup. |
| Rename stable identity | Actual API changes Unicode name, preserves ID/time/generation/window/attachment. |
| Refuse unsafe/ambiguous names | Empty, whitespace, C0/C1, other-name, other-ID and missing-session errors preserve original name; same-name rename succeeds. |
| Preserve surviving records | Actual pure removal keeps survivor geometry, output, focus, attachment, all metrics and next-ID while compacting all four registries. |
| Retain native ownership | Actual pure removal refuses target PID or fd=0, rejects unknown target, and preserves unrelated PID/PTY tokens. These records do not simulate native execution. |
| Rename complete records | Actual pure transform preserves timestamp/generation/geometry/output/attachment/metrics/allocator. |
| Targeted empty-session kill | Actual API removes only target resources/notices; survivor notices and startup metric remain; repeated kill errors and next session is id7. |
| Reuse bounded capacity | Eight sessions fill the registry; killing one permits id25 without rewinding allocation. |
| Real Windows detached-child kill | Spawn real `cmd.exe /Q` in ConPTY, attach/detach, kill with at most 200 retries separated by 25ms, require success, survivor session, and cleanup_pending=0. |

The live scenario checks closing-state mutation refusals and snapshot capture
only when native close actually defers. That conditional branch is not claimed
as guaranteed coverage. Use a bounded external per-case watchdog when admitted
Windows execution becomes available. The source's 5s retry sleeps do not bound
all native calls; piped close can block 100ms + 5s per owned child and has no
runtime failure-case proof here. No skips or placeholder passes are present.

Release gate: execute this actual spec with the admitted Phase 3 Windows
provider roots, preserve the runner receipt, and evaluate native cleanup and
remaining pending/failure branches. Source inspection alone does not satisfy
the gate.
