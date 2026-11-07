# Simple Container API integration status

Status: **AWAITING_VERIFICATION**, not a completed orchestrator release.

Integration baseline: `8028e75917289a50b31bb695cbb5fe6f8c528667` on
`release/1.0.0`. Initial assembled source: `e335ef3a210d6a1accb16b4c502ee0cf1ef1c4a9`.
This report describes that source snapshot; later fixes require their own evidence.

Follow-up: `fc06f40` and Linux effect projection `4050939` are integrated.
At `23fc344c4b9`, the combined native sources passed the 82-check capture and
36-check seccomp compatibility fixtures. See
[integrated evidence](container_capture_integrated_20261107/evidence.sdn).
The initial relative-path fixture invocation failed its prerequisite; the
corrected absolute-path run and that failure are both retained. This closes the
capture compatibility blocker below for that native snapshot, not the separate
Windows candidate-recovery finding or any full application qualification gate.

## Required execution boundary

Linux selects `linux-podman`; Windows selects `windows-docker-process`.
`src/lib/nogc_async_mut/container/api_v2.spl` dispatches typed operations to
the actual platform adapters and returns the updated owner after every turn.
The signed host executor consumes this API, without engine argv construction.
Backend substitution and native-process fallback are not authorized.

| Integrated source | Upstream checkpoints | Evidence level |
| --- | --- | --- |
| Common API, execution scope and absence receipts | `ab492e6`, `d744bd4`, `3a46839` | Source and authored scenarios |
| Linux managed lifecycle | `1c5c4e9`, `e311d69` | Source; managed capture rejects truncation flags |
| Windows Docker process provider and adapter | `e180380`, `166139a`, `3a2fdc6` | Source; strong finite opener rejects weak boot evidence |
| Aggregate helper budget and signed dispatch contracts | `a30af7f`, `103b760` | Source and authored scenarios |
| Signed host execution through common API | `1678ac0` | Source and authored lifecycle scenarios |
| Native captured execution | `c89dc1f`, `c7ecde1` | Historical native fixture evidence; final compatibility correction pending |

## Evidence limits and outstanding work

- Native capture reports record the original 41-check and repaired 82-check
  source snapshots. Neither is evidence that this entire integrated tree, Simple
  compiler, providers, or host application ran successfully.
- The final capture correction must preserve ordinary legacy process execution
  when Linux `close_range` is unavailable. Strong new capture guarantees must
  fail explicitly where unsupported. This is a landing blocker for this snapshot.
- Linux managed non-launch capture now rejects incomplete output even on engine
  exit zero. Its Simple API regression scenarios remain **NOT_RUN**.
- Windows persistent-service startup still needs actual inventory reconciliation
  and a durable readiness receipt. A weak boot counter is not native boot authority.
- Host workspace/device admission currently refuses unsupported claims. Qualified
  workspace preparation, protected roots and guest access evidence must be wired
  before workspace-backed Caret or remote builds can be declared usable.
- Helper CPU admission accounting is not a kernel cap. The versioned native quota
  profile and separately charged service-broker overhead remain required.
- Controller CLI/service composition, terminal bind/stream ownership, legacy test
  consumer migration and verified container build/test publication are ongoing.
- Journal durability is explicitly process-crash only. Reboot or unproven
  continuity requires inventory/quarantine; no power-loss durability is claimed.
- Live Podman, Windows Docker, full Simple SSpec, core/MCP and end-to-end Caret
  qualification remain **NOT_RUN**. No unavailable fixture is counted as a pass.

Source integration and reviewed landing do not satisfy the original full feature
definition of done. Keep runtime qualification and remaining feature work visible.
