# Host cleanup retains diagnostics after consuming resources

Status: **AUTHORED_NOT_RUN**. The source spec is
`test/03_system/app/orchestrator/feature/windows_host_cleanup_disposition_v1_spec.spl`.
No compiler, runtime, native fault injection, SPipe or docgen was run.

| Requirement | Production transition exercised |
|---|---|
| REQ-WINDOWS-HOST-CLEANUP-DISPOSITION-001 | The same reducer used by Host cleanup classifies machine `consumed-error`, partner `retained`, then partner `released`; the first diagnostic survives and only retention remains pending. |
| REQ-WINDOWS-HOST-CLEANUP-DISPOSITION-001 | Released outcomes are consumed; ordinary retention remains transient; generic stale and unknown outcomes preserve pending ownership. |
| REQ-WINDOWS-HOST-CLEANUP-DISPOSITION-002 | Actual deployment and local cleanup finalize empty native-owner sets with `closed=true`, no cleanup owner and the original diagnostic. |

The first two scenarios supply modeled disposition data to the production
reducer. They do not fabricate native capabilities or prove an OS close fault.
The modeled paired first-error label is also retained through a pending turn
and final consumption; production obtains that label from the lower metadata
accessor without reopening consumed native capabilities.
The third invokes production finalization with genuinely empty owner sets and
a retained modeled diagnostic. Actual machine Option clearing before native
cleanup is source-reviewed; fault-injected machine consumption followed by a
retained actual native handle remains NOT_COVERED.

These are cleanup progress cases, not authority, admission, workload settlement
or capacity release. No manually constructed disposition can mint a machine
owner. First-error retention does not convert unknown resources into consumed
ones, and no platform fault or release qualification is claimed.
Raw stale state supplies no consumption proof. Idempotent completion must come
from the owning pair's canonical prior-closed metadata and its confirmed
released/consumed-error result; Host cannot infer it from a stale token.
