# Managed native MIR worker lifecycle

Status: coherent source candidate; exact review and runtime acceptance pending.
Frozen Phase3 campaigns and cached producer/runtime artifacts are unchanged.

## Existing owners and explicit request

The existing `run_ledger_shards` slot pool schedules selective workers. Parent
mutable state stays in that pool; one independent existing Linux group broker
owns each worker's pidfd, cgroup and descendant lifetime. The compiler child
receives encoded copies of exact argv/environment/input authority. No parent
pointer or native lease crosses the process boundary.

`GroupProcessRequestV1.mode` defaults to `group-root-v1`. Its old version-one
and version-two bytes and exact `--group-root ROOT` contract are preserved.
`native-worker-v1` uses version-three framing, bound into the same existing
request identity. It binds the exact executable content, argv, cwd, explicit
environment, immutable source-owner input hashes, broker image, finite lifetime
and enforced memory policy. The CLI registers the existing Linux broker launcher
explicitly. `SIMPLE_MIR_GROUP_BROKER_PROGRAM` and `_DIGEST` name its already
cached admitted executable. The compiler image must equal the running image by
content, and the existing compiled internal worker allowlist/marker is required.
No new runner, source broker, seed, raw-PID fallback or eligibility relaxation.

The sealed selective manifest's file digest includes its seal bytes and is an
actual pinned request input. Its separately verified manifest identity remains
the body seal used by job/context ownership. Each attempt gets a fresh private
native cache, temp directory and stdout/stderr logs. Private paths are explicit
request environment assignments, so the parent environment is not mutated for
those values. Request files remain in the atomically created private directory.

## Lifetime and terminal proof

`group_process_start_retained_v2` returns the retained owner after every attempted
launcher call, including uncertain startup. Pre-launch rejection is distinct.
Unknown observation keeps the slot charged. Cancellation acceptance requests a
transition; it does not prove termination. Only the durable broker terminal
receipt with `leader_reaped`, `tree_empty` and zero active processes, followed by
lease-bound `group_process_collect_reap_v1`, releases the slot for replacement.
An unresolved drain blocks new dispatch/linking and retains the durable owner
request/root for recovery; no new process is retried for that unknown slot.

Before any poll/collect can reap its child, the broker obtains the actual PID
from the retained Linux owner and the existing process birth primitive. It
publishes canonical bounded `simple/managed-child-identity/v1` with request,
worker/generation and executable-content identities. The compiler's self-report
cannot issue this receipt. The parent records these observations alongside the
managed request and collected tree-receipt digests. Numeric PIDs are observation
values only, never termination authority in the managed path.

The only new native operation exposes metadata already held by the existing
pidfd owner; its error result has no PID. Simple owns request policy, birth
validation, serialization, lifetime decisions and parent receipt validation.
Non-Linux boundary symbols return explicit ENOTSUP without owners or success,
and the CLI refuses this managed path there. No alternative platform runtime is
introduced. Existing nonselective/HIR and exporter paths are not qualified by
these new selective-worker receipts.

The broker retains a live lease if native drain becomes unknown. After actual
collection it retains the exact terminal result while persisting required
receipts, never collecting twice or re-encoding retained sample arrays on I/O
retries. Parent/cgroup release and terminal persistence are independent of the
manager lifetime. Quarantine is an owner-service state with bounded data and a
100 ms reconciliation interval; it starts no replacement children. It cannot
be reported as a completed build or a tree-empty proof by the manager.

## Budget and acceptance

Resource admission explicitly includes both worker/tool-tree and broker RSS
estimates (`SIMPLE_MIR_SELECTIVE_WORKER_KIB`, `_BROKER_KIB`). Each native child
scope enforces the worker limit before its first instruction. Parent/exporter,
combined worker+broker estimates, disk reserves and enclosing tree limits remain
required. These estimates are not measurements or qualification evidence.

Authored tests cover legacy framing, exact generic argv/environment, wrong
request/generation/executable child receipts, actual compiler-child/grandchild
cancellation, a forged numeric self-report pointing at another live owned child,
repeat terminal collection without signalling reused PIDs, native timeout and
SIGKILL status with surviving descendant cleanup. Actual OS PID reuse, real
job10 overlap, semantic/object equivalence, source/provider binding and complete
partial-result adoption still require qualified runtime evidence. The actual
managed CLI/tree tests are UNRUN, not skipped or source-approved execution.

Static evidence: Linux runtime C syntax and non-Linux-preprocessed C syntax pass;
the non-Linux object exports all nine fail-closed owner boundary symbols. The
existing unavailable-host C fixture reached the new negative PID checks, then
two attempts exposed its old errno whitelist missing independently observed
ENODATA from empty `cgroup.subtree_control`. The focused test correction matches
that prerequisite exactly; it remains UNRUN under the current resource and
missing-delegation restriction. No further kernel/native attempt was made.

The SFFI source warning audit failed its inventory dependency with
`source_variants=411/399 migration=3715/3546`. This is retained evidence, not a
provider PASS; repository-wide counts were not changed or automatically accepted.
The existing all-PASS link gate and independently owner-bound original inventory,
source/provider/context, object adoption and timing admission remain required.
