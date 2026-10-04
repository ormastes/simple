# Linker resource evidence and owned worker

Status: prerequisite repair design plus full worker implementation contract.
Simple execution, qualification and whole-job enforcement are UNRUN/open. This
does not turn measurement integrity into completion of item 4's bounded worker.

## Session and selection constraint

Owner/session: `/root/linker_research`, `item4-resource-evidence-docs-20261004`.
Worktree: `C:/dev/simple-item4-stream-got-docs-20261004` (reused clean).
Branch: `work/item4-resource-evidence-docs-20261004`; target `origin/release/1.0`;
base/expected target `d11536cc67be20934752b566f63e2bb10ccfe7ee`.
Only this document is owned here. Root owns classification/integration, runtime
owns provider repair, acceptance owns tests; sidecars N/A. No push or runtime run.

The user's selection constraint is explicit: Simple's mold-like linker should
be available, but must not become the default. `linker/mold.spl` retains external
mold -> lld -> ld discovery; existing `SIMPLE_LINKER=internal` is explicit internal
selection. A future bounded-worker route must preserve that distinction and
existing configuration/target routing. It must not silently select the internal
engine because a resource budget was requested. Target-specific SimpleOS routing
is outside this change. Root documents the supported explicit invocation path.

## Existing production seams and missing proof

`linker/link_engine_external.spl` resolves policy and returns UnsupportedBudget
before reading inputs when Bounded is selected. That is currently correct.
`elf/stream_link.spl` provides retained inputs, logical scan/window/metadata/output
limits, spilled output and transactional publication, but no process-tree memory
enforcement. Its current publication runs within the caller's process.

`linker/link_accounting.spl` previously promoted any ExactTree observation plus
a positive caller-supplied limit to QualifiedJobScope. Neither value proves
installed enforcement, no swap, complete process ownership, or valid admission.
The selected repair never promotes measurement-only input. Test intent
`d2440ba96ce` precedes that repair. `linker/linker_pack.spl` also correctly rejects
a provider's QualifiedJobScope claim without parent-owned resource evidence.

`src/lib/nogc_sync_mut/io/resource_scope.spl` has real Linux cgroup and systemd
providers, but direct scope setup writes only memory.max/pids.max, does not prove
swap prohibition, and scope removal is best-effort. Missing memory.peak formerly
became zero while the observation remained available. The systemd path formerly
used permissive numeric conversion and weak property-presence checks. Repair
these production parsers before consuming observations in any worker receipt.

The same module can fall back to per-process Unix limits or a monitored child.
These paths must not be accepted by a future strict whole-job provider. Moving
the current parent into a cgroup after its allocations does not establish a
before-allocation worker boundary.

`windows_process_owner.spl` already installs and reads back a Job memory limit,
creates a suspended child, assigns it to the Job before resuming, restricts
inherited handles, and exposes cancellation/collection proofs. These are useful
ownership capabilities. Job committed-memory limits and peak committed memory
are not a no-swap guarantee or an RSS measurement. Do not rename their metric.

Upstream refinement inspected at release
`bcd4dd3be474a5ff17a22a328e4a35193971515e` (PR 2443): `resource_scope.spl` now
also exposes `run_in_owned_execution_resource_scope` and the test alias
`run_in_owned_test_resource_scope`. Its Windows `_run_windows_owned_scope` uses
the redirected Job owner, memory/deadline controls, bounded cleanup observation,
quarantine when collection remains unproven, and an additive completion receipt.
This is a real owned-process facade; it must be preserved when integrating the
Linux metric-parser repair. It continues to report CPU/RSS resource evidence as
Unavailable and does not establish no-swap or qualified linker admission. The
legacy generic observation route also remains present, so describe the selected
API accurately rather than treating all Windows execution as legacy-only.

## Primary evidence and parser requirements

The [Linux cgroup v2 documentation](https://www.kernel.org/doc/html/v5.19/admin-guide/cgroup-v2.html)
defines memory.peak as the maximum cgroup/descendant charge since creation.
[Current documentation](https://docs.kernel.org/6.14/admin-guide/cgroup-v2.html)
adds file-descriptor-specific reset behavior; a fresh per-job scope avoids
unrelated historical peaks. memory.swap.max is distinct from memory.max: a RAM
charge ceiling does not itself disable anonymous swap. Kernel capabilities and
delegation must be checked, not assumed from an OS label or version string.

[systemd's accounting implementation](https://github.com/systemd/systemd/blob/main/src/core/cgroup.c)
uses UINT64_MAX for unavailable cached memory accounting and returns ENODATA
without valid data. A [maintained distro backport](https://git.almalinux.org/rpms/systemd/src/commit/1e476f0c7036c7f74bee73ef7e9ff6048d1412b4/1195-cgroup-add-support-for-memory.peak.patch)
shows the property getter initialized to UINT64_MAX when peak acquisition fails.
Absence, `[not set]`, `infinity`, unsigned maximum, negatives, junk and signed
range overflow must not become a zero-byte measurement. Valid zero remains a
possible empty-scope observation, never a qualification certificate.

The [Microsoft Job limit definition](https://learn.microsoft.com/en-us/windows/win32/api/winnt/ns-winnt-jobobject_extended_limit_information)
specifies committed virtual memory for JobMemoryLimit/PeakJobMemoryUsed. This
supports retaining a distinct charge metric and rejecting unsupported no-swap
requirements. Sources inspected 2026-10-04.

The provider repair must parse required cgroup quantities strictly, require a
valid peak file, and retain observation quality as unavailable on malformed or
missing evidence. The systemd production parser must require valid properties
and successful query transport; arbitrary nonempty Result text is not proof of
a terminal unit. Unit status, process result and accounting quality remain
separate concepts. A valid measurement accompanying a failed job may still be
useful; it never implies successful execution or admitted enforcement.

## Full positive worker path

1. An explicit selected-engine request enters a parent-owned job owner. Validate
   bounded protocol sizes and target/options; obtain an independently admitted
   worker artifact identity. Do not synthesize trust from an arbitrary pathname
   hash. Reserve parent control-plane memory and bounded transport separately.
2. Before the worker reads input or starts its runtime allocation, create a fresh
   owned Linux scope, install and read back memory.max, memory.swap.max=0 and
   process limits, and establish descendant containment. A minimal launcher must
   attach before exec or use an equivalent atomic spawn facility. Failure means
   no worker execution, not fallback. Clarify which launcher allocations and
   parent allocations are outside the worker charge and reserve them explicitly.
3. Pass immutable bounded request/configuration and retained input authority.
   Worker artifact, input identity, policy digest, target and unique job identity
   must bind the response. Reopening untrusted paths does not preserve retained
   input identity; specify inherited capabilities or a verified immutable staging
   protocol. All existing native options must survive the transport.
4. Worker executes the real stream engine into a task-owned private destination,
   never the user's final output. Refactor or redirect stream publication so the
   worker's success cannot publish before the parent finishes evidence collection.
   Existing scan/window checks and scratch reservations still apply inside the
   worker; they complement the OS limit, not replace it.
5. Parent waits for the whole process scope, not only its leader. Cancellation,
   timeout or resource breach terminates/reaps descendants. Read final strict
   peak/events and enforced-limit identity while scope authority still exists.
   Scope escape, unavailable peak, failed cleanup/collection, identity mismatch
   or invalid child result prevents qualification and publication.
6. Parent independently validates staged output identity/length/digest and child
   protocol, then issues the parent-owned receipt and atomically commits output.
   Only a dedicated admission owner with actual enforcement/lifecycle evidence
   may eventually issue QualifiedJobScope. Child text or caller booleans cannot.
   Post-commit cleanup failure returns published+cleanup_pending, not an error
   pretending the destination was never changed.

Linux cgroup delegation, suitable kernel interfaces and an admitted executable
are genuine prerequisites. Missing ones return UnsupportedBudget before input
work. Windows can supply an explicitly narrower committed-memory job mechanism,
but must reject the full no-swap/RSS contract until an honest owner exists.
No broad process API fallback may silently relax the selected requirement.

## Concrete ownership and implementation order

First repair `resource_scope.spl` parsing and `link_accounting.spl` classification
with real file/property parser tests. This is an evidence-integrity prerequisite.
Next add a strict platform job owner (no permissive fallback) and a compiler
linker worker dispatcher/entry, reusing existing process/file owners rather than
introducing app-leaf raw process or environment calls. Coordinate any platform
owner changes with their active sessions. Then split private stream staging from
parent publication, wire explicit bounded requests in `link_engine_external.spl`,
and extend receipt validation with actual parent-owned admission evidence.

Scratch enforcement needs both logical pre-write reservation for every owned
file and a stated containment boundary. memory.max does not cap disk bytes;
RLIMIT_FSIZE alone does not cap aggregate scratch. A trusted single worker using
checked file owners can enforce its declared scratch protocol, while arbitrary
descendants need a separate filesystem/quota mechanism. Do not claim the latter
from the former. Input copies, spill copies and staged publication must all be
included in simultaneous scratch accounting.

## Executable acceptance obligations

Tests first, then implementation; runtime execution remains unadmitted.

- Real metric files and the production systemd parser accept valid decimal zero
  and positive peaks; reject missing, malformed, negative, sentinel and overflow
  values. Failed query transport cannot produce ExactTree. ExactTree plus a
  caller limit remains measurement-only, including values below/equal/above it.
- A real worker writes an input-open marker only after installed/read-back
  limits. Admission failure leaves that marker absent and output unchanged.
- Worker and child/grandchild allocations share the actual enforced scope.
  Exceeding its limit terminates/fails the job and cannot publish; positive
  within-limit linking produces independently checked ELF bytes.
- Verify no-swap controls before launch and final scope identity/events. Reject
  unavailable capability rather than simulate a successful qualification.
- Delayed descendant after leader exit prevents premature completion. Cancel,
  crash, timeout and OOM all reap the owned tree and preserve the destination.
- Corrupt/truncated/wrong-job/wrong-policy child receipts, changed inputs or
  staged outputs cannot authorize publication. Real scratch boundary failures
  and copy overlap remain within the declared accounting and preserve sentinel.
- Post-publication cleanup faults report committed output plus retained cleanup
  capability. No cleanup failure is hidden or relabeled as pre-publication Err.
- Default external linker discovery remains unchanged. Explicit internal bounded
  selection traverses the real worker; unsupported targets/options fail clearly.

Required execution on an admitted runtime, canonical manuals, coverage, compiler
and MCP smoke, representative latency/RSS/descendant tests and full item 4 gates
remain open. A source-only parser repair cannot close any of these worker gates.
