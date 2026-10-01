# Grouped native manager performance and memory qualification

Status: measurement protocol only. The grouped compiler and supervisor have no
admitted runnable binary at this point. No speedup, peak, or tuned boundary is
claimed from the staged contract and preparer commits.

## Pinned comparison

Use one frozen source snapshot, inventory, variant receipt, target, backend,
admitted self-hosted binary digest, and toolchain per platform. Compare serial
one-member groups with the grouped setting using the same binary and compiler
flags. Windows and Linux are separate comparisons. Rust seed results cannot
serve as the self-hosted baseline. Record the exact config and output hashes.

Use a small representative inventory only if it has its own admitted complete
SCV/index/source authority. The run contract rejects an arbitrary subset of a
larger inventory. For an admitted fixture, run once with fresh state and five
times with new state/output roots against the same warm read-only index. Label
the first run `fresh-state` and the latter five `warm-index`; neither label
promises a cold or warm OS page cache. Report all six raw samples, warm median,
nearest-rank p95, modules per second, and failures. If no admitted small fixture
exists, coordinate host headroom before full-inventory runs; one serial and one
grouped pass give capacity evidence but do not support run-level percentiles.
A changed binary or config starts a new comparison, never a merged row.

## Required event and memory evidence

Time with a monotonic clock: manifest/route staging, source read, frontend,
MIR, codegen, object write, final link, group wall time, and manager wall time.
Associate each event with run/group/module/backend and the source/producer
digests. Missing stages are marked unavailable, never inferred from whole-run
time. Verify object and final binary hashes against the serial run before
accepting throughput; explain any expected nondeterministic bytes separately.
Each group compiler writes its existing monotonic `log_phase` records to its
manager-owned `groups/<group>/generation-<n>/attempt-<n>/compiler.phase.log`.
The attempt root and environment are pinned in the broker request. The profile
file is diagnostic evidence, while the typed module result and tree reap remain
the authority for completion.

Windows records parent working-set peak and sampled child-tree working set as
resident observations, JobObject peak committed bytes and enforced job limit
as commitment observations, plus physical availability and commit headroom
before staging and immediately before each spawn. Linux records parent/child
RSS and cgroup current/peak/limit when available. Under WSL, record host VMMEM
resident use and its possible further growth separately; host available
physical memory already excludes the current resident VMMEM allocation.
Process exit, cancellation, descendant reap, timeout and denied memory charges
must be visible in the same bounded attempt log.

Windows metric definitions follow Microsoft's
[JobObject limit](https://learn.microsoft.com/en-us/windows/win32/api/winnt/ns-winnt-jobobject_extended_limit_information),
[system memory](https://learn.microsoft.com/en-us/windows/win32/api/sysinfoapi/ns-sysinfoapi-memorystatusex),
and [WSL memory behavior](https://learn.microsoft.com/en-us/windows/wsl/compare-versions)
documentation. `ullAvailPageFile` is process-specific, so use the system-wide
commit limit minus committed total if that value is needed for admission.

## Admission decision

Derive active process count from CPU allowance and *current* host capacity.
The process-tree owner enforces each group's hard cap. Windows JobObject
current charge is committed bytes, not resident bytes, so use
`hard cap - current charge` only for the system commit-headroom check. For
physical/host memory, reserve each active group's full hard cap until a
tree-wide resident sample exists. Host available physical memory already
accounts for WSL's current resident allocation; do not subtract it separately.
A later measured incremental WSL-growth allowance belongs in the host reserve.
This hard-cap rule allows bounded overlap without treating a prior
group's lower peak as a guarantee for different modules. Record prior per-group
peaks for review and use them to tune group size only after parity and repeated
memory measurements. Resample after staging and just before spawn. Fail closed
when a required sample is unavailable or stale. Log candidate counts, each
limiting quantity, chosen counts, and refusal or clamp reason. Keep pending
groups bounded and commit results in manifest order after complete tree reap.
Effective inner threads remain one until comparable codegen-specific memory
evidence and native backend overlap/parity qualify.

The first implementation gate is a focused policy test using measured fixture
values, including a post-staging capacity drop, unavailable commit headroom,
WSL growth without double counting its current RSS, and active reservations.
The runtime gate checks the real output hashes and cancellation/reap evidence.
