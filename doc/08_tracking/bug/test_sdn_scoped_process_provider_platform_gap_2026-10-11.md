# SDN test wrapper scoped-process provider platform gap

Status: open; release verification blocker on all current providers.

The public SDN test wrapper requires the V4 owned process provider to pass a
per-child environment without mutating the parent environment, collect bounded
diagnostics, and establish child retirement before reading its result file.
`src/runtime/runtime_process_owned.c` implements the provider capability response
under `__linux__`; other hosts report `ENOTSUP`. The current Windows development
host therefore cannot qualify this wrapper through that provider. Source review
also found that the current Linux V4 provider advertises leader-only control,
rejects a process-group descendant policy, and does not establish tree-empty
retirement. The wrapper's required group-retirement contract therefore remains
unsupported on Linux as well.

The wrapper must emit a canonical failure document and a nonzero exit on an
unsupported provider. Ambient environment mutation, an unowned process launch,
or a Rust seed fallback does not close this gap.

Resolution requires a supported implementation of scoped environment launch and
actual descendant-group retirement, plus an admitted source-matched executable.
Leader-only reaping cannot prove that a descendant stopped writing the result
file. Verify scoped environment isolation, bounded output, cancellation,
retirement acknowledgement, result-file safety, and failure framing on each
supported host. Source inspection and pure framing fixtures are insufficient.

Evidence: capability response near line 3749 in the runtime owner; wrapper
capability admission in `src/app/test_runner_new/sdn_wrapper.spl`. Native wrapper
execution has not been verified for this feature candidate.

## Existing Linux owner capture gap

The direct Linux cgroup owner can accept general arguments, an explicit
environment, and pinned executable/cwd identities. Its retirement observation
uses leader reap plus an unpopulated cgroup. However, its stdout and stderr are
redirected directly to exclusive regular files without per-stream byte caps or
seen/retained/truncation counters. Reading those files with a bounded reader
after retirement limits reader memory, but does not bound capture disk usage.
The durable group-worker protocol additionally fixes its worker arguments and
cwd, so it cannot directly launch this test CLI.

The required owner extension needs immutable per-stream limits, owner-managed
nonblocking pipe capture, bounded retained bytes with seen-byte counters,
explicit overflow/error disposition and scope cancellation, and frozen output
digests bound to the request and retirement receipt. Partial start failures
must preserve cleanup authority. Applying a general file-size resource limit
would also restrict files created by the tests and does not establish the
required capture evidence.

Source evidence: `runtime_linux_group_owner_impl.h` output redirection near
lines 561–579, and the direct Linux request/poll contract. This is a source
audit finding; no native owner qualification was performed.

## 2026-11-20 update: Linux/Darwin admitted in source, Windows still open

The Linux owner has advertised `POV4_CAP_PROCESS_GROUP_RETIRE` since
`998622c8624` and Darwin already did, but
`test_sdn_group_retirement_preflight` still returned `Err` on both branches, so
`--format sdn` could not succeed on any host. The preflight now uses the shared
`process_observation_monitor_group_gap_v4` contract (the HIR-worker and
bootstrap-builder gate). Linux/Darwin end-to-end execution of the wrapper is
unrun; only the pure preflight spec ran (Windows seed, 10/10).

Windows remains open and is a runtime platform gap, not a native-build or pin
defect: `rt_process_observation_v4_capabilities_value` is the
`{4, 8, 0, 0, 0, 0, 0, ENOTSUP}` stub outside unix, so both the natively built
runner and the seed interpreting the runner source stop at
`SDN worker scoped-environment process provider is unavailable or insufficient`
(rc 1). Closing it needs a Windows V4 owner (job-object group retirement,
pinned executable/cwd, bounded capture) in `runtime_process_owned.c`.
