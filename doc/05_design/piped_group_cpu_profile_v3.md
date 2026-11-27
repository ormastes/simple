# Versioned group-stream CPU and shared broker profile V3

Base 8028e75917289a50b31bb695cbb5fe6f8c528667; work/piped-group-cpu-owner-20261107.
Status IMPLEMENTATION / AWAITING_VERIFICATION. Native plan approved before edits;
one finite native contract build/run is recorded below. Existing V1/V2 native arities and strict wire
entrypoints remain unchanged. A nil profile retains exact V2 bytes. Some(profile)
uses explicit SIMPLE-GROUP-STREAM-3 through shared codec cores and full identity.

## Frozen policy

Helper CPU is signed millicores, not a thread count. For 1..9 use period 1000000 us
and quota=millis*1000; for >=10 use period 100000 us and quota=millis*100. Reject zero,
negative, overflow and mismatched redundant fields; no rounding or unlimited
fallback. Install exact cpu.max and read it back before clone3. Descendants that
remain in the owned cgroup share that cap. No second resource ledger is added.

The authenticated host allocates a shared broker overhead partition once.
GroupProcessBrokerBudgetV3 binds actual cgroup path/device/inode, generation,
policy digest, finite CPU/memory caps and reserved CPU/memory. Native compares
actual readback exactly and rejects caps exceeding authenticated reservations.
This is not native authentication of the signed host policy: host policy remains
its existing owner. The profile is part of the complete canonical launch digest.

Broker target is a direct child of the delegated parent. A fresh helper parent
is a different direct child, so broker overhead is neither omitted nor nested
inside a per-helper charge. Native target admission opens/verifies the broker
cgroup FD and retains it until clone. The existing detacher starts atomically
inside that scope with clone3(CLONE_INTO_CGROUP); the final detached broker
inherits it. No caller service migration or additional supervisor is introduced.
Before worker clone the broker verifies its current membership by actual cgroup
mapping plus device/inode and exact CPU/memory readback again. Host delegation
must already include cpu and memory; only the newly owned helper parent enables
both controllers. The ordinary memory-only V1/V2 paths are not relaxed.

Image modes are exactly sealed-main-image-v1 and trusted-local-admin-image-fd-v1.
Only the child image may use the latter: open no-follow, observe/hash/stat the
same original FD, then execute that FD. Local administrator mutation remains an
explicit trust assumption; this mode does not claim immutable main-image bytes.
Broker image stays sealed. There is no automatic mode fallback. Neither mode
pins the complete dynamic loader/shared library dependency graph. Dynamic Podman
compatibility needs actual execution/protocol readiness evidence.

## Native ABI frozen for this slice

All text has explicit counted byte lengths; numeric profile is exactly 12 typed
integer words: helper millis/quota/period, broker device/inode/generation,
broker quota/period/reserved CPU, broker memory/reserved memory, child mode id.
Mode id 0 is sealed and 1 trusted original; all other ids fail. Names:

- rt_linux_group_stream_admit_profiled_v3(delegated,len,brokerPath,len,policyDigest,len,words)
- rt_linux_group_stream_verify_broker_profiled_v3(same): current broker membership
- rt_linux_group_launch_stream_broker_profiled_v3(existing V2 args plus brokerPath,len,policyDigest,len,words)
- rt_linux_group_parent_acquire_profiled_at_v3(existing counted V2 args): cpu+memory
- rt_linux_group_start_stream_profiled_v3(existing V2 args plus brokerPath,len,policyDigest,len,words)

Private cores are shared. Opened verified broker FD survives through clone;
pathname reopening is never substituted for that capability. Non-Linux/core-only
providers return explicit unavailable results. No copied registry or Rust alias.

broker.resources.sdn binds identity, canonical profile digest, exact numeric
readbacks/identity/reservation fields and mode. Path is already request/profile
bound and is not re-escaped into this <=4096-byte receipt. Publish only after real
native cap checks and child-owner admission, before ready-transfer receipt.
Actual-child reap collection requires this receipt; unlaunched cleanup makes no
claim of enforced child execution. Deadline remains launch admission only.

## Implemented source and evidence limits

The canonical profile/launch/template codecs, five native OS leaves, explicit
unavailable providers, Linux wrappers and existing broker dispatch are now
implemented in this worktree. The parent lane owns full-owner/facade receipt
validation and signed-host correlation. Common tests are in
`test/01_unit/lib/io/group_process_stream_profile_v3_spec.spl`; transfer provenance
tests are in `test/01_unit/lib/io/piped_process_profile_v3_spec.spl`.
The finite native contract fixture is
`src/runtime/test/group_stream_profile_v3_selfcheck.c`. Its regular-file readback
cases test parsing only; they do not prove a kernel cgroup cap. All 9 pure SSpec cases and actual cgroup/broker qualification are
NOT_RUN. No full lifecycle or final-head qualification is claimed.

Actual child admission may return a cleanup-required lease after an exec-channel
error; resource receipt is still published from the cap checks that preceded
that real clone. The ready receipt means an owned transfer is available. Neither
that receipt nor CLOEXEC-channel EOF proves successful workload exec/attach.
Uncertain native outcomes retain the existing broker/owner and do not relaunch.

The strict V3 profile requires `memory_policy == enforce`; nil/V2 monitor remains
unchanged. The pre-grant template domain normalizes only transport generation and
launch deadline to zero. It cannot be decoded/launched as a real request.
Applying a profile before grant uses this template path without inventing expiry.
Grant deadline checks gate launch only and do not cap workload duration.

## Ownership and platform references

The five new native symbols are explicit entries in the existing C-owner policy
in `scripts/check/check-rt-dual-implementation-ratchet.shs`; unknown-symbol
enforcement is unchanged. The compiler's normal and CoreC runtime source sets
both include `runtime_process_owned`, which includes the Linux implementation
header. Non-Linux definitions return unavailable. This registration follows the
root-reviewed OS-boundary design under user-authorized implementation; it is not
a blanket exemption for new runtime symbols.

The quota policy follows the kernel's [cgroup v2 CPU controller](https://www.kernel.org/doc/html/latest/admin-guide/cgroup-v2.html)
and [CFS bandwidth bounds](https://docs.kernel.org/scheduler/sched-bwc.html).
It controls CPU bandwidth over the selected period, not instantaneous affinity
or thread count. The host must keep the authenticated broker budget stable for
the enrolled epoch; changing it requires drain and reconciliation. Native checks
are admission/readback observations, not protection from a trusted administrator
changing cgroup limits later.

## Pending checks

Pure quota boundary/overflow, profile identity and strict V2/V3 rejection tests;
actual CPU delegation/write/readback mismatch-before-clone; broker fd inode/path/
current-membership substitution; oversized/shared caps; ordinary dynamic image
under explicit trust and no fallback; actual cpu.stat throttling/descendants.
No source-only parser result or files-only probe will be claimed kernel cap
qualification. CPU affinity 0-4 applies to all local checks/builds/hooks.

Resource publication has one initial attempt while a child is live. Failure
routes to the existing cancel/drain loop instead of delaying timeout/cancel
service. Once the real tree has been collected, publication may retry from the
same retained admitted profile before terminal publication; no-child cleanup
never enters this actual-child receipt path. The manual records the real
filesystem-failure acceptance scenario, currently NOT_RUN.

The allocated native contract snapshot built and ran once with exit 0 using the
normal CoreC providers. It proves typed native policy rejection and exact
readback parsing only. Durable command/input/compiler/binary hashes and explicit
NOT_RUN boundaries are in
`doc/06_spec/01_unit/lib/io/group_stream_profile_v3_native_contract_evidence.sdn`.
Temporary regular files are not cgroup enforcement proof. No old green fixture
was rerun.

The native snapshot's runtime_process.c hash is related boundary provenance only;
that file is not a linked translation unit in the recorded recipe. Other listed
owner implementation/header hashes describe the fixture's included boundary.
This is an explicit input inventory, not a complete system dependency closure.
Separate build/run timing was not recorded and is unavailable.
