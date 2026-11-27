# Pure-Simple container runtime

Date: 2026-11-26. Baseline: `release/1.0.0` @ `790371966e6` (lane E landed, #11914).
Status: proposed architecture. Nothing here is implemented or measured unless a
line says so. Plan: `doc/03_plan/platform/container/pure_simple_container_plan.md`.

## 1. Decision

Add one container backend that needs no Docker, WSL, HCS, Podman or other engine.
It is written once, host-neutral, and reaches the host only through SOSIX. Host
differences live in SOSIX variant bodies selected per target OS. Windows is the
first variant that runs; Linux, FreeBSD and macOS are specified here and stay
typed refusals until their own lanes land.

| Fact | Value |
|---|---|
| Backend id | `simple-pure-process` |
| Engine id | `simple-pure-container-v1` |
| `isolation_kind` reported | `native-sandbox` on Windows and macOS; `native-container` only on a host variant that proves namespace or jail isolation |
| Relation to existing leaves | New sibling. Never aliased to `windows-docker-process`, `windows-hcs-v1`, `freebsd-jail-v1`, `macos-seatbelt-process` or the Linux OCI adapter, and it does not join `SimpleContainerOwnerV2` in increment 1 |

`doc/04_architecture/windows_server_process_container.md` says the Windows leaf
"never substitutes a bare host process". That stays true for the `native-container`
route. This backend is a different route with a weaker, honestly reported kind;
a request for `native-container` is still refused on Windows (§6).

## 2. Layering

```text
caller (build runner, test runner, CLI)
        |
pure_runtime_v1            host-neutral lifecycle: view -> rootfs -> launch -> wait -> destroy
        |                  no host branch, no extern, no @when
        +-- contracts      common/contracts/sosix/containment_v1   (request, limits, support)
        |                  common/contracts/container/pure_backend_v1 (support -> capability report)
        +-- storage        rootfs_materialize_v1 -> storage_view_v1 -> immutable_store_v1
        |
SOSIX facades              sosix/containment_v1, sosix/contained_write_v1, sosix/readonly_share_v1   (level 0)
        |                  the only place a host is chosen: one @when(os=) import switch per facade
SOSIX variant bodies       sosix/windows/*   sosix/linux/*   sosix/freebsd/*   sosix/macos/*
        |
existing host owners       io/windows_process_owner, io/file_ops, sosix/darwin_sandbox_v1, ...
```

Rules:

1. Container code imports `std.nogc_sync_mut.sosix.*` and contracts only. It never
   imports `io.windows_*`, `io.linux_*`, an ABI module, or declares an `extern`.
2. Host selection follows `doc/04_architecture/platform/platform_variant_directory_rule.md`:
   bodies under `sosix/<os>/`, canonical names (`macos`, not `mac`), an identical
   public API in every variant, and a typed refusal where a host is not implemented.
   Binding (owner decision, final): each level-0 facade is one
   `@when(os="windows"): export use ... @elif(os="linux"): ... @end` import
   switch (the form `nogc_sync_mut/container/machine_authority_cleanup_v1.spl`
   uses) and contains no body and no other host test. That directory rule's §3
   rule 1 forbids `@cfg(os=)` in level-0 files once a variant exists, and the
   `variants/` resolver hook it points to is not implemented, so P2 adds a
   one-line exception to that rule for body-free import-switch facades. There
   is no resolver lane. `scripts/check/check-platform-variant-dirs.shs` matches
   only `@cfg(`, so an `@when(os=)` switch is not flagged and P1 can land
   before P2's exception.
3. A variant reports what it enforces through `SosixContainSupportV1`. The runtime
   never infers support from the OS name.
4. An unsupported axis is refused before a child exists
   (`sosix_v4_provider_composition_2026_10_29.md`: typed no-child refusal). It is
   never silently weakened.

## 3. Modules

New files (N) and edited existing files (E). Everything else is reused unchanged.

| Path | N/E | Role |
|---|---|---|
| `src/lib/common/contracts/sosix/containment_v1.spl` | N | Units, request, limits, support, poll, admission; pure request check |
| `src/lib/common/contracts/container/pure_backend_v1.spl` | N | Backend ids; `SosixContainSupportV1` + evidence -> `ContainerCapabilityReportV1` |
| `src/lib/nogc_sync_mut/sosix/containment_v1.spl` | N | Facade: start, poll, cancel, collect, support |
| `src/lib/nogc_sync_mut/sosix/windows/containment_v1.spl` | N | Windows body: job + restricted token launch |
| `src/lib/nogc_sync_mut/sosix/{linux,freebsd,macos,simpleos}/containment_v1.spl` | N | Typed-refusal bodies until their lanes |
| `src/lib/nogc_sync_mut/sosix/windows/restricted_identity_v1.spl` | N | Restricted low-integrity token open/close |
| `src/lib/nogc_sync_mut/sosix/windows/security_abi_v1.spl` | N | advapi32 externs for token and label |
| `src/lib/nogc_sync_mut/sosix/readonly_share_v1.spl` | N | Read-only link; portable body over `io/file_ops`, no host switch |
| `src/lib/nogc_sync_mut/sosix/contained_write_v1.spl` | N | Facade: contained-write grant |
| `src/lib/nogc_sync_mut/sosix/windows/contained_write_v1.spl` | N | Windows body: low label + scope-SID ACE on a directory |
| `src/lib/nogc_sync_mut/sosix/{linux,freebsd,macos,simpleos}/contained_write_v1.spl` | N | Same function name; typed refusal |
| `src/lib/nogc_sync_mut/io/windows_process_owner.spl` | E | One internal admit core taking token + process-count + CPU-rate extras; existing entry points forward unchanged |
| `src/lib/nogc_sync_mut/io/windows_process_owner_abi.spl` | E | `CreateProcessAsUserW`, job basic-limit and CPU-rate offsets |
| `src/lib/nogc_sync_mut/storage/rootfs_materialize_v1.spl` | N | Base manifest -> read-only hardlink tree |
| `src/lib/nogc_sync_mut/storage/storage_view_v1.spl` | E | Add `storage_view_v1_base_entries` (read-only listing) |
| `src/lib/nogc_sync_mut/storage/immutable_store_v1.spl` | E | Add `immutable_store_v1_link_object` |
| `src/lib/nogc_sync_mut/container/pure_runtime_v1.spl` | N | Host-neutral runtime |
| `src/lib/common/contracts/container/pure_sandbox_observed_v1.spl` | N | `SosixContainSupportV1` + evidence -> shared `SandboxObservedCapabilityV1` |
| `src/lib/common/contracts/container/contained_lifecycle_v1.spl` | N (extracted) | Attempt state machine moved out of `seatbelt_provider_v1` (§9) |
| `src/lib/common/container_policy/attempt_dir_plan_v1.spl` | N (extracted) | Attempt directory plan moved out of `seatbelt_provider_v1` (§9) |
| `src/lib/common/contracts/container/sandbox_canary_v1.spl` | N (extracted) | Canary plan/result/status moved out of `seatbelt_capabilities_v1` (§9) |
| `src/lib/nogc_async_mut/container/providers/macos/{seatbelt_provider_v1,seatbelt_capabilities_v1}.spl` | E | Forward to the extracted modules; public names and error strings unchanged |
| `src/lib/common/contracts/container/backend_identity_v1.spl` | E | Add the backend and engine ids (P0); `pure_backend_v1` constants alias them |
| `src/lib/nogc_sync_mut/io/windows_memory_cap_probe_v1.spl` | E | Remove the duplicate report builder (P4) |

Reused as is: `capability_report_v1`, `lifecycle_journal_v1`, `runtime_v1`
(phases and `RuntimeOperationV1`), `storage_view_v1` create/save/load/destroy,
`immutable_store_v1` pins and GC, `io/file_ops.{file_hardlink, file_seal_readonly}`,
the whole suspended-create/job/kill-on-close/stdio/poll/cancel/collect sequence in
`windows_process_owner`, `sosix/darwin_sandbox_v1`, and lane E's landed
`windows_memory_cap_probe_v1` (probe run and verdict) as the only source of the
Windows `memory_hard_limit` evidence, reached through the SOSIX op in §4.2.

Not touched in increment 1: `api_v2.spl`, `service_v2.spl`, and every
`providers/**` leaf except the two macOS files S0 turns into forwards.

## 4. SOSIX extensions

All public values use domain units. Bool-backed units are always truthy, so every
condition reads `.value`.

### 4.1 Contract — `std.common.contracts.sosix.containment_v1`

```simple
pub unit SosixContainBytesV1: i64      # 0 = no limit
pub unit SosixContainCountV1: i64      # 0 = no limit
pub unit SosixContainCpuRateV1: i64    # hard cap, 1/100 percent of the whole machine, 1..10000; 0 = no limit
pub unit SosixContainMillisV1: i64     # 0 = no deadline
pub unit SosixContainExitCodeV1: i64
pub unit SosixContainSlotV1: i64
pub unit SosixContainFlagV1: bool

pub const SOSIX_CONTAIN_IDENTITY_INHERIT_V1 = "inherit"        # caller identity, limits only
pub const SOSIX_CONTAIN_IDENTITY_RESTRICTED_V1 = "restricted"  # write-confined
pub const SOSIX_CONTAIN_NETWORK_HOST_V1 = "host"
pub const SOSIX_CONTAIN_NETWORK_NONE_V1 = "none"

pub struct SosixContainLimitsV1:
    memory: SosixContainBytesV1        # aggregate over all descendants
    processes: SosixContainCountV1     # live processes, leader included
    cpu_rate: SosixContainCpuRateV1
    wall: SosixContainMillisV1

pub struct SosixContainRequestV1:
    program: text
    program_digest: text               # sha256 hex; pinned by the host owner before launch
    args: [text]
    environment: [text]                # complete "K=V" block; nothing is inherited
    directory: text                    # cwd
    stdout_path: text
    stderr_path: text
    limits: SosixContainLimitsV1
    identity: text
    scope: text                        # container identity; names the per-container write principal / cgroup / jail
    network: text
    readonly_dirs: [text]              # must stay unwritable by the child
    writable_dirs: [text]              # already granted by sosix_fs_grant_contained_write_v1
    private_pids: SosixContainFlagV1   # child must not see host processes
    root_dir: text                     # "" = no root remap requested

pub struct SosixContainSupportV1:
    mechanism: text                    # "windows-job+restricted-token", "linux-userns+cgroup2", ...
    memory_accounting: text            # a CONTAINER_MEMORY_ACCOUNTING_*_V1 value or ""
    memory_hard_limit: SosixContainFlagV1
    process_limit: SosixContainFlagV1
    cpu_rate_limit: SosixContainFlagV1
    kill_all_descendants: SosixContainFlagV1
    write_confinement: SosixContainFlagV1   # mechanism implemented; static, not a measured result
    read_confinement: SosixContainFlagV1
    network_isolation: SosixContainFlagV1
    pid_isolation: SosixContainFlagV1
    root_remap: SosixContainFlagV1
    unprivileged: SosixContainFlagV1   # false = needs administrator/root provisioning

pub struct SosixContainPollV1:
    terminal: SosixContainFlagV1
    tree_empty: SosixContainFlagV1
    timed_out: SosixContainFlagV1
    cancelled: SosixContainFlagV1
    exit_code: SosixContainExitCodeV1
    active_processes: SosixContainCountV1
    peak_memory: SosixContainBytesV1

pub struct SosixContainLeaseV1:
    slot: SosixContainSlotV1

pub struct SosixContainCanaryV1:
    id: text
    expected: text                     # "allow" | "deny"
    observed: text                     # "allow" | "deny" | "not-run"
    control: text                      # same op on the allowed target, same run: "allow" | "deny" | "not-run" | "none"

pub struct SosixContainQualifyRequestV1:
    probe_program: text                # executable that runs the probe script
    probe_digest: text                 # sha256 of probe_program
    probe_script: text                 # the repo canary probe; its sha256 is checked against a pinned constant
    work_dir: text                     # empty scratch directory the op owns for the run
    scope: text
    wall: SosixContainMillisV1

pub struct SosixContainQualifyResultV1:
    canaries: [SosixContainCanaryV1]   # every planned canary, in plan order
    evidence_digest: text              # "" when nothing ran
    reason: text                       # "" = ran to completion

pub const SOSIX_CONTAIN_CANARY_LAUNCH_EXIT_V1 = "launch-exit-code"        # allow
pub const SOSIX_CONTAIN_CANARY_OWN_WRITE_V1 = "own-dir-write"            # allow
pub const SOSIX_CONTAIN_CANARY_LOWER_READ_EXEC_V1 = "lower-read-exec"    # allow
pub const SOSIX_CONTAIN_CANARY_TREE_EMPTY_V1 = "tree-empty-after-cancel" # allow
pub const SOSIX_CONTAIN_CANARY_LOWER_WRITE_V1 = "lower-overwrite"        # deny
pub const SOSIX_CONTAIN_CANARY_USER_PRIVATE_WRITE_V1 = "user-private-write"   # deny
pub const SOSIX_CONTAIN_CANARY_OTHER_SCOPE_WRITE_V1 = "other-scope-write"     # deny
pub const SOSIX_CONTAIN_CANARY_OTHER_SCOPE_PROCESS_V1 = "other-scope-process-open"   # deny
pub const SOSIX_CONTAIN_CANARY_PROCESS_LIMIT_V1 = "process-limit-spawn"  # deny

# One canary passes when it is present exactly once, observed == expected, and
# (for a deny canary) control == "allow". A deny without a successful positive
# control is a failure, so a broken probe cannot read as "denied".
pub fn sosix_contain_canary_pass_v1(result: SosixContainQualifyResultV1, id: text) -> SosixContainFlagV1
# True only if all nine pass.
pub fn sosix_contain_canaries_pass_v1(result: SosixContainQualifyResultV1) -> SosixContainFlagV1

pub enum SosixContainAdmissionV1:
    Started(lease: SosixContainLeaseV1)
    RejectedBeforeStart(reason: text)   # no child exists
    FailedAfterCleanup(reason: text)    # a child existed and is proven gone
    Unknown(reason: text)               # cleanup unproven; caller keeps the journal

# "" = admissible. Refuses every requested axis the variant does not enforce.
pub fn sosix_contain_request_reason_v1(request: SosixContainRequestV1,
        support: SosixContainSupportV1) -> text
pub fn sosix_contain_support_none_v1(mechanism: text) -> SosixContainSupportV1
```

`sosix_contain_request_reason_v1` reasons (fixed strings, checked in this order):
`containment-request-invalid`, `containment-readonly-requires-restricted`
(any `readonly_dirs` while `identity` is not `restricted`; on every host the
read-only guarantee comes from the restricted identity, and an `inherit` child
could write through a hard link into a store object all containers share),
`containment-memory-limit-unsupported`,
`containment-process-limit-unsupported`, `containment-cpu-rate-unsupported`,
`containment-write-confinement-unsupported` (identity `restricted` or any
`readonly_dirs`), `containment-network-isolation-unsupported` (network `none`),
`containment-pid-isolation-unsupported`, `containment-root-remap-unsupported`.
A wall deadline with `kill_all_descendants` false is
`containment-deadline-unsupported`. `identity: "restricted"` with an empty or
non-identifier `scope` is `containment-request-invalid`. There is no
read-confinement request field in v1: its absence is reported, not requested
(§6).

### 4.2 Launch — `std.nogc_sync_mut.sosix.containment_v1`

```simple
pub fn sosix_contain_support_v1() -> SosixContainSupportV1
pub fn sosix_contain_start_v1(request: SosixContainRequestV1) -> SosixContainAdmissionV1
pub fn sosix_contain_poll_v1(lease: SosixContainLeaseV1) -> Result<SosixContainPollV1, text>
pub fn sosix_contain_cancel_v1(lease: SosixContainLeaseV1) -> Result<SosixContainFlagV1, text>
pub fn sosix_contain_collect_v1(lease: SosixContainLeaseV1) -> Result<SosixContainPollV1, text>
pub fn sosix_contain_qualify_v1(request: SosixContainQualifyRequestV1) -> SosixContainQualifyResultV1
```

`support` is static: it says which mechanisms the variant implements and never
depends on a measurement, so `start` has no dependency on canaries. Whether
the mechanism works on this host is measured by `sosix_contain_qualify_v1`, a
separate op that sets up its own directories under `work_dir` (one granted to
`scope`, one to a second scope, one linked file) and launches only
`probe_program` through the variant's internal launch. Its result is folded
into `PureContainerEvidenceV1.write_confinement_observed`, and the runtime, not
`start`, refuses a `restricted` run without it (§7). A host without a
qualify body returns no canaries and `containment-qualify-unimplemented-<os>`.

`start` calls `sosix_contain_request_reason_v1` against its own `support` first.

| Axis | Windows (increment 1) | Linux | FreeBSD | macOS |
|---|---|---|---|---|
| Owner reused | `io/windows_process_owner` | `io/linux_process_owner`, `linux_process_replace_*`, `io/linux_container_containment_v1` (retirement evidence) | none: FreeBSD is served by the existing `jail_runtime_v1` sibling backend, see below | `darwin_sandbox_v1` and the SBPL emitter, after N3 moves both (see below) |
| Memory | Job `JOB_OBJECT_LIMIT_JOB_MEMORY` (commit) | cgroup v2 `memory.max` | `rctl jail:<n>:memoryuse:deny` | none aggregate (`RLIMIT_AS` is per process) -> unsupported |
| Process count | Job `ActiveProcessLimit` | `pids.max` | `rctl maxproc:deny` | `RLIMIT_NPROC` is per UID -> unsupported |
| CPU rate | `JobObjectCpuRateControlInformation` hard cap | `cpu.max` | `rctl pcpu:deny` | none (`RLIMIT_CPU` is CPU seconds) -> unsupported |
| Kill descendants | `KILL_ON_JOB_CLOSE`, no breakaway | `cgroup.kill` | `jail_remove` | process group only -> false |
| Write confinement | low integrity + restricting SIDs + per-scope grant ACE (§4.3); mechanism flag, proven per host by `sosix_contain_qualify_v1` | mount namespace, read-only bind | jail path + `nullfs -o ro` | Seatbelt `deny file-write*` |
| Read confinement | not claimed (AppContainer, increment 2) | `pivot_root` | jail path | Seatbelt `deny file-read*` allowlist |
| Network | no | `CLONE_NEWNET` | jail without `ip4`/`ip6` or `vnet` | Seatbelt `deny network*` |
| PID isolation | no | `CLONE_NEWPID` | jail | no |
| Root remap | no | `pivot_root` | jail `path` | no |
| Unprivileged | yes | yes if user namespaces and cgroup delegation are available | no (root or delegated broker) | yes |
| `memory_accounting` | `job-commit` | `cgroup` | `jail-rss` | `` |

The FreeBSD column is a capability mapping only. No new jail owner is added:
the FreeBSD route is the existing `providers/freebsd/jail_runtime_v1.spl`
(ocijail, delegated authority), selected as a sibling backend like Docker (§10).
`sosix/freebsd/containment_v1.spl` stays a typed refusal.

Layering for the later variants: a SOSIX variant imports only `sosix/**`,
`io/**` and `common/**`, never `container/providers/**` or `src/os/**`.
So N3 first moves two files, leaving forwards: the pure SBPL emitter
`seatbelt_profile_v1` to `common/container_policy/`, and
`nogc_async_mut/sosix/darwin_sandbox_v1.spl` (a synchronous extern wrapper that
sits in the async tree today) to `nogc_sync_mut/sosix/macos/darwin_sandbox_v1.spl`,
so the sync macOS variant imports no async module. The SimpleOS body lives
in `src/os/sosix/` behind the existing SimpleOS SOSIX provider binding, while
`lib/.../sosix/simpleos/containment_v1.spl` stays a refusal on hosted targets.

The Windows variant also refuses, before any child exists, a `lower`,
`readonly_dirs` or `writable_dirs` path on a volume without persistent ACLs
(`GetVolumeInformationW` lacks `FILE_PERSISTENT_ACLS`, e.g. FAT/exFAT):
`containment-volume-no-acl`. Labels and ACEs enforce nothing there.

Memory-cap evidence is a SOSIX op in the same facade, so host-neutral code never
imports `io/windows_memory_cap_probe_v1`:

```simple
# std.nogc_sync_mut.sosix.containment_v1 (types defined in the facade, not in the P0 contract)
pub struct SosixContainMemoryProbeV1:
    program: text
    program_digest: text
    under_args: [text]
    over_args: [text]
    cap: SosixContainBytesV1
    work_dir: text
    wall: SosixContainMillisV1
pub struct SosixContainMemoryEvidenceV1:
    enforced: SosixContainFlagV1
    evidence_digest: text
    reason: text
pub fn sosix_contain_memory_cap_evidence_v1(probe: SosixContainMemoryProbeV1) -> SosixContainMemoryEvidenceV1
```

Windows runs lane E's `windows_memory_cap_probe_run_v1` three times (under, over,
uncapped baseline) and returns `enforced` only for `windows_memory_cap_verdict_v1`
= `Enforced`. Other hosts return `enforced` false with
`memory-cap-probe-unimplemented-<os>`.

Windows launch sequence, all inside the existing admit core: validate and pin the
executable -> create job -> set extended limits (`KILL_ON_JOB_CLOSE | JOB_MEMORY |
ACTIVE_PROCESS`) and CPU rate, read each back -> open restricted token for
`request.scope` ->
`CreateProcessAsUserW` suspended with an explicit handle list and the given
environment block -> assign to job -> resume. A restricted copy of the caller's
own primary token needs no privilege. Any failure after create terminates the job
and returns `FailedAfterCleanup` or `Unknown`, never `RejectedBeforeStart`.

### 4.3 Windows identity — `std.nogc_sync_mut.sosix.windows.restricted_identity_v1`

Windows-only (no facade; only `sosix/windows/containment_v1` imports it).

```simple
pub unit SosixWindowsTokenV1: i64
pub fn sosix_windows_restricted_token_open_v1(scope: text) -> Result<SosixWindowsTokenV1, text>
pub fn sosix_windows_restricted_token_close_v1(token: SosixWindowsTokenV1) -> SosixContainFlagV1
pub fn sosix_windows_scope_sid_v1(scope: text) -> Result<text, text>   # SDDL SID string, deterministic per scope
```

`OpenProcessToken` -> `CreateRestrictedToken(DISABLE_MAX_PRIVILEGE, restricting
SIDs = {Everyone S-1-1-0, Users S-1-5-32-545, the caller's logon SID, the fixed
reader SID, scope SID})` -> `SetTokenInformation(TokenIntegrityLevel,
S-1-16-4096)` -> `SetTokenInformation(TokenDefaultDacl, {scope SID, user SID,
SYSTEM})`. Reads back the integrity level and `TokenRestrictedSids`; a mismatch
closes the token and returns `Err`.

- The logon SID is needed because the window station and desktop are granted
  to it; without it the child can die at start with `0xC0000142`.
- The default DACL omits the logon SID and Everyone, so objects the child
  creates (its process, threads, files without an inherited ACL) are not
  openable by a child of another scope even though both are low integrity.
- The reader SID is one fixed SID shared by all containers. It only ever
  appears in read+execute ACEs on materialized base objects (§4.4).

Low integrity alone is not write confinement: a low child can write every
low-labelled object (the user's `LocalLow`, another container's `upper/` or
scratch). The restricting SIDs close that. A restricted token passes an access
check only if the restricting list is granted the access too, so the child can
write only where the label is low **and** the DACL grants write to Everyone,
Users or its own scope SID. `LocalLow` grants the user SID only; another
container's directories grant a different scope SID. The scope SID is derived
from `sha256(scope)` under one fixed prefix that P1 chooses and records; it
names no account.

This is unproven on this host. The mechanism counts as working only when
`sosix_contain_qualify_v1` returns all nine canaries passing. Every deny canary
carries a positive control: the same operation, in the same probe run, on a
target that must be allowed.

| Canary id | Attempt | Expected | Positive control |
|---|---|---|---|
| `launch-exit-code` | probe exits with a requested non-zero code and the op reads it back | allow | none |
| `own-dir-write` | write a file in own granted directory | allow | none |
| `lower-read-exec` | read and execute a linked base file | allow | none |
| `tree-empty-after-cancel` | cancel while the probe has live children; job reports no process | allow | none |
| `lower-overwrite` | overwrite the linked base file | deny | overwrite a file in own directory |
| `user-private-write` | write into the user's `LocalLow` | deny | write in own directory |
| `other-scope-write` | write into a directory granted to a second scope | deny | write in own directory |
| `other-scope-process-open` | open a live second-scope process for terminate, VM read and VM write | deny (all three) | the same three opens on the probe's own child succeed |
| `process-limit-spawn` | spawn one process beyond the job limit | deny | spawns within the limit succeed |

Setup is done by the op, not the probe: it forces a user-only DACL on the
linked file before applying the read grant (so `lower-read-exec` is not
satisfied by an inherited Users ACE), and it starts a real second-scope process
that stays alive for the process canary. Root processes are created with an
explicit security descriptor {scope SID, user, SYSTEM}, not only the token
default DACL.

The probe is a repo file, `src/lib/nogc_sync_mut/sosix/contain_canary_probe.spl`.
The op checks its sha256 against `SOSIX_CONTAIN_CANARY_PROBE_SHA256_V1` (a
constant in the facade, pinned by a P2 spec) and returns
`containment-qualify-probe-digest-mismatch` with no canary run otherwise.

`evidence_digest` = sha256 of the canonical line set: `sosix-contain-qualify-v1`,
`support.mechanism`, host OS build string, volume serial of `work_dir`, `scope`,
`probe_digest`, the probe script sha256, then `id:expected:observed:control` for
each canary in plan order. It is `""` when any canary is `not-run`.

Side effect, not claimed as a guarantee: files readable only by the user SID
become unreadable to the child.

### 4.4 Read-only sharing and write grant

```simple
# std.nogc_sync_mut.sosix.readonly_share_v1
pub struct SosixFsShareV1:
    status: text    # "linked" | "copied" | "rejected"
    reason: text

pub fn sosix_fs_link_readonly_v1(source: text, destination: text,
        allow_copy: SosixContainFlagV1) -> SosixFsShareV1

# std.nogc_sync_mut.sosix.contained_write_v1, and the same name in every
# std.nogc_sync_mut.sosix.<os>.contained_write_v1 variant behind it
pub fn sosix_fs_grant_contained_write_v1(empty_dir: text, scope: text) -> text   # "" = granted
pub fn sosix_fs_grant_contained_read_v1(tree: text) -> text                      # "" = granted
```

| Op | Windows | Linux / FreeBSD / macOS |
|---|---|---|
| `link_readonly` | `file_hardlink` (`CreateHardLinkW`, already in `io/file_ops`). `file_seal_readonly` answers false on Windows by design and is not required: the object keeps its medium integrity label, so a low-integrity child cannot open it for write | `file_hardlink` + `file_seal_readonly` (0444); the launch variant adds the read-only mount or Seatbelt rule |
| `grant_contained_read` | read+execute ACE for the fixed reader SID on a tree | typed refusal until that host's lane |
| `grant_contained_write` | Low mandatory label `(OI)(CI)` plus an inheritable modify ACE for the scope SID, via `SetNamedSecurityInfoW` | typed refusal `contained-write-unimplemented-<os>` until that host's lane defines its grant; never "granted" by default |

`link_readonly` has one portable body: it links, then seals where the host can
seal, and it never branches on the OS. It returns `copied` only when `allow_copy.value` and the link failed
(cross-volume, link-count limit, filesystem without hard links); otherwise
`rejected`. `grant_contained_write` refuses a non-empty directory
(`grant-target-not-empty`). That check is load-bearing: a hard link shares one
security descriptor across all its names, so labelling a tree that contains links
would make store objects writable by every container.

`grant_contained_write` also refuses a directory whose existing or inherited
ACEs already give Everyone, Users or the caller's logon SID write
(`grant-target-world-writable`): the restricting list contains all three, so
any child could write there.

`grant_contained_read` exists because the restricted access check applies to
read and execute too, and a hard link carries the store object's DACL. A store
under the user profile or `%TEMP%` has a user-only ACL, so `lower/` would be
unreadable. The op adds one read+execute ACE for the fixed reader SID to the
directory tree and every file under it (bounded count, idempotent, never a
write ACE, never a label change). The walk does not follow or descend into
reparse points (junctions, symlinks); it skips them and never touches their
targets. It deliberately reaches the shared store objects through the links;
one ACE per object ever, shared by all containers. The ACE is permanent for the
object's life and is not removed at dematerialize: other live containers link
the same object, and the SID exists only inside restricted container tokens,
so it grants nothing to ordinary processes. It disappears when GC deletes the
object. An ACL change does not alter the object's bytes or key.
Off Windows it returns `contained-read-unimplemented-<os>`. P1 owns it; the
runtime (P4) calls it on `lower/` after materialization, so P3 is unchanged.
A failure is a refusal before start, `rootfs-read-grant-failed`.

A `copied` fallback file is a new file under `lower/`. It inherits that
directory's medium label and has no scope ACE, so it is as unwritable as a link.

## 5. Windows rootfs

`storage_view_v1` is a byte API over a private manifest; it has no directory a
process can use. `rootfs_materialize_v1` adds one, with no union filesystem:

```text
<view_root>/<view_id>/
  upper/     existing view upper; low label; child cwd; the only directory `save` scans
  lower/     hardlinks to <store>/objects/<xx>/<key>.obj; medium label; read-only to the child
<state_root>/attempts/<key>/
  home/ tmp/ output/ ...   attempt scratch from the shared attempt-dir plan; low label; never saved
```

Scratch lives outside the view, so `TEMP` and profile writes never enter a saved
generation or count against the view's 240-byte / 16-segment path limits.

Store objects are raw payload files, so a hard link is the file. Every container
linking the same object maps the same file, and Windows shares its cache and
image pages between them.

- No copy-on-write over hard links. A base file is never writable in place; a
  changed file is written under `upper/`. The child gets `SIMPLE_CONTAINER_LOWER`
  and `SIMPLE_CONTAINER_UPPER`. `storage_view_v1_save` keeps scanning `upper/` only.
- The materializer pins the base refs (`immutable_store_v1_pin`, owner
  `pure-container`, pin id = view id) before linking and releases after `lower/`
  is removed. GC stays unaffected: no read-only attribute is set, so a store
  object can still be moved or deleted, and a surviving link keeps its bytes.
- A copy fallback is recorded per materialization. One copied file sets
  `readonly_file_backing_reuse` false for that report.
- `report.root_view_kind` = `hardlink-lower-split-upper`.

## 6. What Windows cannot isolate here, and how it is reported

| Property | Increment 1 | Why |
|---|---|---|
| Network namespace | no | Needs HCS/HNS or an AppContainer without network capabilities |
| PID namespace | no | Needs a silo (HCS). The child can enumerate host processes; integrity level blocks opening higher-integrity ones for write |
| Read confinement | no | A low-integrity token can still read the user's files. AppContainer is increment 2 |
| Root remap, transparent union | no | Needs bindflt/wcifs (administrator or HCS) |
| Kernel isolation | no | Shared kernel; not a boundary for hostile tenants |
| In-place base writes | denied | Mandatory integrity `NO_WRITE_UP` |

Fail-closed reporting uses two layers, because `ContainerCapabilityReportV1` v1
has no network or PID field:

1. Launch: `sosix_contain_request_reason_v1` refuses `network: "none"`,
   `private_pids` and `root_dir` before any child exists. Read confinement has
   no request field; its absence shows as `filesystem_confinement` false.
2. Admission: `pure_container_capability_report_v1` builds the report from
   `SosixContainSupportV1` plus measured evidence. On Windows:

| Report field | Value | Source |
|---|---|---|
| `isolation_kind` | `native-sandbox` | a `native-container` requirement fails `isolation-kind-mismatch` |
| `client_authority` | `user` | `support.unprivileged` |
| `filesystem_confinement` | false | needs read and write confinement together |
| `memory_accounting` | `job-commit` | `support.memory_accounting` |
| `memory_hard_limit` | true only with `sosix_contain_memory_cap_evidence_v1(...).enforced` | never from `support` alone |
| `memory_limit_update`, `memory_reclaim`, `durable_recovery`, `process_checkpoint`, `explicit_shared_memory` | false | not implemented |
| `readonly_file_backing_reuse` | true only if every base file was `linked` | materializer result |
| `ephemeral_cleanup` | true only if `tree_empty` and view destroy were both observed | runtime evidence |
| `filesystem_save_load` | true | `storage_view_v1` |
| `launch_qualified` | true only after a real contained launch returned its exit code on this host | runtime evidence |
| `evidence_revision` | non-empty only when evidence was measured | empty makes any constrained requirement fail `capability-evidence-missing`, which is checked before every mismatch reason |

There is one report builder for this backend,
`pure_container_capability_report_v1`. Lane E's
`windows_container_capability_report_v1` (`io/windows_memory_cap_probe_v1.spl:177`)
builds an overlapping report; P4 removes it and moves its spec onto the verdict
plus the single builder.

A v2 report with explicit `network_isolation` and `pid_isolation` fields is a
named gap, not part of this design (plan §6).

## 7. Runtime

```simple
# std.nogc_sync_mut.container.pure_runtime_v1
pub struct PureContainerSpecV1:
    container_id: text
    store: text
    view_root: text
    state_root: text                   # attempt scratch root, outside the view
    base_root: text
    quota: ViewBytesV1
    program: text                      # host path, or "lower:<rel>" / "upper:<rel>"
    program_digest: text
    args: [text]
    environment: [text]
    limits: SosixContainLimitsV1
    identity: text
    network: text
    requirement: ContainerCapabilityRequirementV1
    evidence: PureContainerEvidenceV1  # from pure_container_qualify_v1; empty = unqualified
    extra_grants: [PlannedGrantV1]     # shared filesystem_plan_v1 grants beyond lower/upper

pub struct PureContainerRunV1:
    status: text                       # "exited" | "rejected" | "cleanup-unproven"
    reason: text
    exit_code: SosixContainExitCodeV1
    peak_memory: SosixContainBytesV1
    report: ContainerCapabilityReportV1
    journal: ContainerLifecycleJournalV1

pub struct PureContainerQualifyV1:
    state_root: text                   # canary scratch is created under it
    view_root: text                    # the pair the evidence is bound to
    probe_program: text
    probe_digest: text
    probe_script: text
    memory_probe: SosixContainMemoryProbeV1

pub fn pure_container_qualify_v1(request: PureContainerQualifyV1) -> PureContainerEvidenceV1
pub fn pure_container_run_v1(spec: PureContainerSpecV1) -> PureContainerRunV1
```

Evidence comes first and from a separate call. `pure_container_qualify_v1` calls
`sosix_contain_qualify_v1` (the canaries; it never goes through
`sosix_contain_start_v1` or admission, so nothing is circular) and
`sosix_contain_memory_cap_evidence_v1`, then hands both to the one pure
producer of evidence, `pure_container_evidence_from_qualify_v1` (P0). No other
code sets an evidence field:

| Evidence field | Produced from |
|---|---|
| `launch_observed` | canary `launch-exit-code` passes |
| `cleanup_observed` | canary `tree-empty-after-cancel` passes |
| `write_confinement_observed` | the five deny canaries and `own-dir-write`, `lower-read-exec` all pass |
| `memory_cap_enforced` | `SosixContainMemoryEvidenceV1.enforced` |
| `roots_digest` | sha256 of `state_root`, newline, `view_root` |
| `evidence_revision` | see below |

The shared `SandboxObservedCapabilityV1.qualification` (§7 table) is
`sosix_contain_canaries_pass_v1`; there is no second canary set or second
qualification path. That producer sets `evidence_revision` to `pure:` + sha256 of the qualify `evidence_digest`, `memory_digest` and `roots_digest` joined by newlines,
or empty when the qualify `reason` is non-empty or its digest is empty, so unmeasured evidence never passes `capability-evidence-missing`. `base_fully_linked` is false in qualify
output and is set per run by the materializer.

`pure_container_run_v1` never produces evidence for its own admission. With an
empty `spec.evidence` any constrained requirement fails
`capability-evidence-missing`; with qualify output, a `native-container`
requirement reaches `isolation-kind-mismatch`.

A `restricted` run with `spec.evidence.write_confinement_observed` false is
refused before any effect: `write-confinement-unqualified`.

Evidence lifetime: it is bound to the `state_root`/`view_root` pair it was
produced for (`roots_digest`; a run with different roots is refused
`evidence-roots-mismatch`, checked after `capability-evidence-missing` and before every other mismatch reason), and qualify refuses when `work_dir`, `state_root`
and `view_root` are not on one volume. It is valid for the calling process
only: it is never persisted, and a new process, a reboot or an OS update
means qualifying again. The host build and volume serial inside
`evidence_digest` make a stale copy detectable in logs; v1 does not re-check
them at run time.

Order: `sosix_contain_support_v1` -> build report from support and
`spec.evidence` -> `container_capability_v1_admission_reason` -> the
`write-confinement-unqualified` check -> journal
`created` -> `storage_view_v1_create` -> materialize `lower/` -> if a base file
was copied and the requirement needs `readonly_file_backing_reuse`, refuse and
clean up -> `sosix_fs_grant_contained_read_v1(lower)` -> grant `upper/` and
scratch to `scope = container_id` ->
journal `starting` -> `sosix_contain_start_v1` -> poll to terminal -> collect ->
journal `stopped` -> remove `lower/`, release pin, `storage_view_v1_destroy` ->
journal `destroyed`. Every failure after `created` walks the journal's cleanup
actions; `Unknown` admission returns `cleanup-unproven` and keeps the journal.

The runtime owns no private state machine, directory layout or grant model:

- phase changes go through `contained_lifecycle_next_v1` (the machine the macOS
  Seatbelt leaf already uses) and are projected to `runtime_v1` phases;
- attempt scratch under `state_root` is laid out by
  `container_attempt_dir_plan_v1`; `USERPROFILE`/`APPDATA`/`LOCALAPPDATA` (or
  `HOME`) point at `home`, `TEMP`/`TMP` (or `TMPDIR`) at `tmp`. Each gets
  `sosix_fs_grant_contained_write_v1` and is removed at destroy;
- `extra_grants` are `PlannedGrantV1` values from `filesystem_plan_v1`. A grant
  with `Write` becomes a `writable_dirs` entry, any other a `readonly_dirs`
  entry. Overlap with a protected root is already refused by that planner;
- when the caller holds a `SandboxPolicyV1`, admission also runs the shared
  `sandbox_requirements_match_v1` against
  `pure_container_observed_capability_v1(support, evidence)`, mapped as:

| `SandboxObservedCapabilityV1` field | From |
|---|---|
| `guarantees.file` | `PathAccessPolicy` only if read and write confinement are both true; else `NoFileGuarantee` |
| `guarantees.network` | `DirectDenied` if `network_isolation`; else `NoNetworkGuarantee` (never `DirectDeniedBrokered`: no broker here) |
| `guarantees.process` | `StrictDescendantContainment` if `kill_all_descendants`; else `LeaderOnly` |
| `guarantees.cleanup` | `QualifiedTreeAbsence` only if `kill_all_descendants` and `cleanup_observed`; else `NoCleanupGuarantee` |
| `hard_memory_limit` | qualified only with `memory_cap_enforced` evidence |
| `hard_cpu_limit` | unqualified until throughput is measured |
| `qualification` | `sosix_contain_canaries_pass_v1` over the qualify result |

  On Windows in increment 1 this yields `NoFileGuarantee` and
  `NoNetworkGuarantee`, so both existing evidence profiles
  (`strict-owned-attempt-v1`, `finite-parent-owned-v1`) are refused. That is the
  intended fail-closed result until AppContainer (W2); the
  `ContainerCapabilityRequirementV1` path is the one that admits increment-1
  workloads.

Async wiring into `api_v2.spl` and a `SimpleContainerOwnerV2` case is increment 2.

## 8. Risks

- New advapi32 externs under the seed interpreter. Lane E proved kernel32 job
  externs resolve there; `windows_process_owner.spl` records one extern that did
  not. Each Windows lane starts with an extern-resolution smoke.
- Low integrity breaks programs that write outside `upper/` (profile, registry
  `HKCU`). The runtime points `TEMP`, `TMP`, `USERPROFILE`, `APPDATA` and
  `LOCALAPPDATA` at attempt scratch (§5).
- CPU rate control conflicts with a parent job that already sets it; `start`
  reads the setting back and refuses on mismatch.
- The Windows environment-variable set above replaces the earlier "under
  `upper/`" wording; nothing but workload output is written to `upper/`.
- `storage_view_v1` open items (junction swap between walk and open, stale handle
  after destroy) apply unchanged to `lower/` creation.

## 9. Shared vs per-host

Reviewed: `providers/macos/**`, `common/container_policy/**`, the portable
contracts under `common/contracts/container/`, `src/os/services/container/**`,
`src/os/kernel/loader/container_namespace.spl`, `src/os/kernel/ipc/cspace_spawn.spl`,
`src/os/kernel/scheduler/cspace_delegation.spl`, `src/os/sosix/process_launch_provider_v1.spl`.
"Shared" means one module that the Windows, macOS and SimpleOS routes all call.
Code moves; it is never copied. Extraction is lane S0 in the plan.

Limits of this review: the two SimpleOS research documents
(`llm_role_cspace_container_design.md`, `simple_orchestrator_and_container_2026-09-06.md`)
were read at outline level only. After S0, Windows and macOS call the shared
modules. SimpleOS already shares `runtime_v1` and `bundle_check_v1` but calls
nothing new until N4, which is unscheduled.

### Already host-neutral: reuse unchanged

| File | Verdict | Reason |
|---|---|---|
| `common/contracts/container/filesystem_policy_v1.spl` | shared | Its model is "access isolation over real host paths, not namespace virtualization", which is the Windows restricted-token model |
| `common/container_policy/filesystem_plan_v1.spl` | shared | Pure grant/deny planner; `canonical_path_within_v1` already takes `case_insensitive`, as NTFS needs |
| `common/container_policy/requirements_match_v1.spl`, `diagnostics_v1.spl` | shared | Policy-vs-observed admission with stable diagnostics |
| `common/contracts/container/sandbox_capability_v1.spl` | shared, unchanged | `SandboxObservedCapabilityV1` and `SandboxPolicyV1` values are portable and are built in code by the pure runtime. Not edited |
| `common/contracts/container/backend_identity_v1.spl` | shared, one edit (P0) | The one place a backend id is defined; P0 adds `simple-pure-process` / `simple-pure-container-v1` here |
| `common/container_policy/sandbox_policy_decode_v1.spl`, `simple_container_seatbelt_policy_v1_schema.sdn`, `endpoint_network_decode_v1.spl` | shared, unchanged | The decoder (`:284`) and the schema SDN both pin `backend: "macos-seatbelt-process"`. An SDN policy document for the pure backend needs both changed together and is a later lane; increment 1 does not decode one |
| `common/contracts/container/{runtime_v1,host_capability_v1}.spl` | shared | Already used by the Windows, FreeBSD, macOS and SimpleOS leaves |
| `common/contracts/container/{capability_report_v1,lifecycle_journal_v1}.spl` | shared | Landed in increment 1; no provider leaf emits a report yet (only `storage_view_v1` and lane E's probe use them). This backend is the first runtime consumer |
| `common/oci/bundle_check_v1.spl` | shared | SimpleOS `oci_import` already delegates to it |
| `common/storage/object_record_v1.spl`, `common/hash/hash_policy_v1.spl` | shared | Object identity for the hosted store and the SimpleOS layer store |

### macOS

| File | Verdict | Reason |
|---|---|---|
| `seatbelt_provider_v1.spl`: `seatbelt_lifecycle_next_v1`, `seatbelt_runtime_phase_v1`, state constants | extract to `contained_lifecycle_v1.spl` | Nothing in the machine is Darwin-specific. The Seatbelt names stay as forwards that keep the `seatbelt-` error prefix |
| `seatbelt_provider_v1.spl`: `SeatbeltAttemptDirPlanV1`, `seatbelt_attempt_key_v1`, `seatbelt_attempt_dir_plan_v1` | extract to `attempt_dir_plan_v1.spl` | Layout and key rules are neutral. Two Darwin rules stay in the Seatbelt forward: `seatbelt_path_check_v1` (requires a leading `/`, so `C:/...` fails) and the `sun_path` 103-byte check. The neutral plan keeps the host-independent checks only (non-empty, no control or non-ASCII byte, no empty/dot/dot-dot segment, no trailing slash, not a filesystem root) |
| `seatbelt_provider_v1.spl`: `MacOsSeatbeltAdapterV1`, launch plan, attempt policy | per-host | Seatbelt effect ordering and SBPL grants |
| `seatbelt_capabilities_v1.spl`: canary plan/result types, expected-vs-observed status | extract to `sandbox_canary_v1.spl` | "Qualified only when every planned canary has a recorded native result" is the rule Windows needs too |
| `seatbelt_capabilities_v1.spl`: the fixed Seatbelt canary list, manifest, probe transcript parser | per-host | Darwin build, helper digest and profile digest are Seatbelt facts |
| `seatbelt_profile_v1.spl` | per-host | SBPL emitter. It is the macOS counterpart of the Windows token + label step; both consume the same `PlannedGrantV1` list |
| `executable_preflight_v1.spl` | per-host | Mach-O. A Windows PE preflight would be its sibling behind the same `RuntimeValidationV1` |
| `native_admission_v1.spl`, `native_sandbox_provider_v1.spl` | per-host | Signed App Sandbox helper route, a different engine (`macos-native-sandbox-v1`) |
| `worker_protocol_v1.spl` | per-host for now | The HMAC frame protocol is neutral, but the pure backend launches in-process and has no worker. Extract when a second consumer exists |
| `sosix/darwin_sandbox_v1.spl` | per-host | Becomes the body the `sosix/macos/containment_v1.spl` variant calls (lane N3) |

### Linux, FreeBSD and Windows leaves

| File | Verdict | Reason |
|---|---|---|
| `providers/linux/oci_runtime_v1.spl` and the `engine_*`, `oci_*`, `request_*`, `installed_*`, `whole_inventory_*` files | per-host sibling backend | Podman OCI engine adapter (`linux-podman`). Not on the pure path |
| `providers/linux/{containment_v1,containment_observer_v1,containment_inspect_v1,containment_profile_v1,cleanup_scope_v1}.spl` | per-host | Bind OCI observations to a retained native snapshot |
| `io/linux_container_containment_v1.spl` | per-host; reused by N1 | Pinned cgroup + namespace observation owner. N1 uses it for `tree_empty` and retirement evidence and adds no second observer |
| `providers/linux/{agent_workspace_*,workspace_*,fresh_epoch_*,local_mounts_v5,user_mapping_v3,execution_user_v2}.spl` | per-host | Linux agent-workspace and fresh-epoch lifecycle of the V2/V3 API |
| `providers/linux/host_capability_v1.spl` | per-host adapter | Copies the OCI probe into shared `ContainerHostCapabilityV1`; the pattern A1 repeats for `ContainerCapabilityReportV1` |
| `providers/linux/simple_container_adapter_v2.spl`, `providers/windows/simple_container_adapter_v2.spl` | per-host | The two cases of `SimpleContainerOwnerV2`. A1 adds the pure case beside them |
| `providers/freebsd/jail_runtime_v1.spl` | per-host sibling backend, reused | Existing FreeBSD route over ocijail with delegated authority. No pure jail owner is added |
| `providers/windows/docker_*.spl`, `host_observation_v2.spl`, `runtime_operation_projection_v1.spl`, `primary_*` | per-host sibling backend | Docker process-isolation route (§10) |
| `providers/windows/hcs_runtime_v1.spl` | superseded | Its own header calls it a historical containerd/runhcs intent builder; Docker is canonical |
| `container/shared/{request_digest_v1,request_record_v1,configuration_*,logs_capture_v1}.spl` | shared | Already host-neutral. `request_digest_v1` is the digest form for canary evidence |
| `io/windows_process_owner.spl`, `io/windows_memory_cap_probe_v1.spl` | per-host | Reached only through the Windows SOSIX variant |

### SimpleOS

| File | Verdict | Reason |
|---|---|---|
| `os/services/container/runtime_provider_v1.spl`, `container_runtime.spl` | per-host | Scheduler-task launch with a kernel-supplied context. They become the body of the `sosix/simpleos/containment_v1.spl` variant (lane N4) |
| `os/sosix/process_launch_provider_v1.spl` | per-host | Existing SimpleOS SOSIX launch adapter; N4 composes it |
| `os/services/container/container_manager.spl` | per-host | Userland ECS policy owner. Its `ResourceDomain {cpu, mem, io, pids}` overlaps `SosixContainLimitsV1` on `mem` and `pids` only: `cpu` is shares (not a hard cap), `io` has no SOSIX field, and there is no wall deadline. N4 maps the two common fields and must name the rest as gaps |
| `os/kernel/loader/container_namespace.spl` | per-host | Kernel enforcement stays MDSOC-only. `container_view_allows_path` looks like `canonical_path_within_v1` but is stricter (refuses any `..` substring, root `/` allows all, empty root denies all), so it is not replaced. Sharing it would need those rules added to the common function first; not proposed |
| `os/services/container/container_storage.spl` | per-host | In-memory layer/COW/GC model with no host filesystem. Shares identity through `object_record_v1` and `hash_policy_v1`, not through code |
| `os/services/container/oci_import.spl` | per-host edge | Already a thin adapter over shared `bundle_check_v1` |
| `os/kernel/ipc/cspace_spawn.spl`, `os/kernel/scheduler/cspace_delegation.spl` | per-host | Capability-space attenuation is the SimpleOS enforcement mechanism; no hosted OS has an equivalent. It is how a SimpleOS variant can affirm confinement flags the hosted variants cannot |
| `os/kernel/replay/checkpoint/container_{checkpoint,restore}.spl` | per-host | Only SimpleOS can affirm `process_checkpoint` |
| `os/services/container/macos_simpleos_guest_dispatch_v1.spl`, `common/contracts/container/guest_v1.spl`, `doc/04_architecture/macos_simpleos_guest_container.md` | superseded | VM route rejected 2026-09-27; not evidence for any backend here |

### Result

```text
SandboxPolicyV1 -> filesystem_plan_v1 -> PlannedGrantV1[]       shared
contained_lifecycle_v1, attempt_dir_plan_v1, sandbox_canary_v1  shared (extracted from macOS)
capability_report_v1, lifecycle_journal_v1, runtime_v1          shared
                |
  windows: token + label     macos: SBPL profile     simpleos: cspace + namespace view
```

## 10. Docker sibling backend on Windows

Docker is installed on this host (engine 29.10.1), so `providers/windows/docker_*`
with backend `windows-docker-process` can now be exercised. It is installed, not
qualified: `simple_container_adapter_v2.spl` still says `SOURCE-ONLY NOT_RUN`. The two Windows
backends share the contract, share no code below it, and do not replace each other:

| | `simple-pure-process` | `windows-docker-process` |
|---|---|---|
| `isolation_kind` | `native-sandbox` | `native-container` (HCS process isolation) |
| Network / PID namespace | no | yes |
| Needs | nothing installed | Docker service, a Windows base image, engine authority |
| Shared today | `runtime_v1` phases and operation envelope | the same |
| Capability value | `ContainerCapabilityReportV1` | `ContainerHostCapabilityV1` / `RuntimeProbeV1` only; no report yet |

Selection is data, not an OS `if`. The host variation supplies the list of
backends that exist on that OS (Windows: pure, Docker; Linux: pure, Podman OCI;
macOS: pure, Seatbelt, App Sandbox; FreeBSD: pure, jail; SimpleOS: kernel). Each
backend yields a capability report; the Docker leaf needs a small adapter from
its probe to `ContainerCapabilityReportV1` first (part of A1), since it does
not emit one today. The caller's requirement is checked against
each with `container_capability_v1_admission_reason`; the first admitted backend
in the caller's stated preference order runs, and no admitted backend is a
refusal. A workload that requires `native-container` therefore lands on Docker
on Windows and is refused by the pure backend, with no special case. The
selector (`backend_select_v1`, one `@when(os=)` import switch for the candidate
list) is increment 2, lane A1.
