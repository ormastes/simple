# Pure-Simple container runtime

Date: 2026-11-26. Baseline: `release/1.0.0` @ `38f6249feef`.
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
   No new resolver. The level-0 facade holds exactly one
   `@when(os="windows"): ... @elif(os="linux"): ... @end` import switch (the same
   form `nogc_sync_mut/container/machine_authority_cleanup_v1.spl` uses) and
   nothing else host-specific. These are the first code files in the `sosix/<os>/`
   skeleton, so the switch form is an owner question (plan §6).
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
| `src/lib/nogc_sync_mut/sosix/windows/contained_write_v1.spl` | N | Windows body: low mandatory label on a directory |
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
| `src/lib/common/contracts/container/sandbox_capability_v1.spl` | E | Admit backend id `simple-pure-process` beside `macos-seatbelt-process` |

Reused as is: `capability_report_v1`, `lifecycle_journal_v1`, `runtime_v1`
(phases and `RuntimeOperationV1`), `storage_view_v1` create/save/load/destroy,
`immutable_store_v1` pins and GC, `io/file_ops.{file_hardlink, file_seal_readonly}`,
the whole suspended-create/job/kill-on-close/stdio/poll/cancel/collect sequence in
`windows_process_owner`, `sosix/darwin_sandbox_v1`, `providers/macos/seatbelt_profile_v1`,
and (once landed) lane E's `windows_memory_cap_probe_v1` as the only source of the
Windows `memory_hard_limit` verdict.

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
    write_confinement: SosixContainFlagV1
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
`containment-request-invalid`, `containment-memory-limit-unsupported`,
`containment-process-limit-unsupported`, `containment-cpu-rate-unsupported`,
`containment-write-confinement-unsupported` (identity `restricted` or any
`readonly_dirs`), `containment-network-isolation-unsupported` (network `none`),
`containment-pid-isolation-unsupported`, `containment-root-remap-unsupported`.
A wall deadline with `kill_all_descendants` false is
`containment-deadline-unsupported`.

### 4.2 Launch — `std.nogc_sync_mut.sosix.containment_v1`

```simple
pub fn sosix_contain_support_v1() -> SosixContainSupportV1
pub fn sosix_contain_start_v1(request: SosixContainRequestV1) -> SosixContainAdmissionV1
pub fn sosix_contain_poll_v1(lease: SosixContainLeaseV1) -> Result<SosixContainPollV1, text>
pub fn sosix_contain_cancel_v1(lease: SosixContainLeaseV1) -> Result<SosixContainFlagV1, text>
pub fn sosix_contain_collect_v1(lease: SosixContainLeaseV1) -> Result<SosixContainPollV1, text>
```

`start` calls `sosix_contain_request_reason_v1` against its own `support` first.

| Axis | Windows (increment 1) | Linux | FreeBSD | macOS |
|---|---|---|---|---|
| Owner reused | `io/windows_process_owner` | `io/linux_process_owner`, `linux_process_replace_*` | new jail owner | `sosix/darwin_sandbox_v1`, `seatbelt_profile_v1` |
| Memory | Job `JOB_OBJECT_LIMIT_JOB_MEMORY` (commit) | cgroup v2 `memory.max` | `rctl jail:<n>:memoryuse:deny` | none aggregate (`RLIMIT_AS` is per process) -> unsupported |
| Process count | Job `ActiveProcessLimit` | `pids.max` | `rctl maxproc:deny` | `RLIMIT_NPROC` is per UID -> unsupported |
| CPU rate | `JobObjectCpuRateControlInformation` hard cap | `cpu.max` | `rctl pcpu:deny` | none (`RLIMIT_CPU` is CPU seconds) -> unsupported |
| Kill descendants | `KILL_ON_JOB_CLOSE`, no breakaway | `cgroup.kill` | `jail_remove` | process group only -> false |
| Write confinement | restricted token at low integrity | mount namespace, read-only bind | jail path + `nullfs -o ro` | Seatbelt `deny file-write*` |
| Read confinement | no (AppContainer, increment 2) | `pivot_root` | jail path | Seatbelt `deny file-read*` allowlist |
| Network | no | `CLONE_NEWNET` | jail without `ip4`/`ip6` or `vnet` | Seatbelt `deny network*` |
| PID isolation | no | `CLONE_NEWPID` | jail | no |
| Root remap | no | `pivot_root` | jail `path` | no |
| Unprivileged | yes | yes if user namespaces and cgroup delegation are available | no (root or delegated broker) | yes |
| `memory_accounting` | `job-commit` | `cgroup` | `jail-rss` | `` |

Windows launch sequence, all inside the existing admit core: validate and pin the
executable -> create job -> set extended limits (`KILL_ON_JOB_CLOSE | JOB_MEMORY |
ACTIVE_PROCESS`) and CPU rate, read each back -> open restricted token ->
`CreateProcessAsUserW` suspended with an explicit handle list and the given
environment block -> assign to job -> resume. A restricted copy of the caller's
own primary token needs no privilege. Any failure after create terminates the job
and returns `FailedAfterCleanup` or `Unknown`, never `RejectedBeforeStart`.

### 4.3 Windows identity — `std.nogc_sync_mut.sosix.windows.restricted_identity_v1`

Windows-only (no facade; only `sosix/windows/containment_v1` imports it).

```simple
pub unit SosixWindowsTokenV1: i64
pub fn sosix_windows_restricted_token_open_v1() -> Result<SosixWindowsTokenV1, text>
pub fn sosix_windows_restricted_token_close_v1(token: SosixWindowsTokenV1) -> SosixContainFlagV1
```

`OpenProcessToken` -> `CreateRestrictedToken(DISABLE_MAX_PRIVILEGE)` ->
`SetTokenInformation(TokenIntegrityLevel, S-1-16-4096)`. Reads back the integrity
level; a mismatch closes the token and returns `Err`.

### 4.4 Read-only sharing and write grant

```simple
# std.nogc_sync_mut.sosix.readonly_share_v1
pub struct SosixFsShareV1:
    status: text    # "linked" | "copied" | "rejected"
    reason: text

pub fn sosix_fs_link_readonly_v1(source: text, destination: text,
        allow_copy: SosixContainFlagV1) -> SosixFsShareV1

# std.nogc_sync_mut.sosix.contained_write_v1
pub fn sosix_fs_grant_contained_write_v1(empty_dir: text) -> text   # "" = granted

# std.nogc_sync_mut.sosix.windows.contained_write_v1 (body behind the facade)
pub fn sosix_windows_grant_low_write_v1(empty_dir: text) -> text
```

| Op | Windows | Linux / FreeBSD / macOS |
|---|---|---|
| `link_readonly` | `file_hardlink` (`CreateHardLinkW`, already in `io/file_ops`). `file_seal_readonly` answers false on Windows by design and is not required: the object keeps its medium integrity label, so a low-integrity child cannot open it for write | `file_hardlink` + `file_seal_readonly` (0444); the launch variant adds the read-only mount or Seatbelt rule |
| `grant_contained_write` | Low mandatory label `(OI)(CI)` on the directory via `SetNamedSecurityInfoW` | returns `""`; the launch variant makes `writable_dirs` writable |

`link_readonly` has one portable body: it links, then seals where the host can
seal, and it never branches on the OS. It returns `copied` only when `allow_copy.value` and the link failed
(cross-volume, link-count limit, filesystem without hard links); otherwise
`rejected`. `grant_contained_write` refuses a non-empty directory
(`grant-target-not-empty`). That check is load-bearing: a hard link shares one
security descriptor across all its names, so labelling a tree that contains links
would make store objects writable by every container.

## 5. Windows rootfs

`storage_view_v1` is a byte API over a private manifest; it has no directory a
process can use. `rootfs_materialize_v1` adds one, with no union filesystem:

```text
<view_root>/<view_id>/
  upper/     existing view upper; low label; child cwd, TEMP and all writes
  lower/     hardlinks to <store>/objects/<xx>/<key>.obj; medium label; read-only to the child
```

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
   `private_pids`, `root_dir` and read confinement before any child exists.
2. Admission: `pure_container_capability_report_v1` builds the report from
   `SosixContainSupportV1` plus measured evidence. On Windows:

| Report field | Value | Source |
|---|---|---|
| `isolation_kind` | `native-sandbox` | a `native-container` requirement fails `isolation-kind-mismatch` |
| `client_authority` | `user` | `support.unprivileged` |
| `filesystem_confinement` | false | needs read and write confinement together |
| `memory_accounting` | `job-commit` | `support.memory_accounting` |
| `memory_hard_limit` | true only with lane E's `Enforced` verdict | never from `support` alone |
| `memory_limit_update`, `memory_reclaim`, `durable_recovery`, `process_checkpoint`, `explicit_shared_memory` | false | not implemented |
| `readonly_file_backing_reuse` | true only if every base file was `linked` | materializer result |
| `ephemeral_cleanup` | true only if `tree_empty` and view destroy were both observed | runtime evidence |
| `filesystem_save_load` | true | `storage_view_v1` |
| `launch_qualified` | true only after a real contained launch returned its exit code on this host | runtime evidence |
| `evidence_revision` | non-empty only when evidence was measured | empty makes any constrained requirement fail `capability-evidence-missing` |

A v2 report with explicit `network_isolation` and `pid_isolation` fields is a
named gap, not part of this design (plan §6).

## 7. Runtime

```simple
# std.nogc_sync_mut.container.pure_runtime_v1
pub struct PureContainerSpecV1:
    container_id: text
    store: text
    view_root: text
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
    extra_grants: [PlannedGrantV1]     # shared filesystem_plan_v1 grants beyond lower/upper

pub struct PureContainerRunV1:
    status: text                       # "exited" | "rejected" | "cleanup-unproven"
    reason: text
    exit_code: SosixContainExitCodeV1
    peak_memory: SosixContainBytesV1
    report: ContainerCapabilityReportV1
    journal: ContainerLifecycleJournalV1

pub fn pure_container_run_v1(spec: PureContainerSpecV1) -> PureContainerRunV1
```

Order: build report -> `container_capability_v1_admission_reason` -> journal
`created` -> `storage_view_v1_create` -> materialize `lower/` -> grant `upper/` ->
journal `starting` -> `sosix_contain_start_v1` -> poll to terminal -> collect ->
journal `stopped` -> remove `lower/`, release pin, `storage_view_v1_destroy` ->
journal `destroyed`. Every failure after `created` walks the journal's cleanup
actions; `Unknown` admission returns `cleanup-unproven` and keeps the journal.

The runtime owns no private state machine, directory layout or grant model:

- phase changes go through `contained_lifecycle_next_v1` (the machine the macOS
  Seatbelt leaf already uses) and are projected to `runtime_v1` phases;
- `upper/` is laid out by `container_attempt_dir_plan_v1` (`home`, `tmp`,
  `output`, `workspace`), and `USERPROFILE`/`TEMP`/`HOME`/`TMPDIR` point there;
- `extra_grants` are `PlannedGrantV1` values from `filesystem_plan_v1`. A grant
  with `Write` becomes a `writable_dirs` entry, any other a `readonly_dirs`
  entry. Overlap with a protected root is already refused by that planner;
- when the caller holds a `SandboxPolicyV1`, admission also runs the shared
  `sandbox_requirements_match_v1` against
  `pure_container_observed_capability_v1(support, evidence)`.

Async wiring into `api_v2.spl` and a `SimpleContainerOwnerV2` case is increment 2.

## 8. Risks

- New advapi32 externs under the seed interpreter. Lane E proved kernel32 job
  externs resolve there; `windows_process_owner.spl` records one extern that did
  not. Each Windows lane starts with an extern-resolution smoke.
- Low integrity breaks programs that write outside `upper/` (profile, registry
  `HKCU`). The runtime sets `TEMP`, `TMP`, `USERPROFILE`, `APPDATA` and
  `LOCALAPPDATA` under `upper/`.
- CPU rate control conflicts with a parent job that already sets it; `start`
  reads the setting back and refuses on mismatch.
- `storage_view_v1` open items (junction swap between walk and open, stale handle
  after destroy) apply unchanged to `lower/` creation.

## 9. Shared vs per-host

Reviewed: `providers/macos/**`, `common/container_policy/**`, the portable
contracts under `common/contracts/container/`, `src/os/services/container/**`,
`src/os/kernel/loader/container_namespace.spl`, `src/os/kernel/ipc/cspace_spawn.spl`,
`src/os/kernel/scheduler/cspace_delegation.spl`, `src/os/sosix/process_launch_provider_v1.spl`.
"Shared" means one module that the Windows, macOS and SimpleOS routes all call.
Code moves; it is never copied. Extraction is lane S0 in the plan.

### Already host-neutral: reuse unchanged

| File | Verdict | Reason |
|---|---|---|
| `common/contracts/container/filesystem_policy_v1.spl` | shared | Its model is "access isolation over real host paths, not namespace virtualization", which is the Windows restricted-token model |
| `common/container_policy/filesystem_plan_v1.spl` | shared | Pure grant/deny planner; `canonical_path_within_v1` already takes `case_insensitive`, as NTFS needs |
| `common/container_policy/requirements_match_v1.spl`, `diagnostics_v1.spl` | shared | Policy-vs-observed admission with stable diagnostics |
| `common/contracts/container/sandbox_capability_v1.spl` | shared, one edit | `SandboxObservedCapabilityV1` and `SandboxPolicyV1` are portable, but only the Seatbelt backend id is named. S0 adds `simple-pure-process`. The `SCMAC-*` codes and the `simple-container-seatbelt-policy-v1` schema id stay, because renaming breaks stored policies |
| `common/container_policy/sandbox_policy_decode_v1.spl`, `endpoint_network_decode_v1.spl` | shared | Strict SDN decoders; no host call |
| `common/contracts/container/{capability_report_v1,lifecycle_journal_v1,runtime_v1,host_capability_v1}.spl` | shared | Already used by every leaf |
| `common/oci/bundle_check_v1.spl` | shared | SimpleOS `oci_import` already delegates to it |
| `common/storage/object_record_v1.spl`, `common/hash/hash_policy_v1.spl` | shared | Object identity for the hosted store and the SimpleOS layer store |

### macOS

| File | Verdict | Reason |
|---|---|---|
| `seatbelt_provider_v1.spl`: `seatbelt_lifecycle_next_v1`, `seatbelt_runtime_phase_v1`, state constants | extract to `contained_lifecycle_v1.spl` | Nothing in the machine is Darwin-specific. The Seatbelt names stay as forwards that keep the `seatbelt-` error prefix |
| `seatbelt_provider_v1.spl`: `SeatbeltAttemptDirPlanV1`, `seatbelt_attempt_key_v1`, `seatbelt_attempt_dir_plan_v1` | extract to `attempt_dir_plan_v1.spl` | Layout and key rules are neutral. The Darwin `sun_path` 103-byte check stays in the Seatbelt forward |
| `seatbelt_provider_v1.spl`: `MacOsSeatbeltAdapterV1`, launch plan, attempt policy | per-host | Seatbelt effect ordering and SBPL grants |
| `seatbelt_capabilities_v1.spl`: canary plan/result types, expected-vs-observed status | extract to `sandbox_canary_v1.spl` | "Qualified only when every planned canary has a recorded native result" is the rule Windows needs too |
| `seatbelt_capabilities_v1.spl`: the fixed Seatbelt canary list, manifest, probe transcript parser | per-host | Darwin build, helper digest and profile digest are Seatbelt facts |
| `seatbelt_profile_v1.spl` | per-host | SBPL emitter. It is the macOS counterpart of the Windows token + label step; both consume the same `PlannedGrantV1` list |
| `executable_preflight_v1.spl` | per-host | Mach-O. A Windows PE preflight would be its sibling behind the same `RuntimeValidationV1` |
| `native_admission_v1.spl`, `native_sandbox_provider_v1.spl` | per-host | Signed App Sandbox helper route, a different engine (`macos-native-sandbox-v1`) |
| `worker_protocol_v1.spl` | per-host for now | The HMAC frame protocol is neutral, but the pure backend launches in-process and has no worker. Extract when a second consumer exists |
| `sosix/darwin_sandbox_v1.spl` | per-host | Becomes the body the `sosix/macos/containment_v1.spl` variant calls (lane N3) |

### SimpleOS

| File | Verdict | Reason |
|---|---|---|
| `os/services/container/runtime_provider_v1.spl`, `container_runtime.spl` | per-host | Scheduler-task launch with a kernel-supplied context. They become the body of the `sosix/simpleos/containment_v1.spl` variant (lane N4) |
| `os/sosix/process_launch_provider_v1.spl` | per-host | Existing SimpleOS SOSIX launch adapter; N4 composes it |
| `os/services/container/container_manager.spl` | per-host | Userland ECS policy owner. Its `ResourceDomain {cpu, mem, io, pids}` is the same quantity set as `SosixContainLimitsV1`; N4 converts at the variant boundary, with no second limits type |
| `os/kernel/loader/container_namespace.spl` | per-host; duplicate logic removed in N4 | Kernel enforcement stays MDSOC-only. `container_view_allows_path` is a second path-prefix test beside `canonical_path_within_v1`; N4 makes it call the shared function after confirming identical boundary behaviour |
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
with backend `windows-docker-process` is a runnable sibling. The two Windows
backends share the contract, share no code below it, and do not replace each other:

| | `simple-pure-process` | `windows-docker-process` |
|---|---|---|
| `isolation_kind` | `native-sandbox` | `native-container` (HCS process isolation) |
| Network / PID namespace | no | yes |
| Needs | nothing installed | Docker service, a Windows base image, engine authority |
| Shared contract | `ContainerCapabilityReportV1`, `ContainerCapabilityRequirementV1`, `runtime_v1` phases, `lifecycle_journal_v1` | the same |

Selection is data, not an OS `if`. The host variation supplies the list of
backends that exist on that OS (Windows: pure, Docker; Linux: pure, Podman OCI;
macOS: pure, Seatbelt, App Sandbox; FreeBSD: pure, jail; SimpleOS: kernel). Each
backend yields a capability report. The caller's requirement is checked against
each with `container_capability_v1_admission_reason`; the first admitted backend
in the caller's stated preference order runs, and no admitted backend is a
refusal. A workload that requires `native-container` therefore lands on Docker
on Windows and is refused by the pure backend, with no special case. The
selector (`backend_select_v1`, one `@when(os=)` import switch for the candidate
list) is increment 2, lane A1.
