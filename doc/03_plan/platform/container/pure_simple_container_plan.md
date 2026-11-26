# Lane plan — pure-Simple container, increment 1 (Windows)

Date: 2026-11-26. Base: `release/1.0.0` @ `38f6249feef`.
Architecture and every signature: `doc/04_architecture/platform/container/pure_simple_container.md`
(§4 SOSIX, §5 rootfs, §7 runtime). Lanes code against those signatures, not
against each other's files. A renamed or reshaped signature is a merge blocker.

## 1. Lanes

Each lane has its own worktree and `work/<topic>` branch, one worker, and owns its
files exclusively. P0 lands first (pure, small). P1, P2 and P3 then run in
parallel. P4 integrates.

| Lane | Owns | Depends on |
|---|---|---|
| S0 extraction | new `src/lib/common/contracts/container/{contained_lifecycle_v1,sandbox_canary_v1}.spl`, new `src/lib/common/container_policy/attempt_dir_plan_v1.spl`; edits to `providers/macos/{seatbelt_provider_v1,seatbelt_capabilities_v1}.spl`, `common/contracts/container/sandbox_capability_v1.spl` and `common/container_policy/sandbox_policy_decode_v1.spl`; three specs | none |
| P0 contract | `src/lib/common/contracts/sosix/containment_v1.spl`, `src/lib/common/contracts/container/pure_backend_v1.spl`, their two specs | none |
| P1 Windows identity + write grant | `src/lib/nogc_sync_mut/sosix/windows/{security_abi_v1,restricted_identity_v1,contained_write_v1}.spl`, `src/lib/nogc_sync_mut/sosix/contained_write_v1.spl`, two specs | P0 |
| P2 contained launch | `src/lib/nogc_sync_mut/io/windows_process_owner.spl` (edit), `src/lib/nogc_sync_mut/io/windows_process_owner_abi.spl` (edit), `src/lib/nogc_sync_mut/sosix/containment_v1.spl`, `src/lib/nogc_sync_mut/sosix/{windows,linux,freebsd,macos,simpleos}/containment_v1.spl`, every `src/lib/nogc_sync_mut/sosix/**/FILE.md` edit (P1's entries included), one spec, fixtures | P0; P1 merged before the `restricted` examples run |
| P3 rootfs | `src/lib/nogc_sync_mut/sosix/readonly_share_v1.spl`, `src/lib/nogc_sync_mut/storage/rootfs_materialize_v1.spl`, `src/lib/nogc_sync_mut/storage/storage_view_v1.spl` (add one fn), `src/lib/nogc_sync_mut/storage/immutable_store_v1.spl` (add one fn), two specs | P0 |
| P4 runtime | `src/lib/nogc_sync_mut/container/pure_runtime_v1.spl`, `src/lib/common/contracts/container/pure_sandbox_observed_v1.spl`, system spec, fixture, generated spec mirror | S0 and P0–P3 merged; inc-3 lane E landed for a true `memory_hard_limit` |

S0 runs in parallel with P0–P3; only P4 imports its modules. S0 does not change
any P0 file, name or signature. No lane edits `api_v2.spl`, `service_v2.spl`,
`capability_report_v1.spl`, or (S0 excepted) `providers/**`.

## 2. Lane detail

Run specs with `C:/dev/keep/seeds/simple-local-20261125.exe test <spec>`. Every
Windows example returns early unless `is_windows()`; a skipped example is not
evidence, so the acceptance lines below are measured on this host.

### S0 — extract shared code from the macOS leaf (pure; move, not copy)

Architecture §9 names what moves and why.

```simple
# std.common.contracts.container.contained_lifecycle_v1
pub const CONTAINED_STATE_VALIDATED_V1 = "validated"   # ... all ten states, same text values
pub fn contained_lifecycle_next_v1(state: text, event: text) -> Result<text, text>   # Err("invalid-transition-<state>-<event>")
pub fn contained_runtime_phase_v1(state: text) -> text

# std.common.container_policy.attempt_dir_plan_v1
pub unit ContainerAttemptNumberV1: i64
pub struct ContainerAttemptDirPlanV1:   # the ten fields of SeatbeltAttemptDirPlanV1
pub fn container_attempt_key_v1(workload_uid: text, attempt: ContainerAttemptNumberV1) -> Result<text, text>
pub fn container_attempt_dir_plan_v1(state_root: text, attempt_key: text) -> Result<ContainerAttemptDirPlanV1, text>

# std.common.contracts.container.sandbox_canary_v1
pub struct SandboxCanaryPlanV1:      # id, expected, requirement
pub struct SandboxCanaryResultV1:    # id, observed, evidence_digest
pub struct SandboxCanaryStatusV1:    # status, missing, reason
pub fn sandbox_canary_status_v1(plan: [SandboxCanaryPlanV1],
        results: [SandboxCanaryResultV1]) -> SandboxCanaryStatusV1
```

- The Seatbelt functions become forwards. `seatbelt_lifecycle_next_v1` maps the
  error to its existing `seatbelt-invalid-transition-` text.
  `seatbelt_attempt_dir_plan_v1` keeps the `SCMAC-*` prefixes, the path check and
  the Darwin 103-byte socket check. `seatbelt_capability_status_v1` keeps its
  manifest identity checks and calls `sandbox_canary_status_v1` for the canary
  comparison. `SEATBELT_*` constants alias the new ones.
- `sandbox_capability_v1.spl`: add `SANDBOX_BACKEND_SIMPLE_PURE_V1 =
  "simple-pure-process"`; add it to the backend choice list at
  `sandbox_policy_decode_v1.spl:284` (the only hard check).
- `container_attempt_dir_plan_v1` does not call `seatbelt_path_check_v1` (that
  requires a leading `/`). It applies the host-independent checks listed in
  architecture §9; the Seatbelt forward runs its own check first.
- Specs: `test/01_unit/lib/common/contracts/container/contained_lifecycle_v1_spec.spl`,
  `test/01_unit/lib/common/contracts/container/sandbox_canary_v1_spec.spl`,
  `test/01_unit/lib/common/container_policy/attempt_dir_plan_v1_spec.spl`.
- Acceptance: the existing specs under
  `test/01_unit/lib/nogc_async_mut/container/providers/macos/` pass unmodified
  (they are pure, so they run on Windows); no state-machine, dir-plan or
  canary-compare body remains in the two macOS files (grep in review).

### P0 — contract (pure)

- `containment_v1.spl`: architecture §4.1 verbatim.
- `pure_backend_v1.spl`:

```simple
pub const PURE_CONTAINER_BACKEND_V1 = "simple-pure-process"
pub const PURE_CONTAINER_ENGINE_V1 = "simple-pure-container-v1"
pub const PURE_CONTAINER_ROOT_VIEW_SPLIT_V1 = "hardlink-lower-split-upper"

pub struct PureContainerEvidenceV1:
    host_os: text
    host_arch: text
    guest_abi: text
    root_view_kind: text
    memory_cap_enforced: ContainerCapabilityFlagV1   # measured verdict only
    base_fully_linked: ContainerCapabilityFlagV1
    launch_observed: ContainerCapabilityFlagV1
    cleanup_observed: ContainerCapabilityFlagV1
    evidence_revision: text

pub fn pure_container_capability_report_v1(support: SosixContainSupportV1,
        evidence: PureContainerEvidenceV1) -> ContainerCapabilityReportV1
```

  Mapping is architecture §6. `isolation_kind` is `native-container` only when
  write, read, network, PID and root-remap support are all true; otherwise
  `native-sandbox`. `memory_hard_limit` = `support.memory_hard_limit.value and
  evidence.memory_cap_enforced.value`.
- Specs: `test/01_unit/lib/common/contracts/sosix/containment_v1_spec.spl`,
  `test/01_unit/lib/common/contracts/container/pure_backend_v1_spec.spl`.
- Changed 2026-11-26 after P0 started: §4.1 gained one reason,
  `containment-readonly-requires-restricted`, checked second (right after
  `containment-request-invalid`): non-empty `readonly_dirs` with `identity`
  other than `restricted`. No type, field or file name changed.
- Acceptance: each refusal reason in §4.1 has one example, in the stated order;
  a Windows-shaped support with empty `evidence_revision` fails
  `capability-evidence-missing` against a constrained requirement; a
  `native-container` requirement fails `isolation-kind-mismatch`; a
  `filesystem_confinement` requirement fails `filesystem-confinement-missing`.

### P1 — Windows identity and write grant

- Signatures: architecture §4.3 and §4.4. `security_abi_v1.spl` declares the
  advapi32 externs for both target widths, in the style of
  `windows_process_owner_abi.spl`, and reuses that module's heap and pointer
  helpers. Reuse `OpenProcessToken` and `GetTokenInformation` where already
  declared (`windows_local_process_principal_v1`, `windows_machine_policy_abi_v1`).
- The facade `sosix/contained_write_v1.spl` is one import switch: Windows binds
  `sosix_windows_grant_low_write_v1`; every other OS returns `""`.
- Specs: `test/01_unit/lib/nogc_sync_mut/sosix/restricted_identity_v1_spec.spl`,
  `test/01_unit/lib/nogc_sync_mut/sosix/contained_write_v1_spec.spl`.
- First step: an extern-resolution smoke under the seed binary. If advapi32
  externs do not resolve there, stop and report; do not add C.
- Acceptance: token opens, integrity read-back is low, close returns true and a
  second close returns false; grant on an empty directory returns `""` and the
  label reads back low; grant on a directory holding one file returns
  `grant-target-not-empty`; grant on a missing path is refused.

### P2 — contained launch

- Owner edit, one internal core and no second create sequence:

```simple
struct WindowsProcessContainExtrasV1:
    token: i64                  # 0 = caller token, CreateProcessW
    active_process_limit: i64   # 0 = none
    cpu_rate: i64               # 0 = none; 1..10000

fn windows_process_admit_contained_v1(request: WindowsProcessRequestV1,
        memory_limit_bytes: i64, extras: WindowsProcessContainExtrasV1) -> WindowsProcessAdmissionV1
```

  `windows_process_admit_with_reserve_v1` forwards with zero extras; its
  behaviour and the readback checks stay byte-for-byte equivalent.
- `sosix/windows/containment_v1.spl` maps the §4.2 API onto that core, the
  existing poll/cancel/collect, `windows_process_peak_memory_v1` and P1's token.
  `support` is the Windows column of §4.2.
- `sosix/{linux,freebsd,macos,simpleos}/containment_v1.spl`: `support` =
  `sosix_contain_support_none_v1("<os>-unimplemented")`; `start` returns
  `RejectedBeforeStart("containment-unimplemented-<os>")`; poll/cancel/collect
  return `Err`. No silent success.
- Spec: `test/01_unit/lib/nogc_sync_mut/sosix/containment_v1_spec.spl`.
  Fixtures: `test/fixtures/container/contain_spawn_n.spl` (starts N children that
  sleep), `test/fixtures/container/contain_write_probe.spl` (tries to write a
  given path, prints the outcome).
- Acceptance: exit code and stdout file of a trivial child are returned;
  `network: "none"` is `RejectedBeforeStart` and no process was created;
  a process limit of 2 makes the third spawn fail; cancel yields `tree_empty`
  with children running; under `restricted` the write probe fails on a
  medium-label file and succeeds in a granted directory; existing
  `windows_process_owner` specs still pass. CPU rate is set-and-read-back only;
  throughput is not measured in this increment.

### P3 — read-only link and rootfs

- `sosix/readonly_share_v1.spl`: §4.4, portable body over
  `file_hardlink`, `file_seal_readonly`, and a bounded copy.
- Added functions:

```simple
# immutable_store_v1
pub struct StoreLinkV1:
    status: text    # "linked" | "copied" | "missing" | "rejected"
    reason: text
pub fn immutable_store_v1_link_object(root: text, object_key: text, destination: text,
        allow_copy: StoreFlagV1) -> StoreLinkV1

# storage_view_v1
pub struct ViewBaseEntriesV1:
    status: text    # "ok" | "rejected"
    reason: text
    paths: [text]
    keys: [text]    # same length and order as paths
pub fn storage_view_v1_base_entries(view: StorageViewV1) -> ViewBaseEntriesV1

# rootfs_materialize_v1
pub struct RootfsMaterializeV1:
    status: text    # "ok" | "rejected"
    reason: text
    lower_dir: text
    upper_dir: text
    linked: ViewCountV1
    copied: ViewCountV1
pub fn rootfs_materialize_v1(view: StorageViewV1, allow_copy: ViewFlagV1) -> RootfsMaterializeV1
pub fn rootfs_dematerialize_v1(view: StorageViewV1) -> text   # "" = lower removed, pin released
```

  Pin before link, owner `pure-container`, pin id = view id. A failure part-way
  removes the partial `lower/` and releases the pin.
- Specs: `test/01_unit/lib/nogc_sync_mut/sosix/readonly_share_v1_spec.spl`,
  `test/01_unit/lib/nogc_sync_mut/storage/rootfs_materialize_v1_spec.spl`.
- Acceptance: two views of one base both report `linked` and their `lower/`
  files read identical bytes; bytes survive `immutable_store_v1_collect` after
  dematerialize of the other view; a destination that exists is `rejected`;
  `allow_copy` false with an unlinkable source is `rejected`, true is `copied`
  and counted; existing `storage_view_v1_spec` and `immutable_store_v1_spec`
  still pass.

### P4 — runtime

- `pure_runtime_v1.spl`: architecture §7. It uses S0's lifecycle and attempt-dir
  modules and `filesystem_plan_v1` grants, and defines none of its own.
- `pure_sandbox_observed_v1.spl`:
  `pub fn pure_container_observed_capability_v1(support: SosixContainSupportV1,
  evidence: PureContainerEvidenceV1) -> SandboxObservedCapabilityV1`.
  Field mapping is the table in architecture §7.
  Qualified only from `sandbox_canary_status_v1` over the Windows canaries
  (base-file write denied, granted-dir write allowed, process limit hit,
  descendants gone after cancel).
- Spec: `test/03_system/app/container/feature/pure_simple_container_v1_spec.spl`,
  fixture `test/fixtures/container/pure_probe.spl`, mirror under `doc/06_spec/`.
- Acceptance: a run over a two-file base exits 0, reads a `lower/` file, writes
  an `upper/` file, fails to overwrite the `lower/` file, and leaves no view
  directory and no pin; `network: "none"` returns `rejected` with no view
  created; a requirement for `native-container` returns `rejected` with
  `isolation-kind-mismatch`; the journal ends `destroyed`. Without lane E merged
  the report's `memory_hard_limit` is false and a requirement for it is refused.

## 3. Gate for every lane

- Specs above green on this Windows host, plus the existing specs of every
  edited file.
- `sh scripts/check/check-primitive-api-added.shs --changed <base>..HEAD` and
  `sh scripts/check/check-text-len-unit-mix.shs --changed <base>..HEAD` pass.
- No `extern`, `@when`, or `io.windows_*` import outside `sosix/**` and the two
  edited `io/` owner files (grep in review).
- A function a lane cannot finish is `fail("unimplemented: <name>")`.
- Fable review before the PR; land by PR to `release/1.0.0`.

## 4. Increment 2 (not scheduled)

Each replaces exactly one stub or adds one file, so they stay disjoint.
N1–N3 cannot run here: source plus Fable/Opus review only, no capability claim.

| Lane | Files | Check |
|---|---|---|
| N1 Linux | `sosix/linux/containment_v1.spl` | review-only |
| N2 FreeBSD | `sosix/freebsd/containment_v1.spl` | review-only |
| N3 macOS | `sosix/macos/containment_v1.spl` over `sosix/darwin_sandbox_v1` and `seatbelt_profile_v1` | review-only |
| N4 SimpleOS | `sosix/simpleos/containment_v1.spl` over `os/sosix/process_launch_provider_v1` and `os/services/container/runtime_provider_v1`; maps `ResourceDomain` `mem`/`pids` and names the other fields as gaps | QEMU real-firmware lane, then board |
| W2 AppContainer | `sosix/windows/app_container_v1.spl`, identity `app-sandbox` | Windows: read and network denial measured |
| A1 selection + API wiring | `backend_select_v1.spl` (pure or Docker on Windows by capability admission, architecture §10), Docker probe -> `ContainerCapabilityReportV1` adapter, `api_v2.spl` owner case, async adapter | Windows, both backends live |
| R2 report v2 | `capability_report_v2.spl` with `network_isolation`, `pid_isolation` | pure |

Host mapping for N1–N3 is the table in architecture §4.2.

## 5. Evidence rule

Windows claims need a run log from this host. A stub host reports nothing.
Review-only lanes never set `launch_qualified` or a non-empty `evidence_revision`.

## 6. Owner questions, with recommended defaults

Each default is what the lanes assume. Default, owner may override.

1. Is a job-contained host process reporting `native-sandbox` accepted on
   Windows beside Docker/HCS? **Default: yes.** It is a sibling backend with a
   weaker, honestly reported kind. Docker stays the `native-container` route
   and neither replaces the other (architecture §10).
2. Restricted low-integrity token first, AppContainer later? **Default: yes.**
   Increment 1 confines writes only; W2 adds read and network denial.
3. Split `lower/` + `upper/` with no union? **Default: yes** for increment 1. A
   union needs bindflt/HCS, which is the Docker backend's job.
4. Is one `@when(os=)` import switch in the level-0 facade the intended
   selection form? **Default: yes.** It is the form already used in
   `machine_authority_cleanup_v1.spl`, and it adds no resolver.
5. Network and PID isolation as explicit report fields? **Default: not in
   increment 1.** `isolation_kind` plus the SOSIX refusal is fail-closed today.
   R2 adds the fields when a caller needs to require one without the other.

## Resume state (2026-11-26, after host reboot)

- Done: shared-vs-per-host review (architecture §9), extraction lane S0, Docker
  sibling note (architecture §10), defaults for §6.
- Open: no Fable review of these two docs yet; review, fix, then push and land.
- Related lanes outside this plan: Lane C landed (#11901); remaining-work docs
  landed (#11909); Lane E (`work/container-inc3-win-memcap-20261126`) needs its
  round-3 re-review, then push and land.
