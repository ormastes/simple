# Lane plan — pure-Simple container, increment 1 (Windows)

Date: 2026-11-26. Base: `release/1.0.0` @ `790371966e6`.
Architecture and every signature: `doc/04_architecture/platform/container/pure_simple_container.md`
(§4 SOSIX, §5 rootfs, §7 runtime). Lanes code against those signatures, not
against each other's files. A renamed or reshaped signature is a merge blocker.

## 1. Lanes

Each lane has its own worktree and `work/<topic>` branch, one worker, and owns its
files exclusively. P0 lands first (pure, small). S0, P1 and P3 then run in
parallel. P2 is serial after P1 (it imports P1's token module). P4 integrates.

| Lane | Owns | Depends on |
|---|---|---|
| S0 extraction | new `src/lib/common/contracts/container/{contained_lifecycle_v1,sandbox_canary_v1}.spl`, new `src/lib/common/container_policy/attempt_dir_plan_v1.spl`; edits to `providers/macos/{seatbelt_provider_v1,seatbelt_capabilities_v1}.spl` only; three specs | none |
| P0 contract | `src/lib/common/contracts/sosix/containment_v1.spl`, `src/lib/common/contracts/container/pure_backend_v1.spl`, `src/lib/common/contracts/container/backend_identity_v1.spl` (add the backend and engine ids), their specs | none |
| P1 Windows identity + write grant | `src/lib/nogc_sync_mut/sosix/windows/{security_abi_v1,restricted_identity_v1,contained_write_v1}.spl`, `src/lib/nogc_sync_mut/sosix/contained_write_v1.spl`, `src/lib/nogc_sync_mut/sosix/{linux,freebsd,macos,simpleos}/contained_write_v1.spl` (refusals), two specs | P0 |
| P2 contained launch | `src/lib/nogc_sync_mut/io/windows_process_owner.spl` (edit), `src/lib/nogc_sync_mut/io/windows_process_owner_abi.spl` (edit), `src/lib/nogc_sync_mut/sosix/containment_v1.spl`, `src/lib/nogc_sync_mut/sosix/{windows,linux,freebsd,macos,simpleos}/containment_v1.spl`, the one-line import-switch exception in `doc/04_architecture/platform/platform_variant_directory_rule.md`, one spec, fixtures | P0; serial after P1 merged |
| P3 rootfs | `src/lib/nogc_sync_mut/sosix/readonly_share_v1.spl`, `src/lib/nogc_sync_mut/storage/rootfs_materialize_v1.spl`, `src/lib/nogc_sync_mut/storage/storage_view_v1.spl` (add one fn), `src/lib/nogc_sync_mut/storage/immutable_store_v1.spl` (add one fn), two specs | P0 |
| P4 runtime | `src/lib/nogc_sync_mut/container/pure_runtime_v1.spl`, `src/lib/common/contracts/container/pure_sandbox_observed_v1.spl`, system spec, fixture, generated spec mirror | S0 and P0–P3 merged. Also owns the edit of `io/windows_memory_cap_probe_v1.spl` and its spec (remove the duplicate builder) |

Every lane adds the `FILE.md` entries for its own new files in the governed
`sosix/**` directories, in the same commit (disjoint lines), so the
workspace-root guard (WRG003) passes per lane.

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
- ~~`sandbox_capability_v1.spl`: add~~ `SANDBOX_BACKEND_SIMPLE_PURE_V1 =
  "simple-pure-process"`: WITHDRAWN. S0 does not edit
  `sandbox_capability_v1.spl` or `sandbox_policy_decode_v1.spl`. The backend id
  lives only in `backend_identity_v1.spl` (P0), and the decoder plus its schema
  SDN pin the Seatbelt backend together (architecture §9).
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
- Changed 2026-11-26 (review round 3), exact delta against round 2:
  - `SosixContainCanaryV1` gains `control: text` (last field).
  - `SosixContainQualifyRequestV1` gains `probe_script: text` after `probe_digest`.
  - Three more ids: `SOSIX_CONTAIN_CANARY_LAUNCH_EXIT_V1 = "launch-exit-code"`,
    `SOSIX_CONTAIN_CANARY_TREE_EMPTY_V1 = "tree-empty-after-cancel"`,
    `SOSIX_CONTAIN_CANARY_PROCESS_LIMIT_V1 = "process-limit-spawn"` (nine total).
  - New `sosix_contain_canary_pass_v1(result: SosixContainQualifyResultV1,
    id: text) -> SosixContainFlagV1`; `sosix_contain_canaries_pass_v1` now
    requires all nine, and a deny canary needs `control == "allow"`.
  - `PureContainerEvidenceV1` gains `roots_digest: text` before
    `evidence_revision`.
  - New in `pure_backend_v1.spl`, the only producer of evidence fields:

```simple
pub fn pure_container_evidence_from_qualify_v1(qualify: SosixContainQualifyResultV1,
        memory_enforced: ContainerCapabilityFlagV1, memory_digest: text,
        host_os: text, host_arch: text, guest_abi: text, root_view_kind: text,
        roots_digest: text) -> PureContainerEvidenceV1
```

    Field mapping is the table in architecture §7. `base_fully_linked` is false
    here. `evidence_revision` = `pure:` + sha256 of `qualify.evidence_digest`,
    `memory_digest` and `roots_digest`; it is `pure:unaffirmed` when
    `qualify.evidence_digest` is empty.
  - Acceptance adds: a deny canary with `control` other than `allow` fails; each
    evidence field follows only its listed canaries.
- Changed 2026-11-26 (review round 2), all in P0's two files:
  `containment_v1.spl` adds `SosixContainCanaryV1`,
  `SosixContainQualifyRequestV1`, `SosixContainQualifyResultV1`, the six
  `SOSIX_CONTAIN_CANARY_*_V1` ids and `sosix_contain_canaries_pass_v1`
  (architecture §4.1). `PureContainerEvidenceV1` gains
  `write_confinement_observed: ContainerCapabilityFlagV1` after
  `memory_cap_enforced`. The report mapping is unchanged
  (`filesystem_confinement` stays false without read confinement). Acceptance
  adds: canaries pass only when all six ids are present once with
  observed == expected; a missing, duplicated or `not-run` canary fails.
- Changed 2026-11-26 (review round): `SosixContainRequestV1` gains
  `scope: text` after `identity`; `restricted` with an empty or non-identifier
  `scope` is `containment-request-invalid`. `PURE_CONTAINER_BACKEND_V1` and
  `PURE_CONTAINER_ENGINE_V1` alias new constants in `backend_identity_v1.spl`
  (`CONTAINER_BACKEND_SIMPLE_PURE_PROCESS_V1`,
  `CONTAINER_ENGINE_SIMPLE_PURE_CONTAINER_V1`), which P0 adds with their enum
  cases.
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
- Changed 2026-11-26 (review round 2): new
  `sosix_fs_grant_contained_read_v1(tree: text) -> text` in the same facade and
  in all five variant files (non-Windows: `contained-read-unimplemented-<os>`).
  Token: restricting SIDs are {Everyone, Users, logon SID, fixed reader SID,
  scope SID}, and the token default DACL is {scope SID, user, SYSTEM}. Write
  grant also refuses `grant-target-world-writable`. No existing signature
  changed in this round.
- Round 3, behaviour only: the world-writable refusal also covers the caller's
  logon SID; the read-grant walk skips reparse points and never touches their
  targets; the reader ACE is permanent (architecture §4.4).
  `check-platform-variant-dirs.shs` matches only `@cfg(`, so P1's `@when(os=)`
  facade lands without waiting for P2's rule exception.
- First step is now a restricted-launch smoke: start a trivial child with the
  token (plain `CreateProcessAsUserW`, no job) and see exit code 0, not
  `0xC0000142`. If it cannot be made to start, stop and report.
- Changed 2026-11-26 (review round), three signatures:
  `sosix_windows_restricted_token_open_v1(scope: text)`; new
  `sosix_windows_scope_sid_v1(scope: text) -> Result<text, text>`;
  `sosix_fs_grant_contained_write_v1(empty_dir: text, scope: text)`. The Windows
  body is no longer named `sosix_windows_grant_low_write_v1`: every variant file
  exports the one name `sosix_fs_grant_contained_write_v1`.
- The facade `sosix/contained_write_v1.spl` is one import switch over the five
  variant files. Non-Windows variants return
  `contained-write-unimplemented-<os>`, never `""`.
- The token carries restricting SIDs {Everyone, Users, scope SID}; the grant adds
  the low label and an inheritable modify ACE for the scope SID (architecture
  §4.3). If restricting SIDs cannot be made to work under the seed, stop and
  report; do not fall back to label-only.
- Specs: `test/01_unit/lib/nogc_sync_mut/sosix/restricted_identity_v1_spec.spl`,
  `test/01_unit/lib/nogc_sync_mut/sosix/contained_write_v1_spec.spl`.
- First step: an extern-resolution smoke under the seed binary. If advapi32
  externs do not resolve there, stop and report; do not add C.
- Acceptance: token opens, integrity read-back is low and the restricted-SID
  list reads back with the scope SID, close returns true and a second close
  returns false; two scopes give two different SIDs and one scope always the
  same; the smoke child exits 0; read grant on a tree with a user-only ACL
  adds exactly one reader ACE per object and is idempotent; grant on a
  directory where Users can already write returns `grant-target-world-writable`;
  grant on an empty directory returns `""` and the label reads back low; grant on a directory holding one file returns
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
  `support` is the Windows column of §4.2. It also implements
  `sosix_contain_memory_cap_evidence_v1` over lane E's probe and verdict
  (not over `windows_container_capability_report_v1`), the
  `containment-volume-no-acl` refusal, and `sosix_contain_qualify_v1`
  (architecture §4.2/§4.3; the other four variants return
  `containment-qualify-unimplemented-<os>`). `start` does not consult canaries.
  P2 also owns the probe `src/lib/nogc_sync_mut/sosix/contain_canary_probe.spl`,
  the constant `SOSIX_CONTAIN_CANARY_PROBE_SHA256_V1` in the facade, and a spec
  example that the constant equals the file's sha256. Qualify does the setup
  itself: user-only DACL forced on the linked file, a live second-scope
  process, explicit security descriptor on root processes.
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
  with children running; `sosix_contain_qualify_v1` returns the nine canaries
  of architecture §4.3 passing, each deny with `control: "allow"`; an altered
  probe script gives `containment-qualify-probe-digest-mismatch` and no canary; memory evidence is `enforced`
  with the fixture lane E measured; existing
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

  `ViewFlagV1`, `ViewCountV1`, `ViewBytesV1` and `StoreFlagV1` are declared
  without `pub`; P3 owns both files and makes them `pub` (names unchanged) so
  these public signatures and P4's spec type are legal.
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

- `pure_runtime_v1.spl`: architecture §7, including `pure_container_qualify_v1`
  and the evidence-first order. It uses S0's lifecycle and attempt-dir
  modules and `filesystem_plan_v1` grants, and defines none of its own.
- `pure_sandbox_observed_v1.spl`:
  `pub fn pure_container_observed_capability_v1(support: SosixContainSupportV1,
  evidence: PureContainerEvidenceV1) -> SandboxObservedCapabilityV1`.
  Field mapping is the table in architecture §7. `qualification` comes from
  `sosix_contain_canaries_pass_v1`. P4 runs no canaries of its own and sets no
  evidence field: `pure_container_qualify_v1` only calls the two SOSIX ops and
  `pure_container_evidence_from_qualify_v1`.
- Spec: `test/03_system/app/container/feature/pure_simple_container_v1_spec.spl`,
  fixture `test/fixtures/container/pure_probe.spl`, mirror under `doc/06_spec/`.
- Acceptance: a run over a two-file base exits 0, reads a `lower/` file, writes
  an `upper/` file, fails to overwrite the `lower/` file, and leaves no view
  directory and no pin; `network: "none"` returns `rejected` with no view
  created; a `restricted` run with evidence lacking
  `write_confinement_observed` returns `write-confinement-unqualified`;
  evidence produced for other roots returns `evidence-roots-mismatch`; a
  `lower/` read works with the store under `%TEMP%`; with qualify evidence a requirement for `native-container` returns
  `rejected` with `isolation-kind-mismatch`, and with empty evidence the same
  requirement returns `capability-evidence-missing`; the journal ends
  `destroyed`; `windows_container_capability_report_v1` no longer exists and the
  lane E spec passes on the single builder.

## 3. Gate for every lane

- Specs above green on this Windows host, plus the existing specs of every
  edited file.
- `sh scripts/check/check-primitive-api-added.shs --changed <base>..HEAD` and
  `sh scripts/check/check-text-len-unit-mix.shs --changed <base>..HEAD` pass.
- No `extern`, `@when`, or `io.windows_*` import outside `sosix/**` and the two
  edited `io/` owner files (grep in review).
- A function a lane cannot finish is `fail("unimplemented: <name>")`.
- Every lane adds its new `.spl` paths to `src/lib/source_inventory.lock` in the
  same commit (one sorted line each). Lines are disjoint across lanes; the merge
  owner resolves any adjacency conflict by keeping both.
- Fable review before the PR; land by PR to `release/1.0.0`.

## 4. Increment 2 (not scheduled)

Each replaces exactly one stub or adds one file, so they stay disjoint.
N1–N3 cannot run here: source plus Fable/Opus review only, no capability claim.

| Lane | Files | Check |
|---|---|---|
| N1 Linux | `sosix/linux/containment_v1.spl` | review-only |
| N2 FreeBSD | none in SOSIX: bind the existing `providers/freebsd/jail_runtime_v1.spl` into A1's selection; no new jail owner | review-only |
| N3 macOS | move pure `seatbelt_profile_v1` to `common/container_policy/` and `nogc_async_mut/sosix/darwin_sandbox_v1.spl` to `nogc_sync_mut/sosix/macos/darwin_sandbox_v1.spl` (forwards left), then `sosix/macos/containment_v1.spl` over it | review-only |
| N4 SimpleOS | body in `src/os/sosix/` over `process_launch_provider_v1` and `os/services/container/runtime_provider_v1` (lib SOSIX never imports `src/os`); maps `ResourceDomain` `mem`/`pids` and names the other fields as gaps | QEMU real-firmware lane, then board |
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
4. How is the host variant bound? **Resolved (owner, final):** one `@when(os=)`
   import switch per facade, no body, no resolver lane. P2 adds the one-line
   exception to the directory rule.
5. Network and PID isolation as explicit report fields? **Default: not in
   increment 1.** `isolation_kind` plus the SOSIX refusal is fail-closed today.
   R2 adds the fields when a caller needs to require one without the other.

## Status (2026-11-26)

- Design reviewed by Fable over four rounds; final verdict LAND.
- Landed: S0 shared extraction (#11924), seed advapi32/token/SID/ACL externs
  for P1 (#11925; specs needing them run on a seed built from that commit),
  inc-3 lane E memory cap (#11914).
- In flight: P0 contract, P1 identity + grants, P3 rootfs, Windows Docker
  live lane. P2 and P4 start after P0/P1/P3 land.
