# Container fresh route: no workspace bind or TTY through the shared API

- **Status:** FIXED IN SOURCE (2026-11-27), unit-proven; live guest run pending and
  blocked by a separate gap
  (`container_fresh_route_wait_logs_unsupported_2026-11-27.md`)
- **Component:** Simple Container shared API, Linux Podman fresh install route
  (`src/lib/nogc_async_mut/container/api_v2.spl`,
  `src/lib/nogc_sync_mut/container/machine_fresh_workload_record_v2.spl`,
  `src/lib/nogc_async_mut/container/providers/linux/engine_exec_codec_v3.spl`)
- **Found:** 2026-11-27, while writing
  `test/03_system/app/container/feature/podman_shared_api_live_spec.spl`
- **Spec cases affected (kept as real failures, not skipped or pending):**
  "binds the workspace into the container and enforces its read-only half",
  "allocates a TTY for the workload only when tty mode is requested"

## Symptom

A caller that holds the installed fresh owner (`simple_container_open_fresh_v2`)
cannot get a workspace bind or a TTY from `simple_container_apply_v2`.

### 1. Primary workload: build roots and terminal modes refused

API path: `simple_container_apply_v2(owner, "prepare" | "create", ...)` ->
`simple_container_project_v2` -> `LinuxSimpleContainerAdapterV2.validate`
(fresh branch) -> `LinuxFreshWorkloadOwnerV2.project_v2` ->
`machine_fresh_workload_request_v2`.

The route's first profile refuses any leaf with `mounts`, `bundle_path`,
`build_input_root`, `build_output_root`, environment, working directory,
`terminal_mode != "none"`, a user selection, network other than `none` or a
filesystem other than `read-only`. The operation is `rejected` with the exact reason:

```
machine-fresh-workload-profile-unsupported
```

(timeouts above 30000 ms get `machine-fresh-workload-bounds`).

### 2. Secondary exec: TTY refused

API path: `simple_container_exec_begin_v3` (`container/exec_v3.spl`) ->
`LinuxOciEngineExecOwnerV3` -> `engine_exec_request_error_v3`:

```
engine-exec-finite-noninteractive-required
```

The engine inspect check refused `ProcessConfig.tty == true` with
`engine-exec-process-config-mismatch`.

## Root cause

Not a defect in one check. The fresh route is a closed, exact-byte chain and
every link pinned the first profile independently, with no admission input
anywhere:

1. `machine_fresh_workload_request_v2` refused build roots and terminal modes
   unconditionally.
2. `linux_fresh_workload_command_validate_v2` compared the retained request
   against canonical bytes that hard-coded `buildInputRoot: ""`,
   `buildOutputRoot: ""` and no `terminalMode`.
3. `linux_fresh_workload_argv_v2` had no `--tty` or `--mount` projection.
4. `linux_fresh_workload_created_config_validate_v2` required `mounts` and
   `binds` to be empty.
5. The installed fresh-epoch profile had an exact 34-key set, so an
   administrator had nowhere to state an admission.
6. The exec codec hard-coded `"Tty": false` in create and start and refused
   `tty == true` at inspect; the installed exec policy had no terminal field.

## Decision (2026-11-27): option 2, gated by the installed profile

Option 1 (lent workspace + primary attach) was rejected for this gap: it needs
an admin-signed workspace manifest and a different owner
(`simple_container_open_lent_v4`), so the plain fresh owner would still refuse a
caller-supplied build root. It moves the gap to provisioning.

Option 2 was taken, but **not** as an unconditional widening:

- **Refused by default.** A profile without the new keys is the historical
  34-key profile and admits nothing; the reason string
  `machine-fresh-workload-profile-unsupported` is unchanged.
  `machine_fresh_workload_request_v2` keeps its signature and stays refusing.
- **Admission is root-installed DATA.** Two optional keys (both or neither) in
  `/etc/simple/container/fresh-epoch-profile.sdn`:
  - `workloadBuildRootPrefix`: `""` or a canonical absolute path of at least two
    components over `[A-Za-z0-9._-]`, not overlapping `/etc`, `/proc`, `/sys`,
    `/dev`, `/boot`, `/usr`, `/bin`, `/sbin`, `/lib`, `/lib64`, `/root`,
    `/var/lib/simple/container`, the graph root, the run root, or either
    installed executable.
  - `workloadTerminalMode`: `none` or `tty`.
  The profile digest already binds the epoch record, so the admission is bound
  to the epoch identity.
- **Authoritative gate at launch.** `linux_fresh_workload_argv_v2` re-derives
  the admission from the profile the installed owner holds, for every action,
  before any argv exists. A forged record or command cannot reach podman.
- **Audit fields.** `MachineFreshWorkloadRecordV2.admitted_build_root_prefix`
  and `.admitted_terminal_mode` record the admission a workload *used*. They
  are serialized (`admittedBuildRootPrefix`, `admittedTerminalMode`) only when
  non-default, so every first-profile record keeps its bytes and id.
  Record validation re-derives the request under the record's own admission and
  refuses a record whose audit fields are narrower than, or shaped differently
  from, what the request uses. It **cannot** detect a forged *wider* prefix that
  still contains both roots: a pure validator has no installed profile. The
  argv gate is what enforces; the audit field is as honest as the reserve path
  (`MachineFreshWorkloadTransferV2.reserve_v2`), which reads the installed
  profile through the live custody.
- **Narrow shape.** Build roots are a complete, disjoint pair strictly beneath
  the prefix, mounted at the fixed guest paths `/simple-build/inputs` (`ro`) and
  `/simple-build/outputs` (`rw`), both `nosuid,nodev,bind-propagation=rprivate`.
  The path alphabet excludes `,` `=` `:` and space, so a root can never inject a
  `--mount` option. TTY is `--tty` without `--interactive`; `stdin` mode, generic
  `mounts`, environment, cwd and user selection stay refused under every profile.
- **Created-config correspondence.** With build roots the inspected container
  must carry exactly those two binds (source, destination, access, propagation,
  options, one `HostConfig.Binds` entry each); without them any mount is still
  `fresh-workload-unrequested-mount-configuration`.
- **Exec.** `LinuxOciInstalledPolicyV3.exec_terminal_mode` (`execTerminalMode:
  tty`, serialized only when admitting, part of the policy digest) admits a
  finite **detached** TTY exec: `"Tty": true` in create and start, and inspect
  requires `ProcessConfig.tty` to equal the requested mode in both directions.
  `stdin_requested` stays refused. Default reason string unchanged.

### Residual risk, stated

- Build-root admission is **string-level** (prefix + alphabet + overlap), not
  fd-pinned source-object admission. The administrator must make the admitted
  prefix a directory only the service principal can write (the guest wrapper
  creates `/var/lib/simple-host/live-work` 0700, service-owned); a prefix other
  users can write beneath would allow a symlink swap between request and mount.
- The V2 inspect schema has no `Config.Tty` field. TTY correspondence for the
  primary workload rests on the existing exact `create_command` comparison in
  `fresh_workload_created_v2`, not on an independent inspected field.
- `has_workspace` in the fresh projection is now `true` for a build-root
  request; orchestration paths that require `has_workspace == false` will
  refuse such a request, which is the fail-closed direction.
- Not executed anywhere yet (no installed owner on the development host): the
  plumbing from the installed owner through `reserve_v2` to `project_v2`, the
  read-only bind's inspected `Mounts[].Options` / `HostConfig.Binds` shape
  (inferred from the workspace V3 read-write case and Podman 5.2.5's
  `parseMountOptionsForInspect`), and the detached TTY exec against a real
  engine. No step replaces the wrapper's `AUTHOR_WITH_SIMPLE` placeholders, so
  the two new keys exist only in that heredoc.

## Fix (files)

- `src/lib/common/contracts/container/linux_fresh_epoch_v1.spl` — optional keys,
  prefix validation, accessors.
- `src/lib/common/contracts/container/linux_fresh_workload_v2.spl` —
  `LinuxFreshWorkloadAdmissionV2`, feature checks, command fields, mount values,
  canonical-byte comparison.
- `src/lib/nogc_sync_mut/container/machine_fresh_workload_record_v2.spl` —
  `machine_fresh_workload_request_admitted_v2`,
  `machine_fresh_workload_record_admitted_v2`, audit fields.
- `src/lib/nogc_sync_mut/io/linux_fresh_workload_launch_v2.spl` — gate + argv.
- `src/lib/common/contracts/container/linux_fresh_workload_inspect_v2.spl` —
  exact two-bind validation.
- `src/lib/nogc_sync_mut/io/linux_installed_fresh_epoch_owner_v1.spl`,
  `src/lib/nogc_sync_mut/container/machine_authority_v1.spl`,
  `src/lib/nogc_sync_mut/container/machine_fresh_workload_effects_v3.spl`,
  `src/lib/nogc_sync_mut/container/machine_fresh_workload_dispatch_v3.spl`,
  `src/lib/nogc_async_mut/container/providers/linux/fresh_epoch_workload_v2.spl`
  — plumbing from the installed profile to reserve and projection.
- `src/lib/nogc_async_mut/container/providers/linux/{engine_exec_codec_v3,installed_policy_v3,engine_exec_owner_v3,engine_exec_record_v3}.spl`
  — exec TTY admission.
- `scripts/check/check-linux-orchestrator-host-qemu.shs`,
  `test/fixtures/container/podman_live_spec.env` — guest profile keys and the
  admitted work root.

Unit proof: `test/01_unit/lib/container/linux_fresh_workload_admission_v2_spec.spl`
(7 cases) and
`test/01_unit/lib/nogc_async_mut/container/providers/linux/engine_exec_tty_admission_v3_spec.spl`
(5 cases), each covering the admitted case and the default refusal.

## Acceptance

Both spec cases pass in the guest VM with the self-hosted binary, without any
change to the cases themselves.

**Not yet met, and not reachable by this fix alone.** While tracing the route a
second gap was found that the original record missed: the fresh route has no
`wait` or `logs` read, so `live_run_v1` fails after `start` for *every* case,
including the three that carried no known-gap comment. See
`container_fresh_route_wait_logs_unsupported_2026-11-27.md`. The guest profile
skeleton in the QEMU wrapper is also still marked `AUTHOR_WITH_SIMPLE`
(placeholder digests, `overlay`/`systemd` where the decoder requires
`vfs`/`cgroupfs`), so it is not decoder-valid yet either.
