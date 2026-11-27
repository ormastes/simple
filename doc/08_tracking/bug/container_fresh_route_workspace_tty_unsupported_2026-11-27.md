# Container fresh route: no workspace bind or TTY through the shared API

- **Status:** OPEN (2026-11-27)
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
`machine_fresh_workload_request_v2`
(`machine_fresh_workload_record_v2.spl:47-54`).

The route's first profile refuses any leaf with `mounts`, `bundle_path`,
`build_input_root`, `build_output_root`, environment, working directory,
`terminal_mode != "none"`, a user selection, network other than `none` or a
filesystem other than `read-only`. The operation is `rejected` with the exact reason:

```
machine-fresh-workload-profile-unsupported
```

(timeouts above 30000 ms get `machine-fresh-workload-bounds`). The seed
confirmed the reason on a `network_policy: "host"` leaf. Build roots and
`terminal_mode: "tty"` reach the same condition.

### 2. Secondary exec: TTY refused

API path: `simple_container_exec_begin_v3` (`container/exec_v3.spl`) ->
`LinuxOciEngineExecOwnerV3` -> `engine_exec_request_error_v3`
(`engine_exec_codec_v3.spl:35`):

```
engine-exec-finite-noninteractive-required
```

This happens for any `terminal_mode != "none"` or `stdin_requested`. The
contract itself (`common/contracts/container/exec_v3.spl:161`) accepts `"tty"`,
and the engine inspect check (`engine_exec_codec_v3.spl:153`) refuses
`ProcessConfig.tty == true` with `engine-exec-process-config-mismatch`. Exec also
needs an issued `ContainerExecInstalledV3` + `ContainerExecAdmissionV3`. No spec
can fabricate those.

## Options found

1. **Use the typed workspace and primary-attach lanes that already exist.**
   - Workspace: `simple_container_open_lent_v4` (admission plus native
     service-identity borrow), then `simple_container_take_workspace_root_v3` and
     `simple_container_enable_workspace_v3` (`container/workspace_api_v3.spl`).
     This path needs an admin-signed workspace manifest and invocation digest.
   - TTY: `primary_attach_v1` / `terminal_primary_v2` on a workspace workload.
   - Cost: the live spec would need an operator-provisioned manifest and
     admission fixture. The gap moves to "provisioning", not "API".
2. **Widen the fresh route's first profile.** Admit
   `build_input_root` / `build_output_root` (and `terminal_mode: "tty"`) in
   `machine_fresh_workload_request_v2`, backed by the same native source-object
   admission the provider demands for mounts (`linux-mount-native-admission-not-installed`
   today). Make the exec leaf accept `tty` end to end (request check and engine
   inspect check) once the interactive attach transport exists.
   - Cost: security review of the host-object admission. This is an owner
     decision.

## Acceptance

Both spec cases pass in the guest VM, run as root with the self-hosted binary,
without any change to the cases themselves.
