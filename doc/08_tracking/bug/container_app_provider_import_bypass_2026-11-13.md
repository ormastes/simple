# Applications import container provider internals instead of std.container

Status: OPEN — frozen by `scripts/check/check-container-provider-imports.shs`
(baseline `scripts/check/container_provider_imports_baseline.txt`).

Design: `doc/05_design/simple_container_macos_seatbelt.md` §16.2, §16.5.1,
§20 P5. Every application, runner and orchestrator must reach containers only
through the public facade (`std.container` = the existing
`SimpleContainerOwnerV2` in `api_v2.spl`; `std.container.oci`;
`std.container.policy`). The Linux OCI provider must become an internal detail.

## Remaining violations (2026-11-13)

| File | Provider import |
|---|---|
| `src/app/ci/pipeline_runner.spl` | `providers.linux.oci_runtime_v1.{LinuxOciRuntimeProviderV1, LinuxOciRequestV1}` |
| `src/app/build/scheduler/dist_exec_worker.spl` | `providers.linux.oci_exact_logs_v1` |
| `src/app/build/scheduler/worker_capability_observer.spl` | `providers.linux.oci_runtime_v1` |
| `src/app/build/scheduler/worker_cleanup_ack.spl` | `providers.linux.oci_runtime_v1` |
| `src/app/build/scheduler/worker_execute.spl` | `providers.linux.oci_runtime_v1` |

## Why `pipeline_runner.spl` was not migrated in the facade PR

Moving its prepare/create/start/wait/logs/stop/destroy sequence onto
`simple_container_open_v2` + `simple_container_apply_v2/read_v2/control_v2`
today would change behaviour, which the migration must not do. The facade
lacks three things the CI lane relies on:

1. **Ephemeral, uninstalled engine lane.** `LinuxSimpleContainerAdapterV2.open`
   requires installed engine-policy bytes (`linux_oci_engine_policy_decode_v1`:
   pinned executable identity) and a `ContainerHostScopeV2` with
   `native-boot-incarnation-v1` continuity plus physical-host / service-scope /
   native-machine ids and an expected provider identity digest. The CI runner
   resolves `podman`/`docker` from PATH, runs under a per-run temporary journal
   root, and has none of that host-service identity.
2. **Docker on Linux.** The facade's only Linux backend is `linux-podman`
   (`new_with_engine_policy("linux", "podman", ...)`); the CI lane supports an
   explicit `docker` engine. Migrating would silently drop that lane.
3. **Request construction.** The facade takes a `ContainerExecutionRequestV2`
   (plan bytes + request digest + scope); there is no public helper that builds
   one from a portable `PodSpecV1` container without a host-service owner.

Required facade work (owner: Container V2, `api_v2.spl`, work item C1/P5):
a public, explicitly versioned per-run "ephemeral-runner" open path (or a host
service the runner is admitted to) that preserves the CI receipt fields
(`native_id`, `provider_generation`, `operation_id`, runtime-state retention
for recovery, merged cleanup reasons, cancellation via stop/destroy), plus an
exhaustive `linux-docker` backend. Then migrate `pipeline_runner.spl` and the
four build-scheduler workers, delete their baseline lines, and keep
`test/01_unit/app/ci/` receipt specs unchanged.
