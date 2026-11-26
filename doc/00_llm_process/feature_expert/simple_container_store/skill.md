# Feature expert: Simple Container shared immutable store (increments 1-3)

**Docs:** architecture `doc/04_architecture/platform/container/simple_container_improvement.md`,
design `doc/05_design/platform/container/simple_container_improvement.md`,
plan `doc/03_plan/platform/container/simple_container_improvement.md`.

## Modules
- `std.common.hash.hash_policy_v1` — `hash_policy_v1_digest(policy, bytes)`:
  `xxh3-128` (default), `gxhash-128` (pinned `gxhash-4.0.0-scalar`, in-tree
  pure-Simple port), `blake3-256`, legacy `sha256`. Unknown policy ->
  `status: "unsupported"`; never falls back to another algorithm.
- `std.common.storage.object_record_v1` — SDN `ObjectRecordV1` + digest
  aliases; strict decode, invalid -> `format_version: 0`.
- `std.nogc_sync_mut.storage.immutable_store_v1` — file I/O, so `nogc_sync_mut`.
  Ingest byte-compares on alias hit; collisions get `<algo>_<hex>_c<n>` (n <= 64).
  No-replace publication; `ingest_pinned` ingests and pins atomically w.r.t. GC.
  - Roots: CAS truth is the never-deleted `roots/<name>.g<N>.claim` chain
    (`immutable_store_v1_root_head` reads it); `roots/<name>.sdn` is a cache.
  - Pins are append-only directories: `pins/<id>/owner` and `pins/<id>/refs/<key>`.
  - GC: list-first, then re-check/restore; dry-run default, quarantine, never unlink.
- `std.nogc_sync_mut.storage.storage_view_v1` — host copy-on-write view over the
  store: path policy, quota, volumes, save/load, clone, destroy, lifecycle journal.
- `std.nogc_sync_mut.storage.scv_adapter_v1` — bridges legacy SCV chunks
  (`sha256_<hex>`, identity preserved) into `<repo>/.scv/store`; `pin_reachable`
  writes `scv-gc-<g>-<n>` pins; `scv_adapter_v1_enable` creates the store.
- `std.common.contracts.container.{capability_report_v1, lifecycle_journal_v1}`
  — fail-closed admission (needs `evidence_revision`), pure recovery-action planner.

## SCV opt-in
Nothing creates `.scv/store` by default. Run `scv store-init` in an initialized
repo; afterwards `scv gc` imports and pins reachable chunks (fail closed).

## Testing (Windows host)
Use a Nov-25+ binary, e.g. `C:/dev/keep/seeds/simple-local-20261125.exe test <spec>`.
Specs (test/01_unit/lib/nogc_sync_mut/storage + common): hash_policy 10,
object_record 15, immutable_store 26, scv_adapter 6, storage_view 13 (junction
example is Windows-only via `only_on_windows`), capability_report 10,
lifecycle_journal 11, system 2, plus `scv_gc_store_e2e_spec.spl` (2).

## Not done
Native provider wiring, SimpleOS pager/PMM, VFS enforcement, live memory-limit
updates; SCV write paths are not hooked (chunks import lazily at gc).

## Remaining work
Increment 4 (pure-Simple Windows backend), the Windows Docker process-isolation
lane, Lane D, AppContainer confinement and other-host items are in
`doc/03_plan/platform/container/simple_container_remaining_work.md`
(todo rows 468-475 in `doc/08_tracking/todo/todo_db.sdn`).

## Pure-Simple backend contracts (lane P0)
`std.common.contracts.sosix.containment_v1` (request/limits/support units, fail-closed
`sosix_contain_request_reason_v1`) and `std.common.contracts.container.pure_backend_v1`
(`pure_container_capability_report_v1`: support + measured evidence -> capability report).
Design: `doc/04_architecture/platform/container/pure_simple_container.md` §4.1, §6.

## Windows Docker provider (process isolation) — LIVE evidence 2026-11-26
Provider: `std.nogc_async_mut.container.providers.windows.docker_runtime_v1`
(`WindowsDockerRuntimeProviderV1`), contract `docker_contract_v1`.
- **Live run** (host Windows 10.0.26300, Docker Engine 29.10.1 native, npipe
  `docker_engine`): `prepare -> create -> start -> wait -> logs -> destroy`
  of `cmd /c echo simple-docker-ok` in `nanoserver:ltsc2025`
  (`--isolation=process`): exit 0, logs `simple-docker-ok`, exact-ID absence
  confirmed. Spec: `test/03_system/app/orchestrator/feature/windows_docker_live_process_spec.spl`
  (1 passed, 0 skipped; skips only when `docker.exe` cannot reach the pipe).
- **Pins** (contract consts `WINDOWS_DOCKER_PINNED_*_V1`): image id
  `sha256:b911cb54...4587`, repo digest `...nanoserver@sha256:5c42e42b...35cb`,
  image OsVersion `10.0.26100.33828`, host kernel `10.0 26300 (26100.1...)`.
  `windows_docker_build_pair_reason_v1` accepts equal host/image builds and
  only the 26300/26100 pair; anything else (or unparseable) fails closed.
- **Blocker found**: `_execute` needs the native clean-environment child owner
  (`process_run_bounded_environment_v1`), which refuses interpreter/JIT
  ("requires the matching native C provider"); `windows_command_owner_v2`
  refuses too (canonical-thread guard). Spec runners are interpreted, so the
  live lane never ran. Fix: a non-AOT branch inside `_execute` (native AOT never
  takes it). It is OFF unless `SIMPLE_DOCKER_HOSTED_LIVE=1` (read via SOSIX).
  It refuses when any `DOCKER_*`, `HTTP_PROXY`, `HTTPS_PROXY`, `NO_PROXY` or
  `ALL_PROXY` variable is set (SOSIX `run_bounded` cannot replace the
  environment), and runs `docker.exe --host <pipe> --config <dir>` with a fresh
  owner-only empty config dir (`secure_temp_dir`), removed on every path;
  failed cleanup reports `docker-hosted-config-dir-cleanup-unproven`.
  Limit (`# ponytail:` in code): the launch deadline is rechecked before
  `process_run_bounded`, not after its private slot wait.
- **Gap (named, not filled)**: the full `WindowsSimpleContainerAdapterV2.open`
  cannot run here (needs native boot incarnation; host observation is
  `machine-boot-counter-v1`, interpreter refuses `windows_host_identity_v1`),
  so the run goes through the provider the adapter delegates to.
- `native-build` of a driver with the Nov-25 seed did not finish in 35+ min
  (compiler runs interpreted); do not use it as the live-spec route.
