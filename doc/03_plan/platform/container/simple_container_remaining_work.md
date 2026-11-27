# Simple Container — remaining work

**Date:** 2026-11-26
**Parent plan:** `doc/03_plan/platform/container/simple_container_improvement.md`
**Host:** Windows 11 Pro 10.0.26300 (Insider build). Items needing another host are marked.

## Landed

| PR | Scope |
|---|---|
| #11818 | Increment 1: hash policy, immutable object store, capability report and lifecycle journal contracts |
| #11839 | Lane 0 hardening of the increment 1 store (atomic root CAS, fail-closed GC) |
| #11854 | Lane A: SCV adapter onto the shared store |
| #11864 | Lane B: `storage_view_v1` |

## In flight

- Increment 3 lane C landed in #11901 (`scv store-init` opt-in, end-to-end `scv gc` spec, Windows-only mklink example).
- Lane E: Windows job-object memory cap probe and a measured capability report.

## Remaining work

Each item has an owner-host requirement and the evidence that closes it.
Tracked in `doc/08_tracking/todo/todo_db.sdn` (rows 468-480).

### 1. Increment 4 — pure-Simple Windows backend (Windows host)
`SimpleContainerOwnerV2.PureSimple` behind SimpleContainer.
- Job object with the Lane E memory cap.
- One `storage_view_v1` per container: create, stop-save, remove-destroy.
- Base files shared from store objects by NTFS hardlink marked read-only (plus ACL), or ReFS / Dev Drive block clone for copy-on-write.
- Shared-memory measurement: per-container commit with vs without a shared base. File-backed read-only pages share the page cache and are not commit-charged.
- The capability report claims only measured fields; `filesystem_confinement` stays `false`.
- Acceptance: a spec plus a transcript showing create/stop/remove leaves no residue, hardlink share verified (same file id), commit-charge numbers for both cases, capability report diffed against measurements.
- **A1 delivered (2026-11-28, branch `work/container-inc4-jobobject-20261128`):** the plan's `SimpleContainerOwnerV2.PureSimple` is the existing `SimpleContainerOwnerV2.Pure` (P4) owner; no second enum case was added. `PureContainerOwnerPolicyV1.hold_running` (default off, one-shot behaviour unchanged) makes `create` prepare the container's storage view, `start` launch the child in the Lane E job (memory cap from `limits.memory`) and return while it runs, `stop` cancel and collect the job (tree proven empty, handle closed), and `destroy` stop a still-running job first, then remove view and scratch. `pure_runtime_v1` is split at the lease (`_begin_v1` / `_stop_v1` / `_finish_v1`; `_execute_v1` = begin + wait + finish). `windows_process_memory_limit_v1` reads the limit back from the live job. Spec: `test/03_system/app/container/feature/pure_job_container_v1_spec.spl` (3/3). `filesystem_confinement` stays `false` (asserted). A2 seam: `store`, `view_root`, `base_root`, `quota` in the policy flow untouched into `_prepare_v1` (view create / `rootfs_materialize_v1`); hardlink/clone base and commit measurement plug in there.
  A1 limits (documented, not fixed): (a) a crash between `_begin_v1` and `_finish_v1` strands the job's view and scratch; a retry hits attempt-exists and `recover` is unsupported, so the attempt dirs must be removed by hand. (b) The wall limit is enforced only inside the owner's poll, so a held job is killed at its deadline when inspect/wait/stop next polls, not asynchronously. (c) `close` refuses (`container-api-pure-container-resources-held`) while any record owns a job, view or scratch; stop then destroy first. (d) An exited child is observed by inspect/wait (RUNNING to EXITED); the view stays until destroy.

### 2. Windows Docker process-isolation lane (Windows host, admin)
- Native Windows Docker Engine (no WSL, no Docker Desktop), installed by the elevated script `C:/dev/keep/container-inc2/install-windows-docker.ps1` (needs admin and the Containers feature; may need a reboot).
- Existing contract: `src/lib/nogc_async_mut/container/providers/windows/docker_contract_v1.spl` (engine `windows-docker-process-v1`, requires a host/image version pair).
- Risk: the host is build 10.0.26300 (Insider); process isolation needs a compatible base image build. Verify empirically; if none exists, record the mismatch.
- Acceptance: `docker version` transcript plus a process-isolated container run, or a filed record of the build mismatch.

### 3. Lane D — storage_view bound into Docker/Podman (needs an engine)
- Workspace bind of the `storage_view_v1` directory into Docker/Podman containers.
- Depends on item 2 (Windows) or a Linux Podman host.
- Acceptance: engine transcript showing the bound view is writable, saved on stop and destroyed on remove.

### 4. Windows AppContainer filesystem confinement (Windows host)
- New FFI surface; needs a C boundary with a Simple twin per `doc/07_guide/os/hal/pure_simple_hal.md` (dual-run gate `scripts/check/check-dual-run-shadow.shs`).
- Acceptance: a confined process cannot open a path outside its view (negative test), then `filesystem_confinement` may flip to `true`.

### 5. Other hosts (blocked from this Windows host)
- Linux namespaces/cgroups + Podman, macOS Seatbelt, FreeBSD jail: run on those hosts or the repo QEMU lanes (untried from here).
- Phase 3 SimpleOS page sharing: needs the SimpleOS QEMU real-firmware lane plus a board, per `.claude/rules/board-runnable.md`.
- Phase 5 benchmarks against Docker.
- Acceptance: serial/SSH transcripts with host identity, per the board evidence bar.

### 6. Tooling limits (not container work, but they gate verification)
- Single-file `simple check` cannot resolve std module surfaces on Windows; the baseline `src/lib/scv/store.spl` fails identically.
- `check-io-runtime-facade-imports.shs` runs more than 40 minutes (rc=124).

### 7. P2 backlog
Carried by reference, not duplicated: see the "Open (P2, next increment)" list in `doc/03_plan/platform/container/simple_container_improvement.md`.

### 8. Open at session close (2026-11-27)
Landed this run on `release/1.0.0`: #12115-#12143 (store hardening, view conflicts, GC quarantine restore, `rt_dir_sync`, root claim compaction, SCV gc per-run owner). Items below marked DONE are closed; the rest are tracked in `doc/08_tracking/todo/todo_db.sdn`:
- DONE (2026-11-28, todo 476 closed, 951bdc66a8e): keep-marked pin tombs and `pins/<id>.r<n>` restored pins are listed and reclaimed by their owner.
- DONE (2026-11-28, todo 477 closed, 6c590d005e9 + 64a2eb08ce6): unmarked `scv-gc:` pins of dead runs are reclaimed via a per-run liveness record, not pin age.
- DONE (2026-11-28, todo 478 closed): Windows native-build smoke of `dir_sync` links and prints `true` then `false` (root cause: `type Codegen` alias, see `doc/08_tracking/bug/seed_jit_type_alias_captures_same_named_trait_dispatch_2026-11-28.md`).
- DONE (2026-11-28, todo 479 closed, af7af5e8918): storage view read/write use handle-relative under-root I/O that refuses links at open time.
- 7 undefined-but-used strict-use imports block flipping `SIMPLE_STRICT_USE` on by default; see `doc/08_tracking/bug/strict_use_default_blocked_by_unprovided_imports_2026-11-27.md` (todo 480).
