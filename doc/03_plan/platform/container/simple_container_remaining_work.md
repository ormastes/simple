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
Landed this run on `release/1.0.0`: #12115-#12143 (store hardening, view conflicts, GC quarantine restore, `rt_dir_sync`, root claim compaction, SCV gc per-run owner). Still open, each tracked in `doc/08_tracking/todo/todo_db.sdn`:
- Keep-marked pin tombs (`pin-owner-changed-unrestored`) and `pins/<id>.r<n>` restored pins are not surfaced to their owner or reclaimed (todo 476).
- SCV gc keeps unmarked `scv-gc:` pins forever; ageing them out needs a liveness signal, not a timeout (todo 477).
- DONE (2026-11-28, todo 478 closed): Windows native-build smoke of `dir_sync` links and prints `true` then `false` (root cause: `type Codegen` alias, see `doc/08_tracking/bug/seed_jit_type_alias_captures_same_named_trait_dispatch_2026-11-28.md`).
- Storage view junction TOCTOU between parent walk and open; needs handle-relative opens (todo 479).
- 18 undefined-but-used strict-use imports block flipping `SIMPLE_STRICT_USE` on by default; see `doc/08_tracking/bug/strict_use_default_blocked_by_unprovided_imports_2026-11-27.md` (todo 480).
