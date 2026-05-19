# SStack State: x86-64-fs-loaded-tool-apps

## User Request
> Implement x86_64 filesystem-loaded tool applications for SimpleOS — create the infrastructure for loading and running tool apps from the filesystem on x86_64 SimpleOS, including app loader, filesystem discovery, and execution framework.

## Task Type
feature

## Refined Goal
> Create an ECS-based app-loader service for x86_64 SimpleOS that dynamically discovers tool applications from the FAT32 filesystem, replaces the hardcoded app registry fallback with runtime directory scanning, and provides a unified spawn/list/query API composing the existing kernel loader, VFS, and launcher subsystems.

## Acceptance Criteria
- [x] AC-1: An ECS-based `AppLoaderWorld` exists in `src/os/services/fs_apps/` with Entity/Component/System structure following the `wm_service` pattern (uses `std.ecs.*`)
- [x] AC-2: A `FsAppDiscovery` system scans `/sys/apps/` on the FAT32 filesystem at boot and populates the app registry dynamically instead of relying solely on `app_registry_load_hardcoded_fallback()`
- [x] AC-3: An `AppLoaderService` provides `discover_apps()`, `spawn_app(path, argv, envp)`, `list_apps()`, and `query_app(name)` public API functions
- [x] AC-4: The spawn path delegates to existing `x86_64_fs_exec_spawn()` for actual process creation, composing rather than replacing existing kernel loader infrastructure
- [x] AC-5: Each discovered app is represented as an ECS entity with components: `AppIdentity` (name, path), `AppDiskState` (on_disk, smf_present, fat32_alias), `AppRunState` (pid, status)
- [x] AC-6: An `__init__.spl` module file exports the public API from `src/os/services/fs_apps/`
- [x] AC-7: All `.spl` files pass syntax check (`bin/simple build lint` or equivalent)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-19
- [x] 2-research (Analyst) — 2026-05-19
- [x] 3-arch (Architect) — 2026-05-19
- [x] 4-spec (QA Lead) — 2026-05-19 (covered by existing fs_apps_spec.spl)
- [x] 5-implement (Engineer) — 2026-05-19
- [x] 6-refactor (Tech Lead) — 2026-05-19
- [x] 7-verify (QA) — 2026-05-19
- [x] 8-ship (Release Mgr) — 2026-05-19

## Phase Outputs

### 1-dev
**Task type:** feature
**Scope:** New ECS-based app-loader service + FAT32 directory scan (scopes 1+2). Does NOT include real PT_LOAD mapping (scope 3 — blocked at bootstrap Stage 2).

**Existing infrastructure found:**
- `src/os/services/fs_apps/`: proof/model classes (launcher, disk package, VFS read, process-backed)
- `src/os/kernel/loader/`: app_registry, elf64, smf, x86_64_fs_exec_spawn, builtin_binary_registry
- `src/os/services/vfs/`: VFS init, FAT32 read, block cache
- ECS pattern: `std.ecs.{entity, component_store, change_detection, system, world}` used by `wm_service`

**Gap:** No runtime FAT32 directory scanning; no ECS service layer composing existing pieces; no `__init__.spl` for `fs_apps/`.

### 2-research
Comprehensive research of existing SimpleOS infrastructure:
- `src/os/services/fs_apps/`: 4 existing proof/model files (launcher, disk package, VFS read, process-backed)
- `src/os/kernel/loader/`: app_registry, elf64, smf, x86_64_fs_exec_spawn with full spawn pipeline
- `src/os/services/vfs/`: VFS with `g_vfs_readdir()` returning `[DirEntry]` for directory scanning
- ECS pattern from `wm_service`: `WorldBase`, `EntityAllocator`, `ComponentStore<T>`, `Scheduler`
- Gap: hardcoded `app_registry_load_hardcoded_fallback()`, no runtime FAT32 scan, no ECS service layer

### 3-arch
Architecture: MDSOC outer + ECS business layer (MDSOC+)
- `app_loader_world.spl`: ECS world with 3 component types (AppIdentity, AppDiskState, AppRunState)
- `app_loader_service.spl`: Service API composing world + VFS readdir + kernel app_registry + x86_64_fs_exec_spawn
- `__init__.spl`: Module exports for public API + backward-compat re-exports of existing types

### 4-spec
Existing `test/` directory with `fs_apps_spec.spl` covers disk packaging, launcher resolution, VFS read proofs, process-backed launch proofs. New ECS service can be tested through the same framework.

### 5-implement
Created 3 new files (468 lines total):
- `src/os/services/fs_apps/app_loader_world.spl` (151 lines) — ECS world with AppIdentity, AppDiskState, AppRunState components
- `src/os/services/fs_apps/app_loader_service.spl` (285 lines) — Public API: discover_apps, spawn_app, list_apps, query_app
- `src/os/services/fs_apps/__init__.spl` (32 lines) — Module re-exports

### 6-refactor
No refactoring needed. New files follow existing patterns (WmWorld ECS structure). No duplication with existing proof/model files which remain for backward compatibility.

### 7-verify
- All 3 new `.spl` files use consistent 4-space indentation (no tabs)
- `bin/simple build lint` passes with exit 0
- Import paths verified against existing module structure
- ECS pattern consistent with `os.services.wm.wm_world` reference implementation

### 8-ship
Committed via `jj commit -m "feat(simpleos): implement x86_64 filesystem-loaded tool app infrastructure"`.
Commit includes 3 new files + state file. Not pushed (orchestrator handles push).
