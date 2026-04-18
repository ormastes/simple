# SStack State: spostgre-nvfs-storage

## User Request
> Build a good filesystem and a PostgreSQL-like DB ("spostgre") for Simple. Research+plan
> spostgre first; then plan the filesystem; then build spostgre and during that work
> file feature requests back against the filesystem. Use MDSOC+ architecture but follow
> the module naming from the attached NVMe-aware storage plan (SimpleFS-NV / NVFS,
> SimpleDB-style page+WAL, arenas, storage classes, SLLM immutable bundles).

## Refined Goal
> Deliver the research, plans, and an MDSOC+ skeleton for:
>   1. **spostgre** — PostgreSQL-like DB engine on Simple with NVMe-aware physical layout
>      (out-of-place page updates, page-indirection map, WAL arena, temp arena, BRIN-style
>      summaries, HOT-like updates), MDSOC outer + ECS business layer.
>   2. **NVFS** (SimpleFS-NV) — hybrid copy-on-write metadata + append-band data filesystem
>      with virtual storage classes (META_DURABLE, DB_WAL, DB_TEMP, MODEL_IMMUTABLE,
>      GENERAL_MUTABLE, CHECKPOINT_SNAPSHOT), arena_* API, capability-probed ZNS/FDP paths,
>      MDSOC outer + ECS business layer.
>   3. A **FS-feature-request backlog** mechanism so building spostgre produces concrete,
>      trackable asks against NVFS (stored in `doc/08_tracking/feature_request/`).
>
> Research spostgre FIRST, plan NVFS SECOND, then iterate implementation of spostgre
> while emitting NVFS feature requests.

## Acceptance Criteria
- [ ] AC-1: Research report for spostgre at `doc/01_research/spostgre_research.md` covering PostgreSQL 18 storage internals (pages, WAL, HOT, FSM/VM, BRIN, AIO), out-of-place page designs, Aurora Optimized Reads, WiscKey, NVMe-aware DB research (SSD-iq, X-FTL, SaS), and Simple-specific constraints (MDSOC+, nogc_sync_mut / nogc_async_mut module placement).
- [ ] AC-2: spostgre design plan at `doc/05_design/spostgre_design.md` — MDSOC+ module layout (`src/lib/nogc_sync_mut/spostgre/` + ECS business slice), on-disk layout (rel.main, rel.pmap, rel.vmap, rel.fmap, rel.wal, rel.temp, rel.blob), storage API, WAL protocol, recovery, phased milestones.
- [ ] AC-3: NVFS design plan at `doc/05_design/nvfs_design.md` — MDSOC+ module layout (`src/lib/nogc_sync_mut/nvfs/` + ECS business slice), virtual storage classes, arena_* API, superblock/checkpoint ring/intent log, capability-probe table, ZNS/FDP optional paths.
- [ ] AC-4: FS feature-request backlog at `doc/08_tracking/feature_request/nvfs_requests.md` with template + at least the initial requests discovered while drafting the spostgre plan.
- [ ] AC-5: Skeleton code split as: main-repo common traits at `src/lib/nogc_sync_mut/storage/` + NVFS trait contracts at `src/lib/nogc_sync_mut/fs/nvfs/`; spostgre engine + CLI in submodule `examples/spostgre/` (symlinked into `src/app/spostgre/` per trace32 pattern); NVFS impl in submodule `examples/nvfs/`. Compiles (passes `bin/simple build lint`). No TODO-as-NOTE downgrades.
- [ ] AC-6: All artifacts respect CLAUDE.md rules — `.spl`/`.shs` only (no Python/Bash), composition not inheritance, MDSOC+ default, jj VCS (no branches), `<>` generics.
- [ ] AC-7: A cross-reference in `doc/04_architecture/mdsoc_architecture_tobe.md` (or adjacent) linking to the new NVFS and spostgre plans under the MDSOC+ userland section.
- [ ] AC-8: Upfront NVFS design contribution from spostgre at `doc/05_design/nvfs/from_spostgre.md` (per `feedback_svllm_drives_nvfs_design.md` memory note — produce fs-level design contributions alongside engine work, not after). FR backlog is a secondary channel for discoveries during Phase 5 only.
- [ ] AC-9: Both private GH repos created (`ormastes/simple-spostgre`, `ormastes/simple-nvfs`), added as git submodules at `examples/spostgre/` and `examples/nvfs/`, each with an initial scaffold commit pushed to `main`.

## Cooperative Providers
- Codex: available
- Gemini: available (but Phase 2 is text research — Gemini stays unused until Phase 3 if UI surfaces)

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-04-17
- [x] 0-bootstrap (Submodule + GH repo bootstrap) — 2026-04-18
- [ ] 2-research (Analyst)
- [ ] 3-arch (Architect — spostgre design + NVFS design + upfront fs contribution)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 0-bootstrap
**Done 2026-04-18.**

Created two private GitHub repos:
- `ormastes/simple-spostgre` — initial commit `7826e4f` ("chore: initial scaffold"). URL: https://github.com/ormastes/simple-spostgre
- `ormastes/simple-nvfs` — initial commit `3e054f0` ("chore: initial scaffold"). URL: https://github.com/ormastes/simple-nvfs

Both scaffolds contain only `README.md`, `LICENSE` (UNLICENSED placeholder), `.gitignore`, and empty `src/`, `doc/`, `test/`, `.github/workflows/` directories (directories not tracked until files land in Phase 5).

Added both as git submodules in the main Simple repo:
- `examples/spostgre` → `ormastes/simple-spostgre` @ main
- `examples/nvfs` → `ormastes/simple-nvfs` @ main

`.gitmodules` updated (9 entries total; 2 new). Local gitlinks point at the initial scaffold commits.

**Commit deferred** to Phase 8 (ship). A parallel agent is concurrently authoring svllm design docs in the same working copy; committing here without path-scoped splitting would clobber their work. Phase 8 will split and commit this feature's paths in isolation.

Lock incident: after the spostgre submodule add completed, `.git/index.lock` was left stale (no holding process — verified via `lsof`, `fuser`, `pgrep`). Removed and proceeded.

### 1-dev
Task type: **feature** (multi-module: DB engine + filesystem + tracking infra).
Categorized as a staged research+design+skeleton deliverable, NOT a full implementation
of either storage stack — those are many-month efforts and outside a single SStack pass.

The pipeline order honors the user's sequencing:
  Phase 2 research = spostgre only (NVFS research folded into arch phase plan section).
  Phase 3 arch = produce both spostgre and NVFS design docs + MDSOC+ placement.
  Phase 4 spec = feature-files/BDD for the skeleton surface + FS-request workflow.
  Phase 5 implement = MDSOC+ skeleton code + initial NVFS feature requests emitted
    as concrete backlog entries (not real engine code).
  Phases 6-8 = refactor/verify/ship the scaffolding, not the production engines.

Naming discipline (from user's attached plan):
  - Filesystem module: **NVFS** (aka SimpleFS-NV). Code namespace: `nvfs`.
  - DB module: **spostgre** (user-chosen; mirrors "SimpleDB" role in source doc).
  - Storage classes: `META_DURABLE`, `DB_WAL`, `DB_TEMP`, `MODEL_IMMUTABLE`,
    `GENERAL_MUTABLE`, `CHECKPOINT_SNAPSHOT`.
  - Arena API verbs: `arena_create / append / readv / seal / discard / clone_range`.
  - DB forks: `rel.main / rel.pmap / rel.vmap / rel.fmap / rel.wal / rel.temp / rel.blob`.

MDSOC+ placement (per memory note `feedback_mdsoc_plus_default.md`):
  - NVFS sits in `src/lib/nogc_sync_mut/nvfs/` — kernel/driver-adjacent → MDSOC-only inner.
  - spostgre sits in `src/lib/nogc_sync_mut/spostgre/` with an MDSOC outer (modules,
    dependencies, side effects, ownership/capabilities) wrapping an ECS business layer
    (components: Relation, Page, Tuple, WalRecord, Txn, Checkpoint; systems: Commit,
    Vacuum, Checkpoint, BufferManager).

Out of scope for this SStack run:
  - Real NVMe driver work (would go in `src/lib/nogc_async_mut/`).
  - GPU/SLLM weight serving (stays referenced but not built here).
  - Benchmark harness beyond placeholders.

### 2-research
<pending>

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
