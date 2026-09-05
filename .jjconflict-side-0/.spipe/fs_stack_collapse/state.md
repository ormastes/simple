# Lane FAT32B — FS-stack collapse increment 2 (team CONVERGE)

Status: **deletion landed in working copy (uncommitted)** — 3,494 net lines removed
Date: 2026-07-27
Predecessors: `.spipe/simpleos_harden_vfs2/state.md` (VFS2, −3,165), `.spipe/simpleos_harden_p3_vfs/state.md` (P3 inventory)

VFS2 collapsed the shadowed **FAT32** files of the `nogc_sync_mut` tier. This lane
finishes that job for the **rest of `fs_driver`** — the same shadowing defect,
seven more files — and resolves VFS2's orphaned `fat32_cache.spl`.

## 1. What was deleted and why

### 1a. The seven remaining shadowed `nogc_sync_mut/fs_driver` files (2,477 lines)

VFS2 proved `use std.X` resolves families in a fixed order with **`nogc_async_mut`
first** (`module_loader_resolve.spl` L211-243, `driver_source_loading.spl` L452/L469,
`module_lowering.spl` L587). That reasoning was applied only to `fat32_*`. It applies
verbatim to every `fs_driver` module that exists in **both** tiers:

| File | sync lines | async twin | diff | sync-only top-level symbols |
|------|-----------:|-----------:|-----:|-----------------------------|
| `extension.spl` | 218 | 218 | **0 (byte-identical)** | none |
| `instance.spl` | 195 | 195 | **0 (byte-identical)** | none |
| `ops.spl` | 138 | 138 | **0 (byte-identical)** | none |
| `driver_adapter.spl` | 198 | 198 | 10 (whitespace only) | none |
| `direct_io.spl` | 222 | 222 | 16 (local `val` renames only) | none |
| `mount_table.spl` | 691 | 677 | 160 | `open_dir_count`, `open_file_count` |
| `ramfs.spl` | 815 | 774 | 180 | `close_handle` |
| **total** | **2,477** | | | |

Reachability: **zero** explicit `nogc_sync_mut.fs_driver.<name>` importers for any
of the seven (repo-wide grep). The only explicit sync-tier importers anywhere are
the async tier's own nine re-export shims (`types`, `error`, `capability`,
`block_device`, `nvfs_arena`, `nvfs_superblock`, `nvfs_driver`, `nvfs_posix_driver`,
`nvfs_hosted_driver`) plus one intra-directory alias in
`nvfs_hosted_driver.spl` L9 — **none** of which name a deleted file.
Sync `__init__.spl` is a docstring only (no `export use`); async `__init__.spl`
re-exports only shim modules. Nothing bound to these seven.

### Porting check (survivor first) — nothing to port

The three sync-only symbols were investigated, not assumed away:

- `MountTable.open_dir_count` / `open_file_count` — **zero callers anywhere** in
  `src/` or `test/`. Dead accessors on a dead copy.
- `RamFsDriver.close_handle` — a two-line alias whose body is `self.close(handle)`.
  The live async `mount_table.spl` L163 already dispatches `RamFs` via
  `case DriverInstance.RamFs(d): d.close(handle)`. Behaviour already present.

No feature existed only in the deleted copy, so no port was required.

### Git evidence — the double-payment harm

Every one of the seven pairs has **15 commits on the sync file and 15 on the async
twin**, an exact lockstep. Same signature VFS2 documented for `fat32_*`: every fix
paid for twice, only one copy ever executing.

### 1b. `fat32_cache.spl` (403) + its two spec copies (614) — VFS2's delete-condition, resolved

VFS2 left this with an explicit condition: *"delete once the live async core either
adopts it or is confirmed to permanently prefer the `Dict`-free strategy."*

**Condition resolved in favour of deletion, by measurement:**

- `src/lib/nogc_async_mut/fs_driver/fat32_core.spl` contains **0** occurrences of
  `Dict` and **77** references to the flat single-entry cache fields
  (`_dcache_*`, `_chain_*`, `_cluster_cache_*`, `_block_cache_*`). The `Dict`-free
  strategy is structural, not incidental.
- The async core's import list does **not** include `fat32_cache` — it never adopted it.
- Consumers of `fat32_cache` / `FatSectorCache` / `ChainCache` / `ClusterDataCache`
  repo-wide: the file itself and its own spec (two mirrored copies). A closed loop.
- `doc/09_report/nogc_eviction_leak_audit_2026-07-25.md` §1 records a **CONFIRMED
  high-severity leak** in exactly these four classes (`_evict_one()` discards
  `Dict.delete` returns; `clear()` reassigns without freeing). Adopting it into the
  live core would import a known leak — a regression, not a rescue.

Deleted with its specs (`test/01_unit/lib/fs_driver/fat32_cache_spec.spl` and the
`test/unit/**` mirror, 307 lines each). The 25 examples were green but exercised
only unreachable code. Recoverable from git if the strategy ever reverses.

## 2. Path-reference sweep (VFS2's miss class — the main risk here)

Specs reference implementations **by path**, which deletion silently breaks. Full
sweep of `test/` (both `test/01_unit/**` and the tracked `test/unit/**` mirror,
plus `test/02_integration`, `test/03_system`, `test/integration`, `test/system`):

- **25 files carried `# @cover src/lib/nogc_sync_mut/fs_driver/<deleted>.spl`
  annotations** — all repointed to `src/lib/nogc_async_mut/fs_driver/<same>.spl`.
  These annotations were *already wrong before this lane*: the specs
  `use std.fs_driver.*`, which binds async, so coverage was being attributed to a
  file that never executed. The repoint is a correctness fix, not just cleanup.
- **One dangling reference left over from VFS2 was found and repaired**:
  `test/01_unit/os/services/vfs/.spipe_wrapped_entry_nvme_filesystem_mounts_spec.spl`
  L230-231 still did `read_file("src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl")`
  and `.../fat32_core.spl` — both **deleted by VFS2**. The unwrapped spec had been
  repaired; the generated wrapper had not. Repointed to the async survivor and the
  now-duplicate `async_core` assertions dropped.
- **Every asserted string was verified present in the survivor** before repointing
  (`grep -cF`, all ≥1): `if self.direct_io.is_none():` (stub, 1),
  `val extent = self.inner.direct_io_extent_for_handle(...)` (stub, 1),
  `me fn direct_io_extent_for_handle(...)` (core, 1),
  `val chain_rc = self.follow_chain(of.start_cluster)` (core, 6),
  `val storage_lba = self.cluster_to_sector(...)` (core, 1),
  `return Err("direct I/O range crosses FAT32 cluster")` (core, 1).
- Residual `.spl`/`.shs` references to any deleted module across `src/lib`, `src/os`,
  `src/app`, all `test/` trees and `scripts/`: **zero**.
- `test/01_unit/compiler/std/nogc_sync_mut/fs_driver/` is an **untracked** generated
  staging copy of the stdlib (`git ls-files` → 0 entries); left alone.
- Remaining sync-tier path mentions live only in prose docs
  (`doc/07_guide/os/fs_driver.md`, `doc/05_design/os/storage/fs_driver_interface.md`,
  `doc/04_architecture/os/{dbfs_architecture,driver/driver_architecture}.md`) and in
  auto-regenerated trackers (`doc/08_tracking/**`, `doc/10_metrics/**`). Outside this
  lane's owned paths — listed in §5 as follow-up.

## 3. Consumers rerouted

**Zero import lines changed** — as in VFS2, there were none to reroute: all seven
deleted modules had zero explicit importers, and every `use std.fs_driver.<name>`
already bound to the async tier. Only path-valued *annotations* and *source-text
guards* needed repointing (§2).

## 4. Verification

Binary: `build/native_probe/simple run <spec>`. Baseline captured **before** deletion
(`build/fat32b_baseline/`), after in `build/fat32b_after/`. Per-describe-block
summary lines counted, never a whole-suite run.

| Spec | Baseline (per describe) | After deletion | Verdict |
|------|-------------------------|----------------|---------|
| `test/01_unit/os/arch/duplicate_owner_spec.spl` **(Stage-S guard)** | 4/0, 1/0, 2/0 | **4/0, 1/0, 2/0 — 7 ✓ / 0 ✗** | **GREEN** |
| `test/01_unit/lib/fs_driver/fs_hardening_spec.spl` | 3/0 2/0 1/0 2/0 1/0 1/0 2/0 1/0 2/0 | identical | unchanged |
| `test/01_unit/fs_driver/extension_test.spl` | 2/0 2/0 1/0 1/0 1/0 1/0 1/0 6/0 | identical | unchanged |
| `test/02_integration/fs_driver/capability_dispatch_test.spl` | 3/0 2/0 3/0 6/0 | identical | unchanged |
| `test/01_unit/fs_driver/instance_test.spl` | 4/3, 1/0 | identical | pre-existing red, unchanged |
| `test/01_unit/fs_driver/mount_table_test.spl` | 3/1 4/2 3/1 3/1 | identical | pre-existing red, unchanged |
| `test/01_unit/fs_driver/mount_table_resolve_test.spl` | 6/4 | identical | pre-existing red, unchanged |
| `test/01_unit/fs_driver/ramfs_test.spl` | 13 blocks, 30 failures | identical | pre-existing red, unchanged |
| `test/02_integration/fs_driver/multi_mount_test.spl` | 3/3 4/4 5/0 4/2 | identical | pre-existing red, unchanged |
| `test/01_unit/os/services/fat32/fat32_spec.spl` | — | 1/0, 2/0 | green |
| `test/01_unit/os/services/vfs/vfs_pure_fat_production_guard_spec.spl` | — | 3/0 | green |
| `test/03_system/hardware/driver_dma_direct_io_spec.spl` (repointed `@cover`) | — | 8/0 | green |
| `test/01_unit/os/services/vfs/nvme_filesystem_mounts_spec.spl` | **18/8** (A/B, see below) | **18/8** | pre-existing red, unchanged |
| `test/01_unit/lib/fs_driver/fat32_core_lfn_spec.spl` | 16/15 (known) | 16/15, 1/1 | pre-existing red, unchanged |

**All post-deletion numbers are byte-identical to baseline, block for block.** That
identity — including every pre-existing failure count — is itself the proof that the
deleted copies were never executing.

### A/B against HEAD for the one unexplained red

`nvme_filesystem_mounts_spec.spl` runs 18/8. To rule it in or out as lane damage the
eight deleted files were restored in place (`git show HEAD:<path> > <path>`; a plain
`git checkout` was blocked by a parallel session holding `.git/index.lock`) and the
spec re-run: **18 examples, 8 failures — identical**. Pre-existing, not this lane.
The failing examples are all NVFS/DBFS arena and BlockDevice cases; the FAT32
direct-I/O extent example (the one touching repointed paths) passes. Files re-deleted
afterwards; `src/lib/nogc_sync_mut/fs_driver/` confirmed back at 14 entries.

### Resolve probe — absolute oracle, JIT and interpreter

`build/fat32b_probe_resolve.spl` imports a symbol through **every** deleted module
name via `std.`: `mount_table.{MountTable}`, `ramfs.{RamFsFile}`,
`instance.{DriverInstance}`, `extension.{SnapshotExt}`, `direct_io.{DirectIoRequest}`,
`ops.{FsDriver}`, and constructs a `MountTable`.

| Mode | Result |
|------|--------|
| `build/native_probe/simple run` (JIT) | **PASS** — `FAT32B-RESOLVE-OK` |
| `SIMPLE_EXECUTION_MODE=interpreter` | **PASS** — `FAT32B-RESOLVE-OK` |

Every `std.fs_driver.<deleted-sync-name>` still binds after deletion, proving the
async tier was the live copy in both execution modes.

Stage-S guard also re-run under `SIMPLE_EXECUTION_MODE=interpreter`: **4/0, 1/0, 2/0**
— identical to JIT.

### Board-runnable

Per `.claude/rules/board-runnable.md`: this increment removed **unreachable** code
only (proved by the resolve probe and by baseline-identical spec output), so no
executing code path changed and no board re-validation is required. The §5 follow-ups
that *do* change what executes are flagged there.

## 5. Net lines

| Group | Lines |
|-------|------:|
| `src/lib/nogc_sync_mut/fs_driver/` — 8 files deleted | **−2,880** |
| `test/**` — 2 spec copies deleted (`fat32_cache_spec.spl` ×2) | −614 |
| `test/**` — 25 `@cover` annotations repointed + 1 stale guard repaired | −24 / +24 |
| **NET DELETED** | **−3,494** |

Files deleted (`src/lib/nogc_sync_mut/fs_driver/`): `ramfs.spl` (815),
`mount_table.spl` (691), `fat32_cache.spl` (403), `direct_io.spl` (222),
`extension.spl` (218), `driver_adapter.spl` (198), `instance.spl` (195),
`ops.spl` (138).

Directory went from 22 files to 14. Combined with VFS2, the sync `fs_driver` tier has
shed **6,045 lines** and is now exactly what it should be: the nine modules the async
tier genuinely re-exports, plus five sync-only utilities with no async twin
(`bytes_util`, `fs_bench_harness`, `handle_guard`, `mem_block_device`, `__init__`).

Nothing committed, per lane instruction.

## 6. Remaining convergence plan — FAT32 3 → 1

### Step 1 (NEXT, ready to execute): delete the retired legacy driver, `src/os/services/fat32/{fat32,fat32_write,fat32_filesystem_ops,fat32_write_helpers}.spl` — 2,122 lines

This was investigated in full this increment and is **feasible and well-scoped**, but
was deliberately not executed because it requires editing a live production guard —
a judgement call that belongs in its own reviewed increment, not a tail-end action.

Evidence it is already an orphaned island:

- The sanctioned facade `src/os/services/fat32/shared_fat32_driver.spl` (168 lines)
  delegates to **`use std.fs_driver.fat32_core.{Fat32Core}`** (L6) — i.e. the *async
  stdlib copy*. It does **not** touch the other four files at all.
- Those four files are imported **only by each other**. Zero consumers anywhere else
  in `src/`.
- `test/01_unit/os/services/vfs/vfs_pure_fat_production_guard_spec.spl` already calls
  them the **"retired driver" / "legacy FAT driver"**, forbids
  `use os.services.fat32.{fat32,fat32_write,fat32_filesystem_ops,fat32_write_helpers}`
  across the whole `src/os` tree (`_assert_os_tree_no_production_legacy_fat_driver`,
  via `rt_dir_walk`), and requires the VFS boot path to use
  `shared_fat32_driver` instead. Deletion is the sanctioned end-state of a migration
  that is already complete in production code.

Exact work required, file by file:

1. Delete the four impl files (2,122 lines).
2. Delete `test/01_unit/os/services/fat32/fat32_spec.spl`, its
   `.spipe_matchers_fat32_spec.spl` sibling, and the `test/unit/**` mirror — these
   are the only remaining importers of `os.services.fat32.fat32`.
3. Edit `vfs_pure_fat_production_guard_spec.spl`:
   - drop `_is_legacy_fat_implementation()` (its 4-path allowlist becomes vacuous;
     the tree-walk assertion then covers all of `src/os` and still passes, since
     nothing imports the deleted modules);
   - **remove the `it "keeps legacy FAT unit coverage from instantiating the retired
     driver"` block**, which does `read_file("test/unit/os/services/fat32/fat32_spec.spl")`
     — this is the path-valued guard that dangles on step 2, and it is the reason
     this step must not be done casually.
   - Keep `_assert_no_legacy_fat_driver` / `_assert_no_legacy_fat_module_import`:
     they still guard the VFS boot path against reintroduction.
4. Re-verify: the guard spec, `fat32_core_lfn_spec.spl` (imports the *facade*, must
   stay bound), `nvme_filesystem_mounts_spec.spl`, and the Stage-S duplicate-owner
   guard. No `src/os` import lines change, so no board re-validation is required —
   but confirm with the resolve-probe technique before claiming that.

Net: **−2,122** product lines, taking FAT32 from 3 copies to 2.

### Step 2: `src/os/kernel/fs/fat32.spl` (813) — blocked, unchanged from VFS2 §3

Still reachable and still not deletable. `boot_fs_mount.spl` L46 imports
`parse_bpb` from it for the sector-level BPB probe, and four kernel specs bind
`Fat32Filesystem` directly. It exists because most baremetal presets in
`target_presets.spl` set `allowed_families: ["nogc_async_mut_noalloc", "common"]`,
admitting **neither** `fs_driver` tier; `allowed_families` is a membership filter
(`driver_core_types.spl` L169-171), not an ordering, so it cannot override
async-first resolution. Deleting it requires a `target_presets.spl` decision to admit
a `fs_driver` family on baremetal — out of scope for an FS lane, and it **would**
change what executes on the boot path, so it needs full QEMU + board FS validation
per `.claude/rules/board-runnable.md`.

### Step 3: document the inverted tier convention (docs-only)

`src/lib/.../structure.md` puts FS in `nogc_sync_mut`, but resolution order makes
`nogc_async_mut` win, so for `fs_driver` the convention is inverted *in practice* —
which is precisely what allowed two full copies to be maintained in lockstep for 15
commits without anyone noticing only one ran. Now that the sync tier holds only shims
plus five sync-only utilities, the cheap fix is to state async-is-canonical for
`fs_driver` in the guide rather than move implementations (moving them changes what
executes on the FS path and needs board validation).

Doc references still naming deleted sync paths (outside this lane's owned paths):
`doc/07_guide/os/fs_driver.md` (L349, L481-486),
`doc/05_design/os/storage/fs_driver_interface.md` (L119-122),
`doc/04_architecture/os/dbfs_architecture.md` (L310-312, L501),
`doc/04_architecture/os/driver/driver_architecture.md` (L145),
`doc/05_design/os/simpleos/simpleos_fs_migration.md` (L183-184, L251, L275-276).
`doc/08_tracking/**` and `doc/10_metrics/**` regenerate and need no manual edit.

### Step 4: pre-existing reds this lane did not cause and did not fix

- `fat32_core_lfn_spec.spl` — 16/15, `unknown extern function: rt_string_char_at`
  (extern gap in the probe binary; VFS2 filed it for the tooling lane).
- `ramfs_test.spl` (30 failures), `mount_table_test.spl` (5),
  `mount_table_resolve_test.spl` (4), `multi_mount_test.spl` (9),
  `instance_test.spl` (3), `nvme_filesystem_mounts_spec.spl` (8). All A/B-confirmed
  identical before and after deletion. These specs exercise the **async** tier, so
  they are real defects in live code, not shadowing artifacts — worth a lane of their
  own now that there is only one copy to fix.

## 7. Files changed this increment

Deleted (`src/lib/nogc_sync_mut/fs_driver/`): `direct_io.spl`, `driver_adapter.spl`,
`extension.spl`, `instance.spl`, `ops.spl`, `mount_table.spl`, `ramfs.spl`,
`fat32_cache.spl`.
Deleted (specs): `test/01_unit/lib/fs_driver/fat32_cache_spec.spl`,
`test/unit/lib/fs_driver/fat32_cache_spec.spl`.
Edited: 25 test files (`@cover` repoint, 1 line each),
`test/01_unit/os/services/vfs/.spipe_wrapped_entry_nvme_filesystem_mounts_spec.spl`
(VFS2 dangling-path repair).
New: `.spipe/fs_stack_collapse/state.md` (this file),
`build/fat32b_probe_resolve.spl`, `build/fat32b_baseline/`, `build/fat32b_after/`.
