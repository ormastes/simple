# Lane FAT32C — delete the retired legacy FAT32 driver island

Status: **deletion landed in working copy (uncommitted)** — 2,232 net lines removed
Date: 2026-07-27
Predecessor: `.spipe/fs_stack_collapse/state.md` §6 Step 1 (FAT32B deferred this deliberately)

FAT32B stopped short of this deletion because it requires editing a live
production guard. This lane made that decision explicitly and executed it.

## 1. Independent re-verification of the island claim

FAT32B's claim was re-derived from scratch, not trusted. Every importer of the
four modules was swept across `src/**`, `test/**`, `scripts/**` and `config/**`.

### 1a. Module importers (`use os.services.fat32.{fat32,fat32_write,fat32_filesystem_ops,fat32_write_helpers}`)

| Consumer | Kind | Disposition |
|----------|------|-------------|
| `src/os/services/fat32/fat32.spl` | intra-island (imports `fat32_filesystem_ops`) | deleted |
| `src/os/services/fat32/fat32_write.spl` | intra-island (imports `fat32`, `fat32_write_helpers`) | deleted |
| `src/os/services/fat32/fat32_filesystem_ops.spl` | intra-island (imports `fat32`, `fat32_write`, `fat32_write_helpers`) | deleted |
| `test/01_unit/os/services/fat32/fat32_spec.spl` | tracked spec, sole external importer | deleted |
| `test/unit/os/services/fat32/fat32_spec.spl` | tracked mirror of the same | deleted |
| `test/01_unit/os/services/fat32/.spipe_matchers_fat32_spec.spl` | untracked generated wrapper of the above | deleted |
| `test/03_system/.spipe_matchers_storage_fat32_{positional_cursor,statfs_truncate}_spec.spl` | untracked, **stale** | deleted (see 1c) |
| guard + no-regression specs | `source.contains(...)` text assertions, **not** imports | kept, still valid |

**Zero importers in `src/` outside the island itself.** The island is closed.

### 1b. The sanctioned facade delegates elsewhere — confirmed

`src/os/services/fat32/shared_fat32_driver.spl` imports only
`std.fs_driver.{fat32_core, types, direct_io}`, `os.kernel.types.fs_types` and
`os.services.block_device`. It has **no** `use os.services.fat32.*` line at all,
so it never touched the four deleted modules.

### 1c. A staleness finding FAT32B did not record

The two `test/03_system/.spipe_matchers_storage_fat32_*` wrappers still imported
`os.services.fat32.fat32` / `fat32_write`, but their **tracked sources**
(`test/03_system/os/storage_fat32_{positional_cursor,statfs_truncate}_spec.spl`)
had already migrated to `std.fs_driver.fat32_core`. They were untracked generated
artifacts left over from before that migration — dead on arrival, and deleted
here rather than left to dangle.

### 1d. Boot path / image builder / script sweep

`git ls-files | xargs grep -l "os/services/fat32"` over the whole repo, excluding
`doc/`: **four hits, all specs** (the two guard copies and the two
`vfs_boot_nvme_lease_spec.spl` copies, the latter referencing only the surviving
`shared_fat32_driver.spl`). No `.shs` script, no image builder, no `FILE.md`
manifest, no kernel or boot module names any deleted file.

## 2. The guard block — strengthened, not removed

FAT32B's plan called for **removing** the `it` block that
`read_file`s the deleted spec. That would have traded a real invariant for
nothing. The block was **rewritten to assert absence** instead.

### What the guard protects

`vfs_pure_fat_production_guard_spec.spl` keeps the retired FAT driver off the
SimpleOS boot path. Deleting the driver does not remove that need — a future
agent can re-add the files. Absence is a strictly cheaper and stronger invariant
than non-use, so the guard got better, not weaker.

### Changes

1. `_assert_os_tree_no_production_legacy_fat_driver()` — **dropped its 4-file
   exemption**. The walk over `src/os` previously skipped the four legacy impl
   files (they necessarily imported each other). With them gone the exemption is
   vacuous, so the walk now covers **all** of `src/os` with no exceptions.
2. `_is_legacy_fat_implementation()` — **kept**, repurposed from "which files are
   exempt" to "which files must never exist". Retaining it keeps a named,
   greppable record of exactly what was retired.
3. `it "keeps legacy FAT unit coverage from instantiating the retired driver"`
   → `it "keeps the retired legacy FAT driver files deleted from the source
   tree"`, calling a new `_assert_legacy_fat_implementation_files_deleted()`
   that walks `src/os` and asserts no path matches the retired set.
4. `_assert_no_legacy_fat_driver` / `_assert_no_legacy_fat_module_import` —
   unchanged, still guarding the VFS/boot production files by name.

**Protection lost: none.** The old block asserted that a now-deleted spec did not
call `Fat32Driver.new(` / `resolve_path(` / `readdir(`. That assertion is
subsumed: the type it guarded against no longer exists anywhere in the tree.

### Negative control — the new assertion demonstrably bites

This is the important part, because a `read_file` on a **missing** path does not
fail a spec — it returns empty and every `contains(...) == false` passes
vacuously. That is exactly how a dangling path-guard hides. The replacement was
therefore proven to fail in the positive direction:

| Tree state | JIT | Interpreter |
|------------|-----|-------------|
| four files **present** (restored mid-lane by a parallel session) | **3 examples, 2 failures** | **3 examples, 2 failures** |
| four files **deleted** | **3 examples, 0 failures** | **3 examples, 0 failures** |

Both the tree-walk block and the new absence block flipped red with the files
present. The guard is load-bearing, not decorative.

### Landmine hit: parallel session reverted the guard edits

Mid-lane a concurrent session restored all four deleted `src/` files **and**
reverted both guard specs to their `HEAD` content. Caught by re-grepping the
files after editing (per `feedback_write_tool_silent_drops`). Edits were
re-applied and re-verified by grep before re-running. Worth noting that the
**old** guard reported a false 3/0 GREEN in that window while `read_file`ing an
already-deleted spec — the precise failure mode the rewrite eliminates.

## 3. Path-reference sweep

Literal-path grep for `src/os/services/fat32/{fat32,fat32_write,fat32_filesystem_ops,fat32_write_helpers}.spl`
and `os/services/fat32/fat32_spec.spl` across every tracked file
(`git ls-files -z | xargs -0 grep -l`, covering `test/01_unit/**`, `test/unit/**`,
`test/02_integration/**`, `test/integration/**`, `test/03_system/**`,
`test/system/**`, `scripts/**`, `src/**`, `config/**`):

- **2 hits**, both the guard spec copies — both rewritten (§2).
- **Zero `# @cover` annotations** pointed at any deleted file.
- **Zero** `.shs` / `.sdn` / `.toml` / `.json` / `FILE.md` references.
- Residual mentions live only in `doc/` prose and in `.spipe/*/state.md` lane
  records, which are history and correctly describe the pre-deletion state.

Every string still asserted by the surviving guard was verified present in its
target before the rewrite was accepted (the `shared_fat32_driver.spl` and
`vfs_boot_init.spl` assertions in block 1 are untouched and still green).

## 4. Verification

Binary: `bin/simple run` (self-hosted `bin/release/x86_64-unknown-linux-gnu/simple`).
Baseline captured **before** deletion in `build/fat32c_baseline/`, after in
`build/fat32c_after/`. Per-`describe`-block summary lines compared; never a
whole-suite `simple test`.

| Spec | Baseline (per describe) | After deletion | Verdict |
|------|-------------------------|----------------|---------|
| `os/services/vfs/vfs_pure_fat_production_guard_spec.spl` **(rewritten)** | 3/0 | **3/0** | **GREEN** |
| `os/arch/duplicate_owner_spec.spl` **(Stage-S guard)** | 4/0, 1/0, 2/0 | **4/0, 1/0, 2/0 — 7 ✓ / 0 ✗** | **GREEN** |
| `os/services/vfs/vfs_chmod_symlink_spec.spl` | 1/0, 2/0 | 1/0, 2/0 | GREEN |
| `os/services/vfs/vfs_boot_memory_swap_range_spec.spl` | 1/0 | 1/0 | GREEN |
| `os/services/vfs/dbfs_direct_io_blob_extent_spec.spl` | 1/1 | 1/1 | pre-existing red, unchanged |
| `os/services/vfs/nvme_block_adapter_spec.spl` | 9/2 | 9/2 | pre-existing red, unchanged |
| `os/services/vfs/nvme_filesystem_mounts_spec.spl` | 18/8 | 18/8 | pre-existing red, unchanged |
| `os/services/vfs/pseudofs_hardening_spec.spl` | 11/11, 10/10 | 11/11, 10/10 | pre-existing red, unchanged |
| `os/services/vfs/pseudofs_mount_spec.spl` | 6/6, 4/4, 3/3 | 6/6, 4/4, 3/3 | pre-existing red, unchanged |
| `os/services/vfs/vfs_boot_nvme_lease_spec.spl` | 27/7 | 27/7 | pre-existing red, unchanged |
| `os/services/vfs/vfs_boot_production_handoff_spec.spl` | 1/1 | 1/1 | pre-existing red, unchanged |
| `os/services/vfs/vfs_nvfs_connector_spec.spl` | 14/12 | 14/12 | pre-existing red, unchanged |
| `os/services/vfs/vfs_rootfs_porting_spec.spl` | 9/8 | 9/8 | pre-existing red, unchanged |
| `os/services/vfs/vfs_spec.spl` | 19/12 | 19/12 | pre-existing red, unchanged |
| `lib/fs_driver/fat32_core_lfn_spec.spl` | 16/15, 1/1 | 16/15, 1/1 | known red (`rt_string_char_at`), unchanged |

**All 15 specs byte-identical to baseline, block for block** — including every
pre-existing failure count. That identity is itself proof the deleted copies were
never executing.

### FAT32 survivors — the facade still binds

Specs that exercise the surviving `std.fs_driver.fat32_core` path, run after
deletion:

| Spec | Result |
|------|--------|
| `test/03_system/os/storage_fat32_positional_cursor_spec.spl` | **2/0 GREEN** |
| `test/03_system/os/storage_fat32_handle_metadata_spec.spl` | **2/0 GREEN** |
| `test/03_system/os/storage_fat32_statfs_truncate_spec.spl` | 5/5 — A/B'd, pre-existing |
| `test/02_integration/storage/dbfs/fat32_no_regression_spec.spl` | 2/1, 1/1 — A/B'd, pre-existing |

The two reds were not in the baseline set, so they were A/B'd explicitly: the
four files were restored with `git show HEAD:<path> > <path>` and the specs
re-run — **5/5 and 2/1, 1/1, identical**. Pre-existing, not lane damage. Files
re-deleted afterwards and `src/os/services/fat32/` confirmed back to a single
entry (`shared_fat32_driver.spl`).

### JIT vs interpreter A/B

| Spec | JIT | Interpreter |
|------|-----|-------------|
| `vfs_pure_fat_production_guard_spec.spl` | 3/0 | **3/0** |
| `duplicate_owner_spec.spl` (Stage-S) | 4/0, 1/0, 2/0 | **4/0, 1/0, 2/0** |

Plus the negative control in §2, also run in both modes.

### Board-runnable

Per `.claude/rules/board-runnable.md`: this increment removed **unreachable** code
only — zero `src/` importers, and every spec block count byte-identical to
baseline in both execution modes. No executing code path changed, no `src/os`
import line changed, so no board re-validation is required. The remaining FAT32
collapse step (`src/os/kernel/fs/fat32.spl`) *does* change the boot path and
still needs full QEMU + board FS validation.

## 5. Net lines

| Group | Lines |
|-------|------:|
| `src/os/services/fat32/fat32_filesystem_ops.spl` | −668 |
| `src/os/services/fat32/fat32.spl` | −597 |
| `src/os/services/fat32/fat32_write.spl` | −765 |
| `src/os/services/fat32/fat32_write_helpers.spl` | −92 |
| **src subtotal** | **−2,122** |
| `test/01_unit/os/services/fat32/fat32_spec.spl` | −53 |
| `test/unit/os/services/fat32/fat32_spec.spl` | −53 |
| `test/{01_unit,unit}/os/services/fat32/fat32/summary.txt` (spec output artifacts) | −12 |
| guard rewrite ×2 | −22 / +22 |
| **NET DELETED (tracked, `git diff --stat`: 22 insertions / 2,254 deletions)** | **−2,232** |

Untracked stale generated artifacts also removed (not counted above):
`test/01_unit/os/services/fat32/.spipe_matchers_fat32_spec.spl` (543),
`test/03_system/.spipe_matchers_storage_fat32_positional_cursor_spec.spl` (82),
`test/03_system/.spipe_matchers_storage_fat32_statfs_truncate_spec.spl` (69).

`src/os/services/fat32/` went from 5 files to **1** — the sanctioned facade alone.
FAT32 implementation copies: **3 → 2**.

## 6. Remaining work

`src/os/kernel/fs/fat32.spl` (813 lines) is the last redundant copy and is
**still blocked**, unchanged from `.spipe/fs_stack_collapse/state.md` §2:
`boot_fs_mount.spl` L46 imports `parse_bpb` from it and four kernel specs bind
`Fat32Filesystem` directly. Deleting it requires a `target_presets.spl` decision
to admit an `fs_driver` family on baremetal, changes what executes on the boot
path, and therefore needs QEMU + board validation. Out of scope for a deletion
lane.

Docs still naming the deleted `src/os/services/fat32/*` paths are prose only and
listed in `.spipe/fs_stack_collapse/state.md` §6 Step 3 as a docs-only follow-up.

## 7. Files changed this increment

Deleted (`src/os/services/fat32/`): `fat32.spl`, `fat32_write.spl`,
`fat32_filesystem_ops.spl`, `fat32_write_helpers.spl`.
Deleted (specs): `test/01_unit/os/services/fat32/fat32_spec.spl`,
`test/unit/os/services/fat32/fat32_spec.spl`, plus 3 untracked generated wrappers.
Edited: `test/01_unit/os/services/vfs/vfs_pure_fat_production_guard_spec.spl`,
`test/unit/os/services/vfs/vfs_pure_fat_production_guard_spec.spl`,
`doc/08_tracking/os/production_status.sdn` (`vfs:` note line).
New: `.spipe/fat32_island_deletion/state.md` (this file),
`build/fat32c_baseline/`, `build/fat32c_after/`.

Nothing committed, per lane instruction.
