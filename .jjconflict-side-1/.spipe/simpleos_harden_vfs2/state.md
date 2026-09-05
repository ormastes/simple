# Lane VFS2b — collapse one FAT32 duplicate (team CONVERGE)

Status: **deletion landed in working copy (uncommitted)** — 3,165 lines removed
Date: 2026-07-27
Predecessor map: `.spipe/simpleos_harden_p3_vfs/state.md` (P3 inventory)
Ledger line updated: `doc/08_tracking/os/production_status.sdn` L42 (`vfs:` note only)

## 1. Inventory — every FAT32 implementation

| # | Copy | Lines | Tier / stack | Reachable? | Explicit importers | Notes |
|---|------|-------|--------------|-----------|--------------------|-------|
| 1 | `src/os/kernel/fs/fat32.spl` | ~37 KB | kernel, direct `BlockDevice` | YES | `boot_fs_mount.spl`, `services/vfs/{vfs_init,vfs_write_ops,vfs_boot_init}.spl`, `services/fat32/shared_fat32_driver.spl` | the only copy usable by baremetal presets (see §3) |
| 2 | `src/os/services/fat32/*.spl` (5 files) | 2,290 | OS service (`SharedFat32Driver`) | YES | `services/vfs/{vfs_write_ops,vfs_init,vfs_boot_init}.spl`, 8 specs | `fat32.spl`, `fat32_filesystem_ops.spl`, `fat32_write.spl`, `fat32_write_helpers.spl`, `shared_fat32_driver.spl` |
| 3 | `src/lib/nogc_sync_mut/fs_driver/fat32_*.spl` (6 files) | **3,165** | stdlib sync tier | **NO — shadowed** | **ZERO** | **DELETED this increment** |
| 4 | `src/lib/nogc_async_mut/fs_driver/fat32_*.spl` (6 files) | 2,946 | stdlib async tier | YES — what `std.fs_driver.*` actually resolves to | all `std.fs_driver.fat32_*` importers | **CANONICAL** |

Kept (sync tier, NOT deleted): `src/lib/nogc_sync_mut/fs_driver/fat32_cache.spl` (355 lines)
— async tier has no `fat32_cache`, so `std.fs_driver.fat32_cache` still resolves
here, and `test/01_unit/lib/fs_driver/fat32_cache_spec.spl` exercises it live.

## 2. Which copy is canonical — resolution evidence (not assumption)

`use std.X` → relative path `lib/X`, resolved by a **hardcoded family search order**,
identical in all three resolvers:

- `src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl` L211-243 (and L284)
- `src/compiler/80.driver/driver_source_loading.spl` L452, L469
- `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` L587

Order: `nogc_async_mut` > `nogc_async_immut` > `nogc_sync_immut` > `nogc_sync_mut` > `common` > …

**`nogc_async_mut` is first**, so every `use std.fs_driver.fat32_*` in the repo —
including the ones written *inside* `src/lib/nogc_sync_mut/fs_driver/` itself
(`instance.spl` L13, `driver_adapter.spl` L12) — binds to the **async** copy.
The sync copy is unreachable.

### Empirical probe pair (absolute oracle, not self-comparison)

`fat32_write_4k_overwrite` exists **only** in the async copy
(`nogc_async_mut/.../fat32_core.spl` L1487; absent from the sync copy).

| Probe | Import | Result |
|-------|--------|--------|
| resolve | `use std.fs_driver.fat32_core.{fat32_write_4k_overwrite}` | **PASS** — printed marker ⇒ `std.` bound to async |
| control | `use nogc_sync_mut.fs_driver.fat32_core.{fat32_write_4k_overwrite}` | **FAIL** (symbol absent) ⇒ sync copy genuinely lacks it |

The control failing is what makes the resolve probe meaningful — it rules out
"the symbol exists in both".

### Grep evidence

`grep -rn 'nogc_sync_mut\.fs_driver\.(fat32|ramfs|mount_table|instance|ops|extension|direct_io|driver_adapter)' src test` → **zero hits**.
The only explicit `nogc_sync_mut.fs_driver.*` importers are the async tier's own
re-export shims for `types` / `error` / `capability` / `block_device` / `nvfs_*`
(1–7 line files) plus `nvfs_hosted_driver.spl`. None reference FAT32.

### Git history — the concrete harm

Both copies were touched by the **identical** commit list, in lockstep:
`37cda4befdc`, `857e26b0cbc` (“7 FAT32 defects”), `752425d3fcc`, `1a17451573d`,
`a707aaf02dd` (LFN), `3f577c312de`. Every FAT32 fix has been paid for twice,
with only one of the two copies ever executing.

## 3. Why the kernel copy (#1) exists — and why deleting it is NOT this increment

`src/compiler/70.backend/target_presets.spl`: most baremetal/SimpleOS presets set
`allowed_families: ["nogc_async_mut_noalloc", "common"]` — **neither** `fs_driver`
tier is admissible there. Only wasm32 (L166) and the unrestricted presets (`[]`)
admit them. `allowed_families` is a membership **filter**
(`driver_core_types.spl` L169-171), not an ordering, so it never overrides the
async-first search order. Copies #1 and #2 therefore serve tiers #4 cannot reach;
collapsing them is a separate, multi-session job (see §6).

## 4. Decision

**Deletion target: copy #3**, `src/lib/nogc_sync_mut/fs_driver/`:
`fat32_core.spl` (1778), `fat32_dir_ops.spl` (591), `fat32_stub.spl` (483),
`fat32_parsers.spl` (146), `fat32_test_device.spl` (133), `fat32_hardening.spl` (34)
= **3,165 lines**.

Rationale: zero consumers, unreachable under every preset, and behaviourally
covered by the canonical async copy. `fat32_parsers.spl` and `fat32_hardening.spl`
were byte-identical to their async twins modulo the tier name; the rest are a
symbol-level subset (`comm` of top-level `fn`/`class` names: nothing sync-only in
`fat32_core`/`fat32_stub`/`fat32_test_device`/`ramfs`).

**No porting was required.** The one apparent divergence was investigated and
dismissed: sync `Fat32Core` carries `Dict`-based cache classes
(`FatSectorCache`/`ChainCache`/`PathCache`/`ClusterDataCache`), while the live
async `Fat32Core` uses flat, `Dict`-free single-entry fields
(`_dcache_*`, `_chain_*`, `_cluster_cache_*`, `_block_cache_*`). Both cache; the
async design deliberately avoids `Dict` for allocation-constrained SimpleOS
targets. Porting the `Dict` strategy into the live copy would be a regression,
not a rescue. Recoverable from git (`37cda4befdc`) if ever wanted.

**No consumers were rerouted** — there were none to reroute. Zero import lines
changed anywhere in the repo.

## 5. Spec verdicts — every describe block, before → after

| Spec | Baseline | After deletion |
|------|----------|----------------|
| `test/01_unit/os/arch/duplicate_owner_spec.spl` (Stage-S guard) | 4/0, 1/0, 2/0 — 7 ✓ | **7 ✓, 0 ✗** (green) |
| `test/01_unit/lib/fs_driver/fat32_cache_spec.spl` | 6/0 5/0 5/0 3/0 2/0 2/0 2/0 | **identical, 0 failures** |
| `test/01_unit/lib/fs_driver/fs_hardening_spec.spl` | 3/0 2/0 2/0 2/0 2/0 | **identical, 0 failures** |
| `test/01_unit/os/services/fat32/fat32_spec.spl` | 2/0 | **2 examples, 0 failures** |
| `test/01_unit/os/services/vfs/vfs_pure_fat_production_guard_spec.spl` | 3/0 | **3 examples, 0 failures** |
| `test/01_unit/lib/fs_driver/fat32_core_lfn_spec.spl` | **16/15 (pre-existing RED)** | **16/15 — unchanged** |
| resolve probe | PASS | **PASS** (async still binds) |

Binary: `build/native_probe/simple run <spec>`.

Note on the guard's summary lines: the run groups its three describe blocks as
`4/0 + 1/0 + 2/0` or `4/0 + 2/0` depending on run, but all **7 checkmarks are ✓
and there is never a ✗**. Counted checkmarks, not just summary lines.

### Pre-existing red, NOT caused by this lane

`fat32_core_lfn_spec.spl` fails 15/16 both before and after, with
`semantic: unknown extern function: rt_string_char_at` — an extern gap in the
probe binary, not FAT32 logic and not the shadowing. Filed here for the tooling
lane; unchanged by this increment.

## 6. Remaining convergence plan (FAT32 3 → 1)

1. **Correct the tier direction (medium).** `src/lib/.../structure.md` convention
   puts FS in `nogc_sync_mut`, and the async tier's other files are already
   re-export shims *into* sync — but resolution order makes async win, so the
   convention is inverted in practice for `fat32_*`. Either (a) accept async as
   canonical for FAT32 and document it, or (b) move the implementation to sync and
   leave 6 shim files in async — (b) changes what executes on the FS path and
   needs full QEMU + board FS validation, so it must not be done blind.
2. **`fat32_cache.spl` is now orphaned** — its only remaining consumer is its own
   spec. Delete-condition: delete once the live async core either adopts it or is
   confirmed to permanently prefer the `Dict`-free strategy.
3. **Copy #2 (`services/fat32`) into copy #1 (`kernel/fs/fat32.spl`)** — both are
   reachable and both are used by `services/vfs/*`. This is the next real
   collapse; needs the mount-path work from P3 increment 2 first.
4. **Copy #1 cannot be deleted** until baremetal presets admit a `fs_driver`
   family (see §3) — that is a `target_presets.spl` decision, not a VFS one.
5. **Board-runnable**: this increment deleted unreachable code only, so no board
   re-validation is required. Steps 1 and 3 above DO require it
   (`.claude/rules/board-runnable.md`).

## 7. Files changed this increment

- deleted `src/lib/nogc_sync_mut/fs_driver/fat32_core.spl` (1778)
- deleted `src/lib/nogc_sync_mut/fs_driver/fat32_dir_ops.spl` (591)
- deleted `src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl` (483)
- deleted `src/lib/nogc_sync_mut/fs_driver/fat32_parsers.spl` (146)
- deleted `src/lib/nogc_sync_mut/fs_driver/fat32_test_device.spl` (133)
- deleted `src/lib/nogc_sync_mut/fs_driver/fat32_hardening.spl` (34)
- edited `doc/08_tracking/os/production_status.sdn` — `vfs:` note line only
- new `.spipe/simpleos_harden_vfs2/state.md` (this file)

Net: **−3,165 lines**, 0 import lines changed. Nothing committed, per lane instruction.
