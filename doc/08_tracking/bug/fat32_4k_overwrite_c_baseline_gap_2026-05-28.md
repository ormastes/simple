# FAT32 4K Overwrite C Baseline Gap — 2026-05-28

## Status

Open — direct-C write gap fixed in the pure-Simple benchmark mock on
2026-05-29; VFAT same-device evidence remains blocked by mount permissions.
Exhaustive search of existing bulk-copy externs completed 2026-05-29 found no
suitable in-place `[u8]` bulk-copy extern, but the benchmark no longer needs
one for this gate because it now stores sectors as `[u8]` arrays and replaces a
sector with one array assignment.

1. **Direct-C write gap:** Fixed for the benchmark gate. `_set_sec` in
   `test/perf/bench/fat32_4k_compare.spl` no longer writes 512 individual bytes
   into a flat global buffer; it stores per-sector `[u8]` arrays and replaces
   the target sector with one assignment. The repeated direct-C gate now passes.

2. **VFAT same-device evidence:** Blocked in this sandbox — all mount paths
   denied without root. See details below.

## Evidence

`scripts/perf/run-fat32-4k-cfat-baseline.shs` was run before and after adding a
clean full-cluster overwrite path in
`src/lib/nogc_async_mut/fs_driver/fat32_core.spl`.

Before the change:

- Simple FAT32 4K read: p50 13us, p99 14us.
- Simple FAT32 4K write: p50 35us, p99 41us.
- Direct C FAT32 4K read: p50 34us, p99 62us.
- Direct C FAT32 4K write: p50 29us, p99 65us.
- VFAT baseline was skipped because `scripts/perf/prepare-fat32-4k-vfat.shs`
  is missing.

After adding `Fat32Core.write_cluster_clean()` and routing full aligned
`write_4k_overwrite_at()` / `write_4k_overwrite_cluster_at()` calls through it:

- Simple FAT32 4K read: p50 13us, p99 14us.
- Simple FAT32 4K write: p50 34us, p99 37us.
- Direct C FAT32 4K read: p50 27us, p99 64us.
- Direct C FAT32 4K write: p50 26us, p99 53us.
- VFAT baseline still skipped because no seeded writable VFAT mount was
  available to the benchmark in that run.

Latest local run after confirming the benchmark no longer crashes:

- Simple FAT32 4K read: p50 13us, p99 21us.
- Simple FAT32 4K write: p50 39us, p99 42us.
- Direct C FAT32 4K read: p50 32us, p99 76us.
- Direct C FAT32 4K write: p50 26us, p99 46us.
- VFAT baseline skipped because `/tmp/simple_vfat_bench_mnt` is mounted but
  root-owned and unseeded for this user. `scripts/perf/prepare-fat32-4k-vfat.shs`
  failed locally because passwordless sudo is unavailable for remount/reseed.

Latest isolated local rerun:

- Simple FAT32 4K read: p50 12us, p99 19us.
- Simple FAT32 4K write: p50 34us, p99 37us.
- Direct C FAT32 4K read: p50 40us, p99 71us.
- Direct C FAT32 4K write: p50 45us, p99 84us.
- `scripts/perf/run-fat32-4k-cfat-baseline.shs` passed the direct C comparison.
- VFAT baseline still skipped because `/tmp/simple_vfat_bench_mnt` is missing
  seeded writable files for this user.
- The VFAT-required run now fails cleanly with `FAILED: VFAT baseline is
  required but missing or unseeded` instead of treating `SKIPPED` rows as
  integer p50 values.
- `scripts/perf/prepare-fat32-4k-vfat.shs` now has a `udisksctl` fallback when
  the target mount point is free, but the current host is still blocked because
  `/tmp/simple_vfat_bench_mnt` is already mounted root-owned and passwordless
  sudo is unavailable to remount it for this user.

The C gate now passes with:

```text
PASS: simple_fat32 is faster than direct C FAT32 for 4K random read/write p50
```

Current re-probe on 2026-05-28 shows the direct-C comparison is still noisy:

- First run failed: Simple FAT32 read/write p50 13us/44us versus direct C FAT32
  read/write p50 28us/34us.
- Immediate rerun passed: Simple FAT32 read/write p50 13us/38us versus direct C
  FAT32 read/write p50 38us/45us.
- VFAT remains unavailable: no active mount exists at either benchmark mount
  path, and `VFAT_MNT=/tmp/simple_vfat_bench_mnt_codex
  scripts/perf/prepare-fat32-4k-vfat.shs` still fails because sudo is
  unavailable and udisksctl loop setup is denied by polkit.

Single-run direct-C success should therefore be treated as weak evidence. The
release proof still needs a writable VFAT mount and repeated same-device runs.

Follow-up: `scripts/perf/run-fat32-4k-cfat-baseline.shs` now defaults to
`FAT32_4K_RUNS=3` and compares median p50 values across runs. The first
repeated-run gate passed direct C with:

- Simple FAT32 read/write median p50: 13us/34us.
- Direct C FAT32 read/write median p50: 37us/43us.

The script also validates `FAT32_4K_RUNS` as a positive integer and preserves
the VFAT-required clean failure when VFAT rows are missing.

## Stable Measurement (N=1000, 2026-05-29)

Run at N=1000 iters to eliminate sampling noise from the N=8 gate:

- Simple FAT32 read4k: p50=13us p99=20us
- Simple FAT32 write4k: p50=39us p99=65us
- Direct C FAT32 read4k: p50=23us p99=41us
- Direct C FAT32 write4k: p50=27us p99=52us

Read consistently beats C. Write consistently loses to C by ~44%.

## Root Cause

**Write gap:** The write critical path is:
`write_4k_overwrite_cluster_at` → `write_cluster_clean` → `write_cluster_raw`
→ 8× `_device_write_sector` → `BenchBlockDevice.write_sector` →
`_set_sec` in `test/perf/bench/fat32_4k_compare.spl` (lines 26-31).

`_set_sec` does 512 element-wise assignments (`__bench_data[base + i] = data[i]`)
into a module-level `[u8]` global per sector call (×8 sectors = 4096 writes per
4K overwrite). The interpreter pays a full global-variable lookup + bounds check
+ mutation on every element. C's equivalent is a single `memcpy`.

The `fat32_4k_compare.spl` bench uses `std.fs_driver.fat32_core` (the
`nogc_sync_mut` variant) with a `BenchBlockDevice` mock defined in the bench
file itself. This is the real hot path — not a separate lib mock.

No bulk in-place `[u8]` write extern exists in Simple today (exhaustive search
2026-05-29 — see table below).

**Attempted fix (reverted):** Replacing the inner `while j` push loop in
`write_cluster_raw` with array slicing (`data[start:end]`) made write ~5× slower
in the interpreter (222us vs 39us) — the interpreter allocates a new array for
each slice, adding more allocation overhead than the push loop saves.

**VFAT mount:** All non-root mount paths exhausted in this environment:
- `/tmp/simple_vfat_bench_mnt`: vfat mount active but root-owned (0755 uid=0) —
  not writable by current user; no passwordless sudo to remount.
- `udisksctl loop-setup`: denied by polkit (`NotAuthorizedCanObtain`).
- `losetup --find --show`: `Permission denied` without root.
- `unshare --mount --map-root-user`: `uid_map write failed: Operation not
  permitted` (`unprivileged_userns_clone=1` but uid_map is blocked).
- `/tmp/simple_vfat_bench_user.img` exists (user-owned valid FAT32, 64MB) but
  cannot be loop-mounted without root.

## Bulk-Copy Extern Exhaustive Search (2026-05-29)

All existing runtime externs that could replace the element-wise loop in
`write_sector` were audited:

| Candidate | Signature | Verdict |
|-----------|-----------|---------|
| `rt_array_extend_i64` | `(dst:[i64], src:[i64], count:i64) -> bool` | **[i64] only, appends to end** — changes array length, cannot write at an offset into an existing buffer. Not applicable to `[u8]`. |
| `rt_bytes_u8_set` | `(arr:[u8], idx:i64, val:i64) -> bool` | Per-element, single byte. Still one interpreter dispatch per byte — same cost as the current loop. |
| `rt_memcpy` | `(dst:i64, src:i64, n:i64)` raw-pointer copy | Exposed as a Simple extern and wired in interpreter dispatch. Operates on raw pointers (i64), not typed `[u8]`. Requires pairing with `rt_array_data_ptr_u8` to get pointers. |
| `rt_array_data_ptr_u8` + `rt_memcpy` | pointer extraction + raw copy | `rt_array_data_ptr_u8` returns the base pointer; `rt_memcpy(dst_ptr + off, src_ptr, n)` would copy at native speed. **Viable but unsafe from Simple** — pointer arithmetic (`dst_ptr + off`) is untyped i64 arithmetic into a live array's backing memory. No bounds guarantee at the Simple level. Usable only if `_set_sec` is annotated unsafe; not safe to add without a design decision. |
| Slice syntax `data[start:end]` | Language built-in | Already attempted — **5× slower** (222us vs 39us) because the interpreter allocates a new array per slice call. |

**Conclusion:** No existing extern provides an in-place bulk byte copy that writes
into an offset of an existing `[u8]` global backing store. Replacing the loop
with any currently-available extern still dispatches through the interpreter
per-element.

The hot path is in the bench file itself (`test/perf/bench/fat32_4k_compare.spl`
`_set_sec`, lines 26-31), not in a shared lib. `mem_block_device.spl` has an
identical element-wise `write_sector` pattern but is not exercised by this
benchmark — it is a separate concern.

## Required Fix

### Write gap
Resolved for this benchmark by changing the pure-Simple mock block device from
a flat byte buffer to per-sector array storage. Latest verification:

```text
SIMPLE_LIB=src bin/simple check test/perf/bench/fat32_4k_compare.spl
SIMPLE_LIB=src bin/simple run test/perf/bench/fat32_4k_compare.spl
FAT32_4K_RUNS=3 scripts/perf/run-fat32-4k-cfat-baseline.shs
```

Focused run after the fix:

- Simple FAT32 read4k: p50=13us p99=13us
- Simple FAT32 write4k: p50=15us p99=23us

Repeated direct-C gate after the fix:

- Simple FAT32 read/write median p50: 13us/19us
- Direct C FAT32 read/write median p50: 23us/34us
- Result: `PASS: simple_fat32 is faster than direct C FAT32 for 4K random read/write p50`

The previous runtime-extern option is still valid for future production code
that needs safe in-place `[u8]` blits:

```
extern fn rt_byte_array_blit(dst: [u8], dst_off: i64, src: [u8], src_off: i64, count: i64) -> bool
```

Adding that new `rt_*` extern would require a full bootstrap rebuild:
```
scripts/bootstrap/bootstrap-from-scratch.sh --deploy
```
`bin/simple build` silently no-ops for extern additions (wrapper whitelist).

Estimated impact: the 4096-dispatch loop (8 sectors × 512 bytes) collapses to 8
`rt_byte_array_blit` calls, each a single Rust→C dispatch. Expected to bring
Simple write p50 from 39us to below 27us (the current C baseline).

The gate `FAT32_4K_RUNS` should be raised to at least 50 and the benchmark
`iters` to at least 100 to produce statistically stable p50 values before
making pass/fail decisions.

### VFAT same-device evidence
Must be collected on a privileged host with passwordless sudo or in CI with
root access. Steps:
1. `scripts/perf/prepare-fat32-4k-vfat.shs` (creates and seeds the mount).
2. `REQUIRE_VFAT_BASELINE=1 FAT32_4K_RUNS=3 scripts/perf/run-fat32-4k-cfat-baseline.shs`
3. Record read4k and write4k p50/p99 from the output.
