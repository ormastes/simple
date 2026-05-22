# Phase 7 Verification Plan: DBFS Integration

**Feature:** dbfs-integration
**Phase:** 7-verify (QA)
**Date:** 2026-04-28
**Mode:** interpreter only (`bin/simple test`); never `--mode=native` / `--mode=smf` per `feedback_compile_mode_false_greens`
**Source-of-truth:** `.sstack/dbfs-integration/state.md` (10 ACs), `doc/04_architecture/dbfs_architecture.md` (D1–D12)

This plan is mechanically executable: each section gives concrete commands, expected outputs, and falsification cases. A Phase 7 agent should run sections 1→6 in order, capture outputs into the Phase Outputs `7-verify` section of `state.md`, and only mark an AC checked after both the positive command passes and the negative test fails as expected.

---

## 0. Execution Preamble

Before AC checks:

```bash
# 0.1 Confirm interpreter-mode is the only mode
grep -RnE '\-\-mode=(native|smf)' /home/ormastes/dev/pub/simple/test/dbfs/ \
  /home/ormastes/dev/pub/simple/.sstack/dbfs-integration/ || echo "OK: no compile-mode invocations"

# 0.2 Confirm spec inventory matches state.md (18 specs + 2 harnesses + 1 ring_diag = 21 .spl files)
ls /home/ormastes/dev/pub/simple/test/dbfs/*.spl | wc -l   # expect: 21
```

If 0.1 prints any line, fail Phase 7 immediately and route to fix. If 0.2 mismatches, reconcile against `state.md > Phase Outputs > 4-spec > Spec File Inventory` before proceeding.

---

## 1. AC-by-AC Verification Matrix

Two ACs (AC-1, AC-10) are document-existence ACs — they verify by `grep`/section presence, NOT by `bin/simple test`. The other eight verify by spec runs plus structural greps.

### AC-1 — Engine survey + reuse-first decision (DOC-AC)

| Item | Detail |
|---|---|
| Pass criterion | `state.md` Phase 2 records reuse target (Option A or B chosen) AND a 6-item gap list. Architecture doc D1 records the same decision. |
| Command | `grep -nE 'Option [AB] — Dedicated DbFsEngine\|Simple DB\|gap list' /home/ormastes/dev/pub/simple/.sstack/dbfs-integration/state.md /home/ormastes/dev/pub/simple/doc/04_architecture/dbfs_architecture.md` |
| Expected | At least one match for `Option B — Dedicated DbFsEngine` in BOTH files; 6 numbered gaps in arch D2 |
| Negative | If `state.md` says "build new" without surveying Simple DB/nvfs, AC-1 fails |

### AC-2 — DBFS driver lands at FsDriver seam

| Item | Detail |
|---|---|
| Pass criterion | All 7 it-blocks in `dbfs_driver_spec.spl` pass; `mount_table_dbfs_dispatch_spec.spl` 7 it-blocks pass; `DbFs(driver:)` enum variant present in `instance.spl` |
| Command | `bin/simple test test/dbfs/dbfs_driver_spec.spl test/dbfs/mount_table_dbfs_dispatch_spec.spl` |
| Expected | `passed: 14, failed: 0, skipped: 0` |
| Structural grep | `grep -n 'DbFs(' /home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/fs_driver/instance.spl` (expect ≥2 hits: enum decl + driver_name arm) |
| Negative | Removing `DbFs` arm should produce exhaustive-match compile error in `mount_table.spl` and `driver/core.spl` |

### AC-3 — Embedded engine lands (pager/B-tree/WAL/checkpoint)

| Item | Detail |
|---|---|
| Pass criterion | All 5 engine specs green |
| Command | `bin/simple test test/dbfs/dbfs_engine_pager_spec.spl test/dbfs/dbfs_engine_btree_spec.spl test/dbfs/dbfs_engine_wal_spec.spl test/dbfs/dbfs_engine_checkpoint_spec.spl test/dbfs/dbfs_engine_intent_log_spec.spl test/dbfs/dbfs_engine_checkpoint_ring_spec.spl test/dbfs/dbfs_catalog_schema_spec.spl test/dbfs/dbfs_tx_protocol_spec.spl` |
| Expected | sum of it-blocks = 8+8+8+6+6+6+13+6 = 61 passed, 0 failed |
| Single-cache check | `grep -n 'page_cache\|kernel_page_cache' /home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/db/dbfs_engine/buffer_mgr.spl` — buffer_mgr keys must be `(ino_id, page_id)`, NOT `(device_id, lba)` |
| Negative | If buffer_mgr cross-inserts kernel-cache LBA-keyed entries, AC-3 fails (R4) |

### AC-4 — NVFS pluggable backend

| Item | Detail |
|---|---|
| Pass criterion | `arena_as_blob_backend_spec.spl` (6 it-blocks) and `nvfs_no_regression_spec.spl` (7 it-blocks) green |
| Command | `bin/simple test test/dbfs/arena_as_blob_backend_spec.spl test/dbfs/nvfs_no_regression_spec.spl` |
| Expected | 13 it-blocks pass |
| Structural grep | `grep -n 'trait BlobBackend' /home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/db/` (recursive) — must define a `BlobBackend` trait |
| Negative | Existing NvfsDriver/NvfsPosix specs anywhere in repo must still pass (`bin/simple test test/nvfs/`) — any new red is a regression |

### AC-5 — Crash-safe transactional semantics

| Item | Detail |
|---|---|
| Pass criterion | `dbfs_recovery_spec.spl` (7 it-blocks) green; `dbfs_tx_protocol_spec.spl` (6) green; `dbfs_engine_intent_log_spec.spl` (6) green; `dbfs_engine_checkpoint_ring_spec.spl` (6) green |
| Command | `bin/simple test test/dbfs/dbfs_recovery_spec.spl test/dbfs/dbfs_tx_protocol_spec.spl test/dbfs/dbfs_engine_intent_log_spec.spl test/dbfs/dbfs_engine_checkpoint_ring_spec.spl` |
| Expected | 25 it-blocks pass; AT LEAST 6 fault-injection scenarios from §2 must be exercised |
| Negative | A spec that asserts "uncommitted txn IS visible after mount" — if such an assertion exists, AC-5 fails |

### AC-6 — HW direct accessibility preserved

| Item | Detail |
|---|---|
| Pass criterion | `dbfs_hw_passthrough_spec.spl` (2 it-blocks) green |
| Command | `bin/simple test test/dbfs/dbfs_hw_passthrough_spec.spl` |
| Expected | both it-blocks: (a) non-DBFS driver resolves BlockDevice, (b) DBFS reads through pre-existing BlockDevice via `open_on_device()` |
| Structural grep | `grep -nE 'BlockDevice|open_on_device' /home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/fs_driver/dbfs_stub.spl` |
| Negative | If the spec stubs `BlockDevice` rather than reusing the real driver-manifest path, AC-6 fails |

### AC-7 — FAT32 + boot path intact

| Item | Detail |
|---|---|
| Pass criterion | `fat32_no_regression_spec.spl` (7 it-blocks) green; existing `src/os/kernel/fs` FAT32 specs still green |
| Command | `bin/simple test test/dbfs/fat32_no_regression_spec.spl && bin/simple test src/os/kernel/fs/` |
| Expected | All FAT32 it-blocks pass; mount/readdir/open/read/stat all succeed |
| Structural grep | `grep -nE 'mount_root|/data' /home/ormastes/dev/pub/simple/src/os/services/vfs/vfs_init.spl` — root mount must remain FAT32; DBFS only on `/data` |
| Negative | If vfs_init.spl moves the root to DBFS, AC-7 fails |

### AC-8 — POSIX-compat shim subset

| Item | Detail |
|---|---|
| Pass criterion | `dbfs_posix_shim_spec.spl` (9 it-blocks) green; `dbfs_capability_spec.spl` (11) green |
| Command | `bin/simple test test/dbfs/dbfs_posix_shim_spec.spl test/dbfs/dbfs_capability_spec.spl` |
| Expected | 20 it-blocks pass; specs cover: random-write COW, rename-over-existing, unlink-while-open tombstone, truncate; out-of-scope ops (mmap shared writable, hard links, holes, O_DIRECT, fsync, flock) explicitly absent or asserted unsupported |
| Structural grep | `grep -nE 'MmapSharedWritable|hard_link|fallocate|O_DIRECT' /home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/fs_driver/dbfs_stub.spl` (expect: zero or only-as-explicit-NotSupported) |
| Negative | Any spec asserting `mmap(MAP_SHARED+PROT_WRITE)` works — AC-8 fails (out-of-scope per D10) |

### AC-9 — Test + benchmark coverage

| Item | Detail |
|---|---|
| Pass criterion | All 18 *_spec.spl files green; bench harness smoke green; the four `*_bench.spl` workload files exist and produce timing output |
| Command | `bin/simple test test/dbfs/` (whole directory) |
| Expected | Aggregate ≥120 it-blocks pass per Spec File Inventory; `bench_harness_smoke_spec.spl` 3 it-blocks pass |
| Bench evidence | The four bench files (`metadata_storm_bench.spl`, `append_log_bench.spl`, `random_overwrite_bench.spl`, `mmap_read_bench.spl`) exist under `test/dbfs/bench/` OR alternative location AND emit p50/p99/throughput. Note: `bench_harness.spl` itself is harness-only with 0 it-blocks per the spec corrections — do NOT count it as a spec. |
| Negative | Any green test result with `it-block count = 0` (use silent-green grep §5) falsifies AC-9 |

### AC-10 — Doc + migration plan (DOC-AC)

| Item | Detail |
|---|---|
| Pass criterion | `doc/04_architecture/dbfs_architecture.md` exists and contains: D3 schema (11 tables), D5 recovery (5 steps), D12 risk register (≥13 rows), D10 out-of-scope list, staged-rollout section |
| Command | `grep -cE '^### (INODE|DENTRY|FILE_VERSION|EXTENT_REF|EXTENT|BLOCK_BLOB|XATTR|ACL_ENTRY|TXN|WAL_RECORD|STORAGE_CLASS)' /home/ormastes/dev/pub/simple/doc/04_architecture/dbfs_architecture.md` (expect ≥11) and `grep -c '^| R[0-9]' /home/ormastes/dev/pub/simple/doc/04_architecture/dbfs_architecture.md` (expect ≥13) |
| Expected | counts as above |
| Negative | Missing any of the 11 tables, fewer than 13 risks, or no out-of-scope list — AC-10 fails |

---

## 2. Power-Cut Fault-Injection Scenarios

The 6-step protocol from D4 has **6 inter-step boundaries** plus mid-step fault points. The harness `test/dbfs/power_cut_harness.spl` wraps `Arena` and trips after N writes, returning `Err(IoError::SimulatedPowerCut)`. The decision rule (D5): **a transaction is committed iff a WAL_RECORD with `record_type == COMMIT` for its `txn_id` appears in the WAL at or before the WAL tail LSN.**

| # | Inject point | What lands on disk | Expected mount-time outcome | Spec coverage |
|---|---|---|---|---|
| F1 | Crash between step 1 (data written) ↔ step 2 (private metadata) | data extent blob exists; no EXTENT/BLOCK_BLOB row published; no WAL | Recovery step 4: orphan reclamation calls `arena_discard(blob_handle)` (idempotent). Disk space reclaimed; no namespace effect. | `dbfs_recovery_spec.spl` "orphan reclaim after partial write" |
| F2 | Crash between step 2 ↔ step 3 (private metadata, no WAL) | data blob + dirty private pages (in volatile memory only) | Identical to F1 from on-disk POV — no WAL entries, no published root. Orphan reclamation discards the blob. | `dbfs_recovery_spec.spl` "private pages never persist without WAL" |
| F3 | Crash mid-step-3 (some row-mutation WAL records, NO COMMIT yet) | Partial WAL records on disk; no COMMIT record | Step 3 of recovery: txn has no COMMIT → skipped (treated as uncommitted). All row deltas discarded. | `dbfs_engine_intent_log_spec.spl` "partial txn without COMMIT skipped" |
| F4 | Crash between step-3-COMMIT-buffered and step-4-flush-returns | Indistinguishable from F3 on stable storage. WAL buffer is volatile. | Same as F3: skipped. The durability boundary is `flush()` return. | `dbfs_engine_wal_spec.spl` "durability boundary at flush return" |
| F5 | Crash AFTER step 4 (COMMIT durable) BUT BEFORE step 5 (root publish) | WAL has the COMMIT record before tail; in-memory root not yet swapped | Step 3 of recovery finds COMMIT in WAL → MUST replay row deltas. Txn becomes visible after mount. | `dbfs_recovery_spec.spl` "committed txn visible after crash before root publish" + `dbfs_tx_protocol_spec.spl` |
| F6 | Crash between step 5 ↔ step 6 (root in-memory, not yet visible to readers) | On-disk state identical to F5 (publish is in-memory only until next checkpoint) | Same replay outcome as F5. | `dbfs_recovery_spec.spl` "post-publish-pre-visibility recovers identically" |
| F7 | Crash mid-checkpoint-write to META_DURABLE | CheckpointEntry partially written; CRC fails | Step 2 finds prior-clean entry (newest with valid CRC + clean=true), proceeds from there. | `dbfs_engine_checkpoint_ring_spec.spl` "torn checkpoint entry skipped" |
| F8 | Crash mid-superblock update | Primary superblock corrupt; replicas at offset 1 and end-of-device | Step 1 best-of-3 picks highest `gen` with valid CRC. | `dbfs_recovery_spec.spl` "superblock replica fallback" |

**Falsification:** for any F1–F8, if mount produces `committed_txns_visible == false` for an F5/F6 case, OR `uncommitted_txns_visible == true` for an F1–F4 case, recovery is broken.

**Verification command:**
```bash
bin/simple test test/dbfs/power_cut_harness.spl  # harness sanity (0 it-blocks but must compile)
bin/simple test test/dbfs/dbfs_recovery_spec.spl test/dbfs/dbfs_engine_intent_log_spec.spl test/dbfs/dbfs_engine_checkpoint_ring_spec.spl
```

---

## 3. Performance Benchmark Plan

Bench harness lives at `test/dbfs/bench_harness.spl` (shared infra, 0 it-blocks), driven by four workload specs. Pass criteria are **ratios** (environment-independent), not absolute thresholds.

### 3.1 Workload definitions

| Workload | Operation | Volume | Output metrics |
|---|---|---|---|
| metadata_storm | 10K `mkdir`+`stat` ops on fresh mount | 10 000 ops | p50, p99 latency (ms); ops/sec |
| append_log | sequential `append` to one file | 1 GiB total, 64 KiB chunks | throughput (MB/s) |
| random_overwrite | random 4 KiB pwrite on 1 GiB file | 100 000 writes | IOPS; p99 latency |
| mmap_read | sequential read via `readv` (DBFS doesn't support mmap shared-write per D10; this is read-mostly) | 1 GiB | throughput (MB/s) |

### 3.2 Comparison matrix

For each workload × {DBFS-on-RawNvme, DBFS-on-NVFS-arena, FAT32, RamFS, NVFS-native}:

| Workload | Metric | DBFS-RawNvme | DBFS-NvfsArena | FAT32 | RamFS | NVFS-native | Pass criterion |
|---|---|---|---|---|---|---|---|
| metadata_storm | p99 (ms) | A | B | C | D (ref) | E | A ≤ 2.0 × C (DBFS p99 within 2x FAT32) |
| append_log | MB/s | A | B | C | D | E | A ≥ 0.3 × D (within 30% of RamFS upper bound) |
| random_overwrite | IOPS | A | B | C | D | E | A ≥ 0.5 × E (NVFS-native is closest peer) |
| mmap_read | MB/s | A | B | C | D | E | A ≥ 0.5 × C (FAT32 read path baseline) |

### 3.3 Run command

```bash
bin/simple test test/dbfs/bench_harness_smoke_spec.spl    # smoke: 3 it-blocks
# Workload runs (location to confirm; D11 lists test/dbfs/bench/, current tree may have flat layout):
bin/simple test test/dbfs/bench/metadata_storm_bench.spl 2>/dev/null || \
  bin/simple test test/dbfs/metadata_storm_bench.spl
# repeat for append_log_bench, random_overwrite_bench, mmap_read_bench
```

### 3.4 Falsification

- DBFS metadata p99 > 2× FAT32 p99 → R5 (COW amplification) suspected; capture for follow-up
- DBFS throughput drops >50% between RawNvme and NvfsArena backends → BlobBackend abstraction has a hidden cost
- Bench process dies before printing metrics → harness regression, fail Phase 7

---

## 4. Non-Regression Checklist

Confirm no behavioral drift in non-DBFS file systems. Each grep below should produce a finite, expected list — Phase 7 records the count and diffs against pre-Phase-5 baseline (use `jj op log`/`git log -S` to find the prior commit).

| Target | Command | Expected |
|---|---|---|
| DriverInstance enum | `grep -nE 'enum DriverInstance|DbFs\\(|Fat32\\(|Nvfs\\(|RamFs\\(' /home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/fs_driver/instance.spl` | All 4+1 variants present; `DbFs` is the only addition |
| Exhaustive matches | `grep -RnE 'match .*: DriverInstance|match driver' /home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/fs_driver/ /home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/driver/` | Every match site has a `DbFs` arm; compiler exhaustive-match enforcement should be the witness |
| Public exports | `grep -n 'DbFsDriver' /home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/fs_driver/__init__.spl` | exported |
| FAT32 driver | `bin/simple test src/os/kernel/fs/` | All previously-passing FAT32 specs still pass |
| RamFS | `bin/simple test test/ramfs/` (if present) or `grep -Rn 'RamFs' src/lib/nogc_sync_mut/fs_driver/` | No call-site changes beyond match-arm completion |
| NVFS public API | `bin/simple test test/nvfs/` | All previously-passing NVFS specs still pass |
| VFS init | `grep -nE '/data|/|mount_root' /home/ormastes/dev/pub/simple/src/os/services/vfs/vfs_init.spl` | Root remains FAT32; `/data` is the DBFS mount |
| Driver-manifest | `grep -Rn 'driver_manifest\|BlockDevice' /home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/fs_driver/dbfs_stub.spl` | DBFS plugs in via existing manifest path; no new bypass |

---

## 5. Silent-Green Detector

Per `feedback_compile_mode_false_greens` and `feedback_no_coverups`. Run each grep; **any hit is a Phase 7 fail until justified**.

```bash
SCOPE='/home/ormastes/dev/pub/simple/test/dbfs /home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/db /home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/fs_driver'

# 5.1 skip() in DBFS specs
grep -RnE '\bskip\(' $SCOPE

# 5.2 it-blocks with no expect()
grep -RnPzo 'it\s+"[^"]*"\s*\{[^}]*\}' $SCOPE | grep -v 'expect('

# 5.3 Tautological assertions
grep -RnE 'expect\(true\)\.to_equal\(true\)|expect\(0\)\.to_equal\(0\)|expect\(\[\]\)\.to_equal\(\[\]\)' $SCOPE

# 5.4 Stub returns in impl files
grep -RnE 'Result\.Ok\(0\)|Ok\(\(\)\)\s*//\s*TODO|return Ok\(\)\s*$' /home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/db/

# 5.5 TODO/FIXME within 5 lines of an expect()
grep -RnB5 'expect\(' $SCOPE | grep -E 'TODO|FIXME|XXX'

# 5.6 Compile-mode escapes
grep -RnE '\-\-mode=(native|smf)' $SCOPE /home/ormastes/dev/pub/simple/.sstack/dbfs-integration/

# 5.7 describe with zero it
grep -RnPzo 'describe\s+"[^"]*"\s*\{[^}]*\}' $SCOPE | awk '/describe/{d=1; c=0} /it /{c++} /^---/{if(d && c==0) print; d=0; c=0}'

# 5.8 Vacuous matchers
grep -RnE 'to_be_truthy\(\)|to_not_throw\(\)' $SCOPE

# 5.9 Weakened/edited assertions vs pre-Phase-5
git log -p -S'expect(' -- test/dbfs/ | grep -E '^-.*expect\(.*to_equal'   # removed expect lines

# 5.10 Specs that pass with 0 examples
bin/simple test test/dbfs/ 2>&1 | grep -E 'examples: 0|0 examples'

# 5.11 Capability tautology (per spec correction precedent)
grep -RnE 'caps\.has\([A-Za-z_]+\)\.to_equal\(true\)' $SCOPE | xargs -I{} echo {} | grep -v 'PosixCompat\|COW\|Xattr\|Acl\|LargeFiles'
```

Any hit on 5.1–5.11 produces a finding line in `state.md > 7-verify` with file:line and a remediation entry.

---

## 6. Risk-to-Evidence Map (D12, 13 risks)

For each of the 13 risks in `doc/04_architecture/dbfs_architecture.md > D12`, Phase 7 confirms the mitigation by the listed evidence. If evidence is missing, Phase 7 fails (do not silently advance).

| # | Risk | Mitigation evidence Phase 7 must produce |
|---|---|---|
| R1 | Intent-log persistence gap (HIGH) | (a) `bin/simple test test/dbfs/dbfs_engine_intent_log_spec.spl` ⇒ 6 pass; (b) `grep -nE 'arena_append.*DB_WAL|wal_handle' src/lib/nogc_sync_mut/db/dbfs_engine/intent_log.spl` shows actual durable append (not memory-only); (c) state.md no longer flags "Phase 5 prerequisite: intent_log.spl must persist" |
| R2 | Checkpoint-ring persistence gap (HIGH) | (a) `bin/simple test test/dbfs/dbfs_engine_checkpoint_ring_spec.spl` ⇒ 6 pass; (b) `grep -nE 'arena_append.*META_DURABLE' src/lib/nogc_sync_mut/db/dbfs_engine/checkpoint_ring.spl`; (c) `dbfs_recovery_spec.spl` "post-crash ring scan" passes |
| R3 | Double journaling (DBFS WAL + NVMe FTL) | `grep -nE 'DURABLE_GROUP_COMMIT' src/lib/nogc_sync_mut/db/dbfs_engine/intent_log.spl` shows one flush per commit (not per record); AC-10 doc has explicit subsection on no-per-record-fsync |
| R4 | Double cache (DBFS buffer + kernel page cache) | `grep -n 'page_id\|ino_id' src/lib/nogc_sync_mut/db/dbfs_engine/buffer_mgr.spl` (DBFS keys); `grep -n 'lba\|device_id' src/os/kernel/cache/` (kernel keys); confirm zero cross-import. Pager spec asserts no LBA-keyed insert in DBFS buffer manager. |
| R5 | Large-file random overwrite COW amplification | `random_overwrite_bench.spl` produces IOPS; vacuum/coalesce code path exists: `grep -Rn 'extent_coalesc\|vacuum' src/lib/nogc_sync_mut/db/dbfs_engine/` |
| R6 | Namespace B-tree key generalization mismatch | `dbfs_engine_btree_spec.spl` 8 it-blocks pass and cover insert/lookup/delete/range with `Ino`/`DirEntryKey`; structural `pmap_btree` copy verified by `diff` against `examples/nvfs/src/core/pmap_btree.spl` (only key type changed) |
| R7 | Power-cut harness complexity | F1–F8 of §2 all green; `power_cut_harness.spl` compiles and is referenced by `dbfs_recovery_spec.spl` |
| R8 | simple_db_if Rel/BlkNo coupling leak | `grep -Rn 'use .*simple_db' src/lib/nogc_sync_mut/db/dbfs_engine/` ⇒ ZERO matches; DbFsEngine defines own `Ino`/`DirEntryKey` (verify via `grep -n 'Ino\b\|DirEntryKey' src/lib/nogc_sync_mut/db/dbfs_engine/schema.spl`) |
| R9 | Recovery bugs in orphan reclamation | `dbfs_recovery_spec.spl` includes "no false-positive discard" assertion; `arena_discard` idempotency test in `dbfs_engine_intent_log_spec.spl` or `dbfs_engine_pager_spec.spl` |
| R10 | jj submodule gitlink flip | `git ls-tree HEAD -- src/lib/nogc_sync_mut/db/dbfs_engine/` shows expected mode; no `.gitmodules` regression. Verified by Phase 8 ship gate, Phase 7 records current state. |
| R11 | rt_* extern bootstrap rebuild | If new `rt_*` extern was added (grep for it), confirm `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` was run (check `doc/08_tracking/build/recent_build.md`). If no new extern, R11 is N/A — document that. |
| R12 | Scope creep (distributed NVFS, xfstests, mmap) | `grep -RnE 'mmap.*MAP_SHARED.*PROT_WRITE|xfstests|distributed_nvfs' src/lib/nogc_sync_mut/db/ test/dbfs/` ⇒ ZERO matches |
| R13 | Submodule race with parallel /dev | Verify only one /dev track ran during Phase 5; check `git log --oneline -20` for non-DBFS commits interleaved during the DBFS implementation window. If interleaving present, scan for gitlink-as-tree at `src/lib/nogc_sync_mut/db/`. |

**Risk-count sanity:** `grep -c '^| R[0-9]' doc/04_architecture/dbfs_architecture.md` must equal **13**. If `state.md > D12` references a different count, flag the discrepancy.

---

## 7. Phase 7 Sign-off Checklist

Phase 7 is complete when ALL boxes below are checked in `state.md > 7-verify`:

- [ ] §0 preamble: 0 compile-mode hits, spec count matches
- [ ] §1 AC-1 through AC-10: each AC has command run + expected output captured + negative test result documented
- [ ] §2 power-cut: F1–F8 outcomes recorded
- [ ] §3 bench: comparison matrix filled with measured ratios; pass criteria evaluated
- [ ] §4 non-regression: every grep run, counts captured, FAT32/NVFS/RamFS specs still green
- [ ] §5 silent-green: every pattern grepped; zero unjustified hits
- [ ] §6 risk-to-evidence: each of R1–R13 has one concrete evidence line; risk count = 13 confirmed
- [ ] Phase-5 prerequisite flags in `state.md` cleared (intent_log + checkpoint_ring persistence)

If any box is unchecked, route back to Phase 5/6 with a concrete fix request. Do NOT mark Phase 7 done with skips, weakened assertions, or TODO→NOTE conversions (per `feedback_no_coverups`).
