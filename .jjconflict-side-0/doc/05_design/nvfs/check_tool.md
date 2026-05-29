# NVFS N8 — Offline Integrity Audit Tool (`nvfs_check`)

**Status:** Skeleton implemented (FR-NVFS-N8-001).  Full walker deferred (FR-NVFS-N8-002).
**Reference tools:** `btrfs-check`, `zpool scrub`, `fsck.ext4`.
**Source:** `examples/nvfs/src/tool/nvfs_check.spl`
**Tests:** `examples/nvfs/test/unit/tool/nvfs_check_test.spl`

---

## 1. Motivation

N4a/N4b provide *online* scrub (periodic, inline, repair-on-read).  They walk
the pmap sidecar while the volume is mounted and repair from reflink peers.
What is missing is an *offline* audit that:

- walks the full on-disk structure without the driver in the loop,
- detects structural inconsistencies that the online scrub cannot see (orphaned
  extents, checkpoint ring gaps, refcount mismatches), and
- exits with a machine-readable report so scripts can alert on problems.

`nvfs_check` fills this gap.  It is run against an unmounted volume (or a
snapshot), similar to `btrfs-check --readonly` or `zfs scrub` on an exported
pool.

---

## 2. CLI

```
nvfs_check [--verbose] [--checksums] [--refcount] <path>
```

| Flag | Default | Meaning |
|------|---------|---------|
| `--verbose` | off | Print per-entry progress lines |
| `--checksums` | off | Phase 3: re-verify extent checksums (slow) |
| `--refcount` | off | Phase 4: full reflink refcount audit |

Exit codes:

| Code | Meaning |
|------|---------|
| 0 | Clean — no warnings, no errors |
| 1 | Warnings only — volume is healthy but has minor anomalies |
| 2 | Errors — volume has structural problems; mount with caution |
| 3 | Fatal — do not mount; immediate backup + repair required |

---

## 3. Check Phases

Phases run in order 1–5.  Each phase returns an updated `CheckReport`.

### Phase 1 — Superblock replicas

Walk each of the N superblock replicas stored at fixed offsets on the device.

**Checks:**
- Magic bytes match `b"NVFS0002"` (v2) or `b"NVFS0003"` (v3).
- CRC32C of each replica verifies against the stored checksum field.
- Generation counters are monotonically non-decreasing across replicas.
- A replica whose generation lags the most-recent by more than 1 → WARN.
- A replica with a bad checksum → ERROR.

**Key invariant:** at least one replica must be clean to attempt recovery.  If
all replicas are bad → FATAL.

### Phase 2 — Checkpoint ring

Walk every slot in the checkpoint ring (`checkpoint.spl`).

**Checks:**
- Per-slot CRC32C verifies.
- Generation numbers are gapless and monotonically increasing within the ring.
- Most-recent slot's `last_checkpoint_gen` matches the superblock field.
- Slot arena_ids are present in the live arena table (derived from phase 1
  superblock's `arena_table_root` pointer).
- A slot referencing an unknown arena → ERROR "checkpoint references unknown arena".
- A wrap-around gap (newest_gen > oldest_gen + ring_capacity) → WARN.

### Phase 3 — pmap B-tree

Walk every entry in the pmap B-tree (`pmap_btree.spl`).

**Checks:**
- Each `(arena_id, offset)` key falls within a live arena's byte range.
- If `--checksums`: re-read extent bytes from the arena buffer and verify the
  stored checksum (same logic as N4a scrub, but offline).
- Orphaned extent: `arena_id` present in pmap but absent from the live arena
  table → ERROR "orphaned pmap extent".
- Unreachable entry: `logical_page_no` not reachable from any inode tree →
  WARN "unreachable pmap entry" (may be a harmless COW remnant pending GC).

**Performance note:** full checksum re-verification (`--checksums`) reads every
extent from the device.  On a 10 TB volume this can take hours; the flag is
opt-in.

### Phase 4 — Reflink refcount table

Only runs when `--refcount` is passed.

**Checks:**
- For every entry in the reflink table, count actual back-references in the
  pmap B-tree that share the same `logical_page_no`.
- Stored refcount == actual back-refs → OK.
- Mismatch by 1 → WARN "refcount off-by-one" (likely a COW race that did not
  commit).
- Mismatch by > 1 → ERROR "refcount mismatch: stored N actual M".
- Stored refcount == 0 and entry not freed → WARN "dangling reflink entry".

**Algorithm (N8-full):** build an in-memory `(logical_page_no → count)` map via
a full pmap B-tree walk (O(n) in entries), then compare against the reflink
table in a single pass.

### Phase 5 — Intent-log tail

Walk WAL/intent-log records from the tail pointer back to the last checkpointed
LSN (`intent_log.spl`).

**Checks:**
- Per-record CRC32C verifies.
- LSNs are monotonically increasing within the tail window.
- A record referencing an unknown `arena_id` → ERROR "intent-log references
  unknown arena".
- A record with LSN ≤ `checkpoint_lsn` from phase 2 → WARN "replayed record
  in intent-log tail" (harmless if recovery skips it, but indicates a truncation
  bug if frequent).

---

## 4. Report Format

`check_report_pretty` emits a JSON-like structured string:

```
{ "clean": false, "info": 0, "warn": 2, "error": 1, "fatal": 0,
  "issues": [
    { "severity": "WARN", "phase": 3, "message": "orphaned pmap extent at arena_id=7 offset=4096" },
    { "severity": "WARN", "phase": 4, "message": "refcount off-by-one: logical_page_no=42" },
    { "severity": "ERROR", "phase": 4, "message": "refcount mismatch: stored 3 actual 1" }
  ] }
```

Severity tiers in order of increasing gravity: INFO < WARN < ERROR < FATAL.

The `issues` list is capped at a configurable sample size in the full
implementation (default 1 000 entries) to keep the report bounded.  Total
counts are always accurate.

---

## 5. Skeleton vs Full Implementation

| Capability | Skeleton (N8-001) | Full (N8-002) |
|------------|-------------------|---------------|
| NvfsCheckOpts struct | yes | yes |
| CheckReport + pretty-print | yes | yes |
| Phase dispatcher (5 stubs) | yes (pass_todo) | yes (real walkers) |
| Superblock replica walk | stub | real |
| Checkpoint ring walk | stub | real |
| pmap B-tree walk | stub | real |
| Checksum re-verification | stub | real |
| Reflink refcount audit | stub | real |
| Intent-log tail walk | stub | real |
| Synthetic corruption tests | 3 structural only | full |

---

## 6. Open Questions

- **OQ-N8-1:** Should `nvfs_check --repair` invoke `scrub_repair_block` (N4a)
  inline, making it a combined offline scrub + check?  Risk: repair modifies the
  device.  Recommendation: keep check read-only; add a separate `nvfs_repair`
  tool for N9+.
- **OQ-N8-2:** Should the intent-log tail walk attempt replay simulation to
  verify idempotency?  That crosses into `nvfs_recover` territory.
- **OQ-N8-3:** Large volumes need streaming output (JSONL, one issue per line)
  rather than a single JSON blob.  Full impl should support `--output=jsonl`.
