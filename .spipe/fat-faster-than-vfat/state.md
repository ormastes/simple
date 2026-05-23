# SStack State: fat-faster-than-vfat

## User Request
> make simple fat faster than vfat

## Task Type
feature

## Refined Goal
> Add caching layers to Simple's FAT32 driver to beat Linux VFAT on metadata and read/write workloads. The driver already avoids kernel VFS/syscall overhead (runs in-process). Adding directory entry cache, cluster chain cache, and FAT sector cache will eliminate redundant I/O — the main bottleneck.
>
> **W1 — FAT Sector Cache:** Cache last N FAT sectors in memory to avoid per-entry I/O on `read_fat_entry()`/`write_fat_entry()`.
>
> **W2 — Cluster Chain Cache:** Cache resolved cluster chains per file handle so sequential read/write doesn't re-walk FAT from cluster 0.
>
> **W3 — Directory Entry Cache:** LRU cache mapping `(parent_cluster, name) → entry` to avoid re-reading directory clusters on repeated path lookups.
>
> **W4 — Benchmark:** Profile FAT32 before/after caching, compare against Linux VFAT reference numbers.

## Acceptance Criteria
- [ ] AC-1: FAT sector cache — `read_fat_entry` hits in-memory cache instead of `read_sector` on repeated access
- [ ] AC-2: Cluster chain cache — `read()`/`write()` use cached chain, no FAT re-walk after first access
- [ ] AC-3: Directory entry cache — `resolve_path` for repeated paths hits cache, no directory cluster re-read
- [ ] AC-4: Cache invalidation on mutation (mkdir, unlink, truncate, write-extend)
- [ ] AC-5: Benchmark: FAT32 metadata ops (open+stat+close) < 50µs avg in compiled mode (VFAT reference: 5-50µs cached)
- [ ] AC-6: No regression — existing fs_hardening_spec.spl passes 15/15

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-23
- [ ] 2-research (Analyst)
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev

**Task type:** feature (performance optimization)

**Research findings:**

1. **FAT32 driver is pure Simple** (0 C externs, 1163 LOC, 34 functions). All hot paths are interpreter/compiled code.

2. **Top 3 bottlenecks** (all I/O related, not CPU):
   - Directory entry lookup: O(n) linear scan per `find_entry_in_dir()`, no caching. Each path component re-reads directory clusters.
   - Cluster chain walking: `read()`/`write()` re-walk FAT from cluster 0 on every access. No chain caching.
   - FAT table reads: `read_fat_entry()` does a `read_sector()` for every single 4-byte lookup. No sector caching.

3. **Linux VFAT advantages** (what we need to match):
   - dcache: `(inode, name) → inode` mapping avoids directory re-reads
   - buffer cache: FAT sectors stay in memory (4-8 sectors, ~4KB)
   - cluster chain cache: resolved chains stored per open file

4. **Simple's advantages** (what makes beating VFAT possible):
   - No syscall overhead (in-process, userspace)
   - No VFS layer traversal
   - No kernel lock contention
   - Direct memory access to cached data (no copy_to_user)

5. **Expected impact:** Cache + no-syscall = 70%+ speedup on directory-heavy workloads. Target: <50µs metadata ops (VFAT is 5-50µs cached but includes syscall overhead).

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
