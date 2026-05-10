# DBFS Integration — Migration & Rollback Playbook

**Feature:** `dbfs-integration` (SStack)
**Phase:** Phase 8 (Ship) precursor — operator runbook for v1 delivery
**Status:** Authoritative for the v1 cut where FAT32 stays the boot/root FS and DBFS mounts on `/data`
**Companion docs:** `state.md`, `arch/codex_design.md`, `verify_plan.md`, `risk_premortem.md`, `doc/04_architecture/dbfs_architecture.md` (D1–D12), `ship_plan.md` (forthcoming Phase 8)
**Architecture decisions cited:** D3 (schema), D4 (tx write protocol), D5 (recovery), D7 (FsDriver seam, MountTable), D9 (build flag), D10 (POSIX shim out-of-scope list)

This playbook is operator-facing. It does not replace the architecture doc. If a step here disagrees with `dbfs_architecture.md` D-decisions, the architecture doc wins and this file is wrong — file a follow-up.

---

## 1. First-Mount / Format Flow (new DBFS volume)

A fresh DBFS volume must end with a published clean checkpoint (mount-generation `gen=1`) and three valid superblock replicas before the FsDriver layer will mount it.

### 1.1 Sequence (matches D4 write protocol applied to an empty volume)

| # | Step | Description | Spec witness |
|---|---|---|---|
| a | Prepare backing | Reserve either an NVMe LBA range (real device, see `vfs_init.spl` NVMe path) or an NVFS arena via the `Arena` trait (`std.storage.arena`). Volume size must be ≥ checkpoint-ring (4096 slots × slot size) + 3× superblock replicas + minimum WAL window. | `arena_as_blob_backend_spec.spl` |
| b | Initialise three superblock replicas | Write replica 0/1/2 with `gen=1`, valid CRC, pointers to empty checkpoint ring head and empty intent-log. Best-of-3 selection at mount picks the highest valid `gen`. | `dbfs_recovery_spec.spl` — "picks replica with highest valid gen", "skips replica with invalid CRC" |
| c | Initialise checkpoint ring | Allocate the 4096-slot ring; write slot 0 with `generation=1`, `superblock_lba` → replica 0, `intent_log_head=0`, `root_pmap_record_lba=<empty namespace root>`. | `dbfs_engine_checkpoint_ring_spec.spl`, `dbfs_engine_checkpoint_spec.spl` |
| d | Write empty namespace tree | Empty INODE table containing only the root inode (mode=040755, link_count=2). Empty DENTRY, FILE_VERSION, EXTENT_REF, EXTENT, BLOCK_BLOB, XATTR, ACL_ENTRY tables. Static STORAGE_CLASS rows (6) per D3. | `dbfs_catalog_schema_spec.spl`, `dbfs_engine_btree_spec.spl` |
| e | Publish first clean mount-generation | After (b)–(d) durable, write checkpoint slot 1 with `generation=2`, `clean=true`. This is the mount-generation that recovery treats as the volume's anchor. | `dbfs_recovery_spec.spl` — "recovery writes a new clean checkpoint slot" |

### 1.2 Binary command(s)

**No CLI yet — Phase 5 delivered programmatic constructors only.**

In v1, a fresh volume is produced by `DbFsDriver.new_hosted()` (in-memory) or by the lower-level `DbFsEngine.format(arena, opts)` entry point used inside Simple test harnesses. There is no `mkfs.dbfs` binary.

**Follow-up TODO (Phase 9 / post-ship):**
- `bin/simple dbfs format --backend=<nvme|nvfs-arena> --device=<path|lba-range> [--size=<bytes>]`
- `bin/simple dbfs mkfs <device>` POSIX-style alias
- Both must drive steps (a)–(e) above, fsync between (d) and (e), and exit non-zero on partial completion.

Until that lands, formatting from userland is not supported; DBFS volumes are produced inside the kernel mount path or by a test fixture.

---

## 2. Mount / Unmount Flow

DBFS adds itself as a fifth `DriverInstance` variant (`DbFs(driver: DbFsDriver)`) per D7. The `MountTable` itself is unchanged — DBFS plugs in via the existing seam.

### 2.1 Mount

```text
# Conceptual — pure Simple, executed by VFS init or admin tool
val dbfs   = DbFsDriver.new(block_dev_or_arena, opts)
val mt_id  = MountTable.mount("/data", DriverInstance.DbFs(dbfs), opts)
```

- Source: `src/lib/nogc_sync_mut/fs_driver/mount_table.spl` (`mount` function — see file header §3, §8).
- `DriverInstance.DbFs` variant: `src/lib/nogc_sync_mut/fs_driver/instance.spl`.
- VFS wiring path: `src/os/services/vfs/vfs_init.spl` keeps FAT32 at `/` and adds DBFS at `/data`. AC-7 in `verify_plan.md` enforces this — root must NOT move to DBFS.
- Spec witness: `mount_table_dbfs_dispatch_spec.spl` (longest-prefix dispatch routes `/data/...` to DBFS); `fat32_no_regression_spec.spl` it-block "FAT32 and DBFS can both be mounted simultaneously".

### 2.2 Mount-time recovery (every mount, dirty or clean)

Per D5 the engine runs the 5-step recovery on every mount, not only after dirty unmount. The five steps:

1. **Best-of-3 superblock pick** — highest `gen` with valid CRC; partially-written replicas rejected.
2. **Checkpoint-ring scan** — find latest clean entry; if none, fall back to last valid entry.
3. **WAL replay from `intent_log_head`** — only records with a `WAL_RECORD_COMMIT` are replayed; uncommitted records are discarded.
4. **Orphan reclamation** — orphan arenas (data written but never referenced by a committed metadata page) are discarded via `arena_discard` (idempotent).
5. **Publish clean mount generation** — increments `gen`, writes a fresh clean checkpoint slot, then `mount()` returns.

Spec witness: `test/dbfs/dbfs_recovery_spec.spl` (covers all five steps).

### 2.3 Unmount

```text
MountTable.unmount("/data").unwrap()
```

- Returns `FsError.NotFound` if no mount at exactly that path; returns `FsError.Busy` if open handles exist.
- Clean unmount = engine flushes pending WAL, writes a final `clean=true` checkpoint slot, then mount-table removal.
- Dirty unmount (crash, force-unmount, OOM-kill) = no `clean=true` slot. Next mount enters the D5 recovery path.

---

## 3. FAT32 → DBFS Data Migration

### 3.1 Is automated migration provided?

**No.** The v1 delivery does not ship a FAT32→DBFS migrator. There is no in-place conversion (file formats are wholly different — FAT cluster chains vs. DBFS EXTENT_REF/BLOCK_BLOB), and there is no batch tool.

### 3.2 Manual workflow (recommended)

1. Boot to FAT32 root (default).
2. Create + format a `/data` DBFS volume per §1 of this doc.
3. Mount DBFS at `/data` per §2.1.
4. From the FAT32 mount, copy desired user data into DBFS:
   ```
   cp -r /home/<user>/  /data/home/<user>/
   ```
   This uses POSIX `open`/`read`/`write`/`mkdir` calls that DBFS's POSIX shim implements (D10 in-scope set).
5. Optionally `sync` and verify file count + a sample checksum on the DBFS side.

The FAT32 read path is unaffected — `fat32_no_regression_spec.spl` it-blocks "FAT32 volume mounts without error", "stat on FAT32 root returns is_dir=true", "readdir on FAT32 root returns a stable empty-or-better listing", and "open on a FAT32 path returns a valid shim handle" all pass post-merge per AC-7.

### 3.3 Data types that may not survive the copy

All of the following are **out of scope for DBFS v1 per D10** — `cp -r` will fail or silently reduce them:

| Data type | What `cp -r` does | Why |
|---|---|---|
| Sparse files (holes) | Copies as fully-allocated zero runs | D10 marks holes out of scope; DBFS will materialise zeros |
| Hard links | Copied as duplicate independent files | D10 marks hard links out of scope; DBFS POSIX shim has no `link()` (returns `Unsupported`) |
| Shared-writable mmap-backed files | Copy works, but downstream `mmap(MAP_SHARED, PROT_WRITE)` will fail on DBFS | D10 out-of-scope; DBFS returns `Unsupported` |
| `O_DIRECT`-only files | Copy works (FAT32 source side); reopens with `O_DIRECT` on DBFS will fail | D10 out-of-scope |
| Per-file `fsync` semantics | DBFS commits at txn boundary, not per-file | D10 out-of-scope; not a data loss issue, behavioural difference only |
| `flock` locks | Not copied (locks are runtime-only anyway) | D10 out-of-scope |

Sparse files and hard links are also out-of-scope on the *source* FAT32 path in this codebase, so the realistic loss is small. Document any of these in a Phase 9 follow-up if user data hits them.

---

## 4. Rollback — Soft (volume-level)

Use this when DBFS is suspected of corruption, when a Phase 7 blocker surfaces post-deployment (R7 recovery bug class, R5 COW amplification, R13 BlobBackend conformance miss), or when an operator needs to take `/data` out of service without rebuilding the OS.

### 4.1 Detach DBFS, fall back to FAT32 or RamFS at `/data`

1. **Stop writers** (best-effort): kill / quiesce any process holding open handles under `/data`. Required because `unmount` returns `FsError.Busy` while handles are open.
2. **Force unmount if needed:** `MountTable.unmount("/data")`. If this returns `Busy`, escalate to a kernel-side force-detach path (Phase 9 follow-up — currently no force flag).
3. **Quarantine the DBFS backing storage** (see §4.2 below) — do this *before* mounting anything else at `/data`.
4. **Mount RamFS at `/data` for continued operation:**
   ```text
   val ramfs = RamFsDriver.new()
   MountTable.mount("/data", DriverInstance.RamFs(ramfs), MountOptions.read_write())
   ```
   RamFS is volatile but unblocks userland that hard-codes `/data` paths. FAT32 over a separate partition is also a valid replacement if one is provisioned.

### 4.2 Preserve the corrupted DBFS volume for forensics

DBFS is single-cache discipline (per D4/D8) — there is no buffered state to lose once unmounted. Forensics requires only the raw backing.

| Backing | Preservation step |
|---|---|
| NVMe LBA range | `dd` (or pure-Simple equivalent) the LBA range to a separate file, including all 3 superblock replicas + checkpoint ring + WAL window + namespace pages. Hash the dump (SHA-256). |
| NVFS arena | Use `arena_export` (Phase 9 follow-up if not present — currently the arena's underlying bytes can be read via the BlobBackend trait `arena_as_blob_backend_spec.spl` exercises). |

Tag the dump with: timestamp, last clean `mount_gen` (read from checkpoint ring slot N), the symptom (`FsError` variant + which spec was failing), and the DBFS commit SHA in use.

### 4.3 What state the rest of the OS goes into

- **Root `/` (FAT32):** unaffected. Boot, kernel, drivers, and user binaries continue serving from FAT32.
- **`/boot` (FAT32, read-only):** unaffected.
- **VFS dispatch:** longest-prefix-match in `MountTable.lookup_text` resolves `/data/...` to whatever is now mounted there (RamFS or FAT32 or nothing). If nothing is mounted at `/data`, paths under `/data` resolve via the longest remaining prefix — which is `/` (FAT32) — and will return `FsError.NotFound` for any path that wasn't on the FAT32 tree.
- **Open handles previously held against DBFS:** invalidated. Future I/O on those handles returns `FsError.NotFound` or `FsError.IoError` (the exact variant depends on whether the handle table entry survives — see §7 below).
- **No automatic kernel reboot is required.** `MountTable` is in-memory state; mount/unmount is a runtime operation.

### 4.4 Soft-rollback safety analysis (the question the advisor would ask)

> *Could a half-completed migration leave the system unbootable?*

**Answer: No, provided the operator does not move the root mount and does not write to FAT32 areas under DBFS control.**

Concretely:
- The root mount point stays FAT32 at all times (AC-7, structural grep in `verify_plan.md` §4). The kernel boot path (`vfs_init.spl` → NVMe → FAT32 BPB → `/` mount) does not touch DBFS at all.
- DBFS lives only at `/data`. If `/data` is detached and replaced with RamFS or left unmounted, boot still succeeds because the boot loader, kernel, and userland binaries are reached via `/` (FAT32).
- The only way a half-completed migration could brick boot is if an operator manually copied `/boot` or `/` contents *into* DBFS and then deleted the FAT32 originals. **DO NOT DO THIS.** The migration workflow in §3.2 explicitly only moves user data under `/data/home/...`. Encode this as a hard rule in the operator runbook.
- Detach is idempotent: an interrupted detach (power loss between unmount and remount) leaves either DBFS still mounted (recovery path engages on next boot) or `/data` empty; both are bootable.

**Verdict: safe.** Soft rollback is bounded, reversible, and cannot affect the boot chain as long as the FAT32 root and `/boot` invariant holds.

---

## 5. Rollback — Hard (code revert)

Hard rollback is the operational lever covered in `ship_plan.md` (Phase 8 deliverable). This section documents only the **operational impact** of executing it, not the procedure.

### 5.1 Trigger conditions

- Phase 7 verification or post-merge fault-injection finds a recovery bug (R7) or correctness failure that cannot be contained by soft rollback.
- A regression in non-DBFS callers (R6 scope creep, exhaustive-match miss in driver dispatch).
- Compile-mode false-green (R11) reveals shipping behaviour diverged from interpreter-mode tests.

### 5.2 What `git revert <DBFS_commits>` does to existing DBFS volumes

1. **The volume's bytes are not touched.** A code revert only removes Simple sources; the on-disk format (D3 schema, superblock replicas, checkpoint ring, WAL) persists.
2. **The post-revert kernel cannot mount it.** `DriverInstance::DbFs` no longer exists in the enum, `DbFsDriver` no longer exists in `std.db`, and any `MountTable.mount("/data", DriverInstance.DbFs(...), ...)` call site is gone (or never compiled in pre-DBFS sources).
3. **Implication:** the volume becomes opaque storage. The bytes can be `dd`-recovered or imported into a future build that reintroduces the DBFS code path, but no live system after the revert can read them.

### 5.3 Will old `bin/simple` builds compile against pre-DBFS sources?

**Yes.** The DBFS commits are additive at the FsDriver seam (per Stream B research):
- `instance.spl` adds `DbFs(...)` variant — `git revert` removes it.
- Every exhaustive-match site in driver/VFS code added a `DbFs` arm — revert removes those arms; the remaining arms still cover `Fat32 | Nvfs | NvfsPosix | RamFs`, which is what pre-DBFS sources expect.
- New files (`std.db.dbfs_engine.*`, `std.db.dbfs_driver`, `dbfs_stub.spl`) are revert-deleted; nothing pre-DBFS imports them.
- Specs under `test/dbfs/` are revert-deleted; the test runner sees fewer specs.

The bootstrap chain (Rust seed → Simple compiler → self-hosted) is untouched by DBFS; no extern additions in this delivery (per Phase 5 "No New rt_* Externs Added" note in `state.md`). `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` after revert produces a working pre-DBFS `bin/simple` (verified by R10 risk register entry — extern bootstrap rebuild is a no-op in the revert direction).

### 5.4 Operational checklist after hard revert

1. Quarantine `/data` DBFS bytes per §4.2 — they are now unreadable until a re-introduction lands.
2. Re-bootstrap: `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`.
3. Re-run `bin/simple test src/os/kernel/fs/` and `bin/simple test test/ramfs/` (if present) to confirm non-DBFS FS paths still green.
4. Mount RamFS or a separate FAT32 partition at `/data` if userland needs that path populated.

---

## 6. fsck-equivalent — `dbfs_fsck`

**Status:** Out of scope for v1 delivery. Documented here as a follow-up TODO with concrete check items.

Because D5 recovery already runs on every mount, the engine is self-healing for *committed* state. `dbfs_fsck` exists to catch *latent* corruption that recovery cannot detect (because it does not constitute a power-cut state) and to provide an offline integrity audit.

### 6.1 Required checks (derived from D3 schema and D5 recovery model)

| # | Check | Failure mode it catches |
|---|---|---|
| 1 | **Superblock-replica triplet integrity** | All three replicas valid, agree on volume UUID, monotonic gen sequence. Catches partial writes recovery picked the wrong way. |
| 2 | **Checkpoint-ring sanity** | Slot generations monotonic modulo wrap; latest `clean=true` slot present; `superblock_lba` / `intent_log_head` / `root_pmap_record_lba` all dereferenceable. |
| 3 | **WAL window bounds** | `intent_log_head` ≤ `lsn_last` of last replayed TXN; no committed TXN with LSN past head. |
| 4 | **Orphan EXTENT_REF** | Every EXTENT_REF row points to an existing EXTENT row. Dangling EXTENT_REF = corruption — recovery would not see it (it's not orphan in the arena sense, it's orphan in the table sense). |
| 5 | **Orphan BLOCK_BLOB** | Every EXTENT row points to an existing BLOCK_BLOB row. Dangling EXTENT = inaccessible byte storage. |
| 6 | **Unreferenced BLOCK_BLOB** (orphan reclamation) | Every BLOCK_BLOB row has at least one referencing EXTENT row. Unreferenced = leaked space (matches the orphan-arena step in D5 but at the catalog level, not the arena level). |
| 7 | **EXTENT checksum verification** | Recompute checksum of each BLOCK_BLOB byte range against EXTENT.checksum. Catches silent disk corruption. |
| 8 | **INODE / DENTRY consistency** | Every DENTRY.child_ino references an existing INODE; every INODE with link_count > 0 has at least that many DENTRY rows pointing at it. |
| 9 | **FILE_VERSION → EXTENT_REF chain** | Every FILE_VERSION.root_extent_ref reaches a coherent EXTENT_REF chain; no cycles, no overlapping logical_offset ranges within a (ino_id, gen). |
| 10 | **STORAGE_CLASS table** | All 6 static rows present (per D3); no foreign rows. |
| 11 | **TXN/WAL_RECORD pairing** | Every TXN row's [lsn_first..lsn_last] window contains exactly one WAL_RECORD_COMMIT if status=committed. |
| 12 | **Capability bitset audit** | `active_caps` of mount matches the capability bits the engine actually services (catches a stale bitset after a partial code revert). |

### 6.2 Suggested CLI shape (Phase 9)

```
bin/simple dbfs fsck <device> [--read-only] [--verify-checksums] [--reclaim-orphans] [--report=<path>]
```

Default `--read-only` so it cannot worsen a damaged volume; `--reclaim-orphans` separately gated. `--verify-checksums` is O(volume size) and should be opt-in.

---

## 7. User-Facing Error Catalog

DBFS returns `FsError` variants from `src/lib/nogc_sync_mut/fs_driver/error.spl`. Each is mapped to a POSIX errno at the VFS syscall boundary by `errno_of`. Below: when each fires, what the operator should do.

| FsError | errno | When it fires (DBFS-specific) | Operator action | Recovery command / hint |
|---|---|---|---|---|
| `Unsupported` | `ENOTSUP` (95) | D10 out-of-scope op invoked: `mmap(MAP_SHARED, PROT_WRITE)`, `link()` (hard link), holes, `O_DIRECT`, per-file `fsync`, `flock`. | Confirm the operation is in the D10 out-of-scope list; switch the caller to a supported alternative or move that workload to RamFS/FAT32. | None — code change required, not data recovery. |
| `IoError(code)` | `EIO` (5) | Underlying NVMe read/write returned non-zero status; DMA buffer error; arena read past end. | 1. Check kernel log for NVMe errors. 2. If transient, retry. 3. If persistent on a specific LBA range, soft-rollback (§4) and run `dbfs_fsck` (when available) or capture the dump for forensics. | Soft rollback per §4. |
| `Corrupt` | `EIO` (5) | Checksum mismatch on EXTENT, bad magic on superblock or checkpoint slot, CRC failure during recovery. | Treat as data loss until proven otherwise. **DO NOT WRITE.** Remount read-only if possible; capture dump per §4.2; engage hard rollback if userland blocked. | Soft rollback + forensic dump; future `dbfs_fsck --verify-checksums`. |
| `ReadOnly` | `EROFS` (30) | Write attempt on a mount that was opened with read-only `MountOptions`. | Either remount read-write (if intended) or fix the writer. | `MountTable.unmount("/data")` then re-mount with `MountOptions.read_write()`. |
| `InvalidArg` | `EINVAL` (22) | Bad path, bad offset, null handle, malformed `OpenFlags`, invalid UTF-8 in name (DBFS catalog requires valid UTF-8 per D3 DENTRY name encoding). | Caller bug; fix the request. | None — code-side fix in the caller. |
| `NoSpace` | `ENOSPC` (28) | Backing arena exhausted; checkpoint ring full and oldest entry still required by an in-flight TXN; WAL window cannot extend. | 1. Free space (delete files in `/data`). 2. If checkpoint ring is the bottleneck (long-running TXN holding head), commit or abort that TXN. 3. Worst case: soft rollback and grow the backing. | `unlink` files, then `sync`. |
| `NotFound` | `ENOENT` (2) | Path or handle does not exist; also returned by `MountTable.unmount(path)` if no mount at that exact path. | Verify the path; verify the mount point matches exactly (longest-prefix lookup uses startswith, but `unmount` requires exact equality). | `MountTable.lookup_text(path)` to confirm mount, then re-issue. |
| `Busy` | `EBUSY` (16) | `unmount` called while open handles exist. | Identify and close the holders; retry unmount. | Process scan + close, then retry. |
| `AlreadyExists` | `EEXIST` (17) | Create with exclusive flag for an existing path. | Caller-driven; fix the request. | None. |
| `Permission` | `EACCES` (13) | ACL/UID-GID check failed (D3 ACL_ENTRY table). | Fix the ACL entry or the caller's identity. | `setfacl` / `chown` (POSIX shim D10 supported set). |
| `TooLarge` | `EFBIG` (27) | Write exceeds engine size limit (per `extension.spl` validate_buffer / validate_shared_buffer). | Reduce write size; chunk the operation. | None. |
| `Transient(code)` | `EAGAIN` (11) | Lock contention or temporary engine state. | Retry with backoff. | Loop with bounded retry. |
| `Interrupted` | `EINTR` (4) | Syscall interrupted by signal (signal-aware callers only). | Retry. | Loop with bounded retry. |

(Source: `src/lib/nogc_sync_mut/fs_driver/error.spl`.)

---

## 8. Smoke-Test Sequence after First Mount

Run these five steps after every fresh DBFS mount (post-format, post-soft-rollback-recovery, or post-boot in environments that re-mount each boot). All of them are POSIX-shim ops in the D10 in-scope set.

```bash
# 0. Pre-condition: DBFS is mounted at /data (verify with mount/MountTable.lookup_text).

# 1. Stat the root — must succeed and report is_dir=true.
stat /data
#   underlying spec: dbfs_driver_spec.spl, dbfs_posix_shim_spec.spl

# 2. Make a directory — exercises mkdir + DENTRY/INODE write through txn protocol.
mkdir /data/smoke

# 3. Write + read + stat a small file — exercises full D4 6-step write path on a
#    real on-disk byte sequence, then verifies read path.
printf 'hello dbfs\n' > /data/smoke/hello.txt
test "$(cat /data/smoke/hello.txt)" = "hello dbfs"
stat /data/smoke/hello.txt
#   underlying spec: dbfs_tx_protocol_spec.spl (6-step write order),
#                    dbfs_posix_shim_spec.spl (open/read/write/stat path)

# 4. Sync — forces a clean checkpoint slot to be published.
sync
#   underlying spec: dbfs_engine_checkpoint_spec.spl

# 5. Unmount and remount, then verify the file survived.
umount /data
mount -t dbfs <backing> /data    # or the equivalent MountTable.mount call
test "$(cat /data/smoke/hello.txt)" = "hello dbfs"
#   underlying spec: dbfs_recovery_spec.spl (clean mount-generation increments,
#                    committed records replayed)
```

If any step fails, capture (a) the FsError variant returned, (b) the kernel log,
(c) the contents of the last 3 checkpoint-ring slots, and (d) all 3 superblock
replicas. Hand that bundle to the engine maintainer along with the DBFS commit
SHA in use.

**Note on the `mount`/`umount` lines:** v1 has no userland `mount(8)` for DBFS;
the lines above are illustrative and assume Phase 9 ships a CLI. Until then the
equivalent flow is `MountTable.unmount("/data")` followed by re-running the
`vfs_init`-style mount call from a Simple harness. Document this gap in
`ship_plan.md` for the operator runbook.

---

## 9. Cross-references

- Architecture decisions D1–D12: `state.md` § Phase Outputs > 3-arch, plus full doc at `doc/04_architecture/dbfs_architecture.md`.
- AC matrix and verification commands: `verify_plan.md`.
- Risk register and pre-mortem: `risk_premortem.md` (R1–R13 + counter-mitigations).
- Refactor opportunities (Phase 6 — not blocking ship): `refactor_targets.md`.
- Spec inventory: `state.md` § Phase Outputs > 4-spec.
- Ship-time procedure (hard-rollback procedure, push order, submodule gitlink check per R8/R9): `ship_plan.md` (forthcoming Phase 8 deliverable — this playbook is consumed by it).

## 10. Open Follow-up TODOs

These are operational gaps surfaced while drafting this playbook. None blocks v1 ship; all are tracked here so they don't get lost.

1. **No `mkfs.dbfs` CLI.** §1.2 — formatting only via Simple constructors today. Phase 9.
2. **No userland `mount(8)` for DBFS.** §2.1 / §8 — runtime-only via `MountTable.mount`. Phase 9.
3. **No force-unmount.** §4.1 step 2 — `Busy` cannot be overridden. Phase 9.
4. **No `dbfs_fsck`.** §6 — 12 check items enumerated; not implemented. Phase 9.
5. **No `arena_export`.** §4.2 — forensic dump of NVFS-backed DBFS volume requires manual byte-level read. Phase 9.
6. **No fault-injected migration test.** §3.2 — `cp -r` from FAT32 → DBFS under power-cut not in current spec set. Phase 9 fault-injection sweep.
