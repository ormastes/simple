# NVFS Feature Requests

Secondary channel for feature requests against the NVFS (SimpleFS-NV)
filesystem. See `README.md` for the primary vs secondary channel rule.

- **Target:** nvfs
- **Owning design doc:** `doc/05_design/nvfs_design.md`
- **Upfront contributions (primary channel):**
  - `doc/05_design/nvfs/from_spostgre.md`
  - `doc/05_design/nvfs/svllm_requirements.md`

## Schema

Entries use the fields in `TEMPLATE.md`:

| Field | Notes |
|-------|-------|
| id | `FR-NVFS-####`, monotonic |
| title | verb-led, ≤ 80 chars |
| Filed-on | `YYYY-MM-DD` |
| Filed-by | author / agent / session id |
| Priority | `P0` / `P1` / `P2` (required at `Accepted`) |
| Status | `Open` / `Accepted` / `Implemented` / `Rejected` |
| Requested-semantics | one-paragraph description |
| Acceptance-criteria | observable bullets |
| Related-upfront | `from_spostgre.md §S#`, `svllm_requirements.md §R#`, or `none` |
| Related-design-doc | `nvfs_design.md §#`, or `tbd` |
| Related-issue | GH issue URL (optional) |

An entry may not move to `Implemented` without a `Related-design-doc` or
`Related-issue` link.

## Upfront Contributions (primary channel — do not re-file here)

Listed here for cross-reference **only**. The upfront doc
`doc/05_design/nvfs/from_spostgre.md` is the source of truth for these items —
edits go there, not in this tracker.

| Ref | Title | Priority | Source |
|-----|-------|----------|--------|
| `[UPFRONT] S1` | `arena_create` per storage class | P0 | `from_spostgre.md §S1` |
| `[UPFRONT] S2` | `arena_append_aligned` | P0 | `from_spostgre.md §S2` |
| `[UPFRONT] S3` | `arena_seal` + `arena_discard` with generation pinning | P0 | `from_spostgre.md §S3` |
| `[UPFRONT] S4` | `arena_clone_range` for page-version cloning | P0 | `from_spostgre.md §S4` |
| `[UPFRONT] S5` | Preferred I/O granule + capability query (`fs_caps`) | P0 | `from_spostgre.md §S5` |
| `[UPFRONT] S6` | Capability-gated atomic-pointer-record publish | P0 | `from_spostgre.md §S6` |
| `[UPFRONT] S7` | NVMe Flush / FUA pass-through tied to durability classes | P0 | `from_spostgre.md §S7` |

The seven `[UPFRONT]` items above are **not** open entries. They are already
locked into the fs-API contract. Do not re-file them here. Updates to their
wording/semantics belong in `from_spostgre.md` (and mirror into
`nvfs_design.md`).

Six P1 stretch items (`S-stretch-1..6` — ZNS zone-append, FDP PIDs,
namespace-per-class, copy offload, CMB/PMR, DSM trim) also live in
`from_spostgre.md`; they are intentionally omitted from the table above to
keep the `[UPFRONT]` list focused on the load-bearing seven.

## Open Requests

<!-- FR-STORAGE-0001 through FR-STORAGE-0003 filed by Phase 9-M1-retrofit agent
     (2026-04-17) while wiring Fat32Driver into g_mount_table. These are FsDriver
     trait-surface gaps in src/lib/nogc_sync_mut/fs_driver/ — they use FR-STORAGE
     because they affect the shared fs_driver interface, not NVFS internals. -->

### FR-STORAGE-0001 — Fat32Driver: statfs() and truncate/ftruncate not implemented

- **Filed-on:** 2026-04-17
- **Filed-by:** Phase 9-M1-retrofit agent (session nvfs-m1-retrofit)
- **Target:** storage  (src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl → fat32.spl)
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  `Fat32Driver.statfs()` currently returns `pass_todo`. The missing piece is in
  `src/os/services/fat32/fat32.spl` (class `Fat32Driver`): after `mount()` the
  geometry fields (`total_clusters`, `sectors_per_cluster`, `bytes_per_sector`) are
  populated but there is no free-cluster walk. A `get_free_clusters()` method that
  walks the FAT table and counts `FAT32_FREE` entries would supply `free_bytes` and
  `avail_bytes` for `FsStatfs`. Similarly `truncate(path, len)` and
  `ftruncate(handle, len)` require a cluster-free operation that releases the tail
  of a cluster chain — this also lives in `fat32_write.spl` (Fat32WriteContext)
  alongside `delete_file`/`create_file`. Add `truncate_chain(start_cluster, keep_bytes)`
  to `Fat32WriteContext` and expose it via `FsDriver.truncate`/`ftruncate`.
- **Acceptance-criteria:**
  - [ ] `Fat32Driver.statfs()` returns `Ok(FsStatfs)` with correct `free_bytes`
  - [ ] `Fat32Driver.truncate("/foo.txt", 0)` returns `Ok(())` and frees all clusters
  - [ ] `Fat32Driver.ftruncate(handle, n)` shrinks or extends the file to `n` bytes
  - [ ] All existing `fs_test_entry.spl` tests pass after the change
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/simpleos_fs_migration.md §M4`
- **Related-issue:** none
- **Notes:** Blocked on M4 (pure-Simple FAT32 replaces C-extern delegation).
  Until M4, the C NVMe path via `rt_fat32_*` externs does not expose free-cluster
  counts either, so this is a genuine gap across all three implementations.

---

### FR-STORAGE-0002 — Fat32Driver: true pread/pwrite (cursor-preserving positional I/O)

- **Filed-on:** 2026-04-17
- **Filed-by:** Phase 9-M1-retrofit agent (session nvfs-m1-retrofit)
- **Target:** storage  (src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl → fat32.spl)
- **Priority:** P2
- **Status:** Open
- **Requested-semantics:**
  `FsDriver.pread(handle, offset, buf)` must not advance the file cursor — it is
  a POSIX `pread(2)` semantics requirement. The current `Fat32Driver` in
  `src/os/services/fat32/fat32.spl` lacks cursor-save/restore around seek+read.
  `Fat32OpenFile.current_offset` and `current_cluster` would need to be snapshotted,
  the seek+read performed, then restored. This requires either exposing
  `open_files` for mutation or adding a `pread(handle, offset, size)` method to
  `Fat32Driver` (alias: `src/os/services/fat32/fat32.spl`). Positional write
  (`pwrite`) has the same requirement.
- **Acceptance-criteria:**
  - [ ] `pread(h, 0, buf)` reads from offset 0 without changing the cursor reported
        by a subsequent `read(h, current_pos, buf2)`
  - [ ] `pwrite(h, 0, buf)` writes at offset 0 without changing the cursor
  - [ ] Round-trip: `write(h, 10, a)` then `pread(h, 0, b)` reads from 0, cursor
        remains at 10 for the next sequential read
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/simpleos_fs_migration.md §M4`
- **Related-issue:** none
- **Notes:** P2 because pread/pwrite are not used by any current entry-point file.
  Will become P1 when M2 (replace rt_fat32_* in shell) lands.

---

### FR-STORAGE-0003 — Fat32Driver: fstat(FileHandle) and readdir(DirHandle) via handle

- **Filed-on:** 2026-04-17
- **Filed-by:** Phase 9-M1-retrofit agent (session nvfs-m1-retrofit)
- **Target:** storage  (src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl → fat32.spl)
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  `FsDriver.fstat(FileHandle)` and `FsDriver.readdir(DirHandle)` both receive
  opaque handles, not paths. The wrapper in `fat32_stub.spl` maintains a
  `file_handles: [Fat32HandleEntry]` table with `path: text` per entry, so the
  information is present — but the `FsDriver` trait declares `fstat` and `readdir`
  as `fn` (immutable self), not `me fn` (mutable self). Delegating from an `fn`
  body to `me fn Fat32Core.stat(path)` / `me fn Fat32Core.readdir(path)` requires
  either (a) relaxing the trait body to `me fn`, or (b) introducing an interior
  mutability wrapper around `Fat32Core`. The simplest fix for M2 is to change
  `fstat`/`readdir` in `ops.spl` to `me fn` — these ops already require mutable
  state in every real implementation (open_files tracking). For `readdir`,
  additionally store the path in `dir_handles` at `opendir` time (a new op not
  yet in `FsDriver`).
- **Acceptance-criteria:**
  - [ ] `fstat(FileHandle)` returns `Ok(FileStat)` matching `stat(path)` for same file
  - [ ] `readdir(DirHandle)` returns the same entries as a path-based readdir
  - [ ] `opendir(path) -> Result<DirHandle, FsError>` added to `FsDriver` trait
        (currently missing; DirHandle exists but no way to obtain one)
  - [ ] All existing tests pass
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/fs_driver_interface.md §2`
- **Related-issue:** none
- **Notes:** The missing `opendir` op is a genuine gap in the `FsDriver` trait design
  (ops.spl line 96 declares `readdir(DirHandle)` but there is no `opendir`).
  This FR covers both the trait gap and the Fat32Driver impl gap.

### FR-STORAGE-0004 — MountTable.resolve() uses slice() which is broken in baremetal Cranelift

- **Filed-on:** 2026-04-18
- **Filed-by:** Phase 9-M2-retrofit agent (a93c433), discovered while attempting to route `shell_serial_entry.spl` / `fs_test_entry.spl` through `g_mount_table`
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:** Rewrite `MountTable.resolve(path)` in `src/lib/nogc_sync_mut/fs_driver/mount_table.spl:129` so it does NOT call `path.raw.slice(mp_len, …)`. Cranelift's baremetal codegen has a known-broken `slice()` operation (per the hazard comment already in `shell_serial_entry.spl`); any baremetal caller routed through the mount table today would reintroduce that bug.
- **Acceptance-criteria:**
  - [ ] `MountTable.resolve("/foo/bar")` returns the same `(driver, relpath)` tuple as today on host.
  - [ ] The function does not call `.slice()` on a `[u8]` or text slice.
  - [ ] A baremetal test on x86_64 (e.g. `shell_serial_entry.spl` path-splitting scenario) no longer hits the slice() codegen path.
  - [ ] Implementation uses indexed char-copy, `starts_with` + length arithmetic, or a C extern `path_strip_mount_prefix(path, mp_len) -> text` — any approach that sidesteps the broken slice.
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/fs_driver_interface.md §2` (MountTable contract), `doc/05_design/simpleos_fs_migration.md §M2` (the retrofit this blocks)
- **Related-issue:** none
- **Notes:** This is the single blocker for Phase 9-M2 (SimpleOS fs call-site retrofit). Until it's resolved, the two direct-FAT32 call sites (`shell_serial_entry.spl`, `fs_test_entry.spl`) cannot be routed through the mount table without reintroducing a known codegen bug. Option A: fix Cranelift `slice()` in baremetal backend (big yak-shave). Option B: add a C extern. Option C: rewrite `MountTable.resolve()` in pure Simple without slice (recommended — self-contained).
  - **Implemented-by:** 2026-04-18, rewrote MountTable.resolve to use str_char_at indexed-char-copy (mount_table.spl +6 lines); 5/5 resolve tests pass.

Entries here are filed during Phase 5+ implementation (per SStack state file
`.sstack/spostgre-nvfs-storage/state.md`) when an NVFS need is discovered that
is not already covered by the `[UPFRONT]` items above. Use `TEMPLATE.md` and
append under this heading.

## Closed (Implemented or Rejected)

_No entries yet._

Closed entries are moved here from `## Open Requests` (never deleted) with
`Status: Implemented` or `Status: Rejected` and the required link/reason.
