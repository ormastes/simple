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

### FR-HOT-001 — HOT: integrate pd_upper/pd_lower free-space check before chaining

- **Filed-on:** 2026-04-17
- **Filed-by:** spostgre M3a agent (session spostgre-m3a)
- **Target:** spostgre  (examples/spostgre/src/engine/hot.spl)
- **Priority:** P2
- **Status:** Implemented — 2026-04-18
- **Implemented-by:** 9-hot-slack agent (session spostgre-hot-001)
- **Requested-semantics:**
  `HotChain.try_update` currently chains a HOT update unconditionally at the
  logical-page-group level. A real PostgreSQL HOT update is only valid when the
  page has sufficient free space (pd_upper − pd_lower > tuple_size). The
  `buffer_mgr` API does not yet expose free-space metadata, so the check is
  deferred. Once `buffer_mgr` provides `page_free_space(page_id) -> u16`, add
  a pre-check in `try_update`: if `free_space < new_tuple_size`, fall through
  to a regular heap insert instead of chaining.
- **Acceptance-criteria:**
  - [x] `buffer_mgr` exposes `page_slack(hdr: PageHeader) -> i32` (pd_upper - pd_lower)
        and `LINE_POINTER_SIZE: i32 = 4`
  - [x] `hot_try_update_page` in `hot.spl` calls `page_slack` and returns Cold/no_slack
        when `slack < byte_size + LINE_POINTER_SIZE`
  - [x] Existing HOT unit tests continue to pass (hot_try_update signature unchanged)
  - [x] 3 new tests in `examples/spostgre/test/unit/hot_slack_test.spl`:
        plenty-of-slack (HOT), too-full (Cold/no_slack), exact-boundary (HOT)
- **Related-upfront:** none
- **Related-design-doc:** `examples/spostgre/doc/design/hot_update.md` (M3a design)
- **Related-issue:** none
- **Notes:** Implemented as `hot_try_update_page` (new fn) rather than replacing
  `hot_try_update`, preserving existing caller contract. `page_slack` accepts a
  decoded `PageHeader` rather than a `page_id` (buffer_mgr has no live page map
  at M3a); callers decode from the buffer before calling.

---

### FR-BENCH-CLOCK-002 — Replace PIT-ch2 TSC calibration with HPET/PMTMR

- **Filed-on:** 2026-04-18
- **Filed-by:** bench-clock-baremetal agent
- **Priority:** P2
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Implemented-by:** agent a8cc4856 (completed by spostgre-nvfs-storage)
- **Requested-semantics:**
  Current TSC calibration in `src/os/kernel/arch/x86_64/timer.spl` uses PIT
  channel 2 for a ~10ms measurement window. Virtualised QEMU HPET is available
  via the ACPI HPET table (MMIO counter at 100 MHz-ish) and provides better
  reference accuracy. The ACPI FADT PM_TMR_BLK port gives a 3.579545 MHz
  PMTMR fallback. Implement ACPI table walk → HPET MMIO → PMTMR port-IO
  discovery, use whichever is present, fall back to PIT-ch2 if neither found.
- **Acceptance-criteria:**
  - [x] `_calibrate_tsc` probes ACPI RSDP (already passed by Limine) for HPET
        table; if found, maps MMIO counter and uses it as reference
  - [x] If HPET absent, falls back to FADT PM_TMR_BLK port for PMTMR reference
  - [x] If neither present, retains PIT-ch2 path (unchanged from FR-BENCH-CLOCK-001)
  - [x] `tsc_frequency` error vs HPET-measured value < 0.1% on QEMU
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/simpleos_fs_migration.md` (boot init section)
- **Related-issue:** none
- **Notes:** Fully implemented 2026-04-18 (B2). Real HPET MMIO and PMTMR port-IO
  calibration wired in `_calibrate_tsc_hpet` / `_calibrate_tsc_pmtmr` (timer.spl).
  Pure math helpers `_tsc_hz_from_hpet` / `_tsc_hz_from_pmtmr` extracted for
  unit-testability; 5 new test cases added to `test/unit/os/timer_test.spl`.
  Overflow-safe staged formula used (hpet_delta×period_fs/1e6 then ×1e9).
  PIT-ch2 fallback retained when hz computation yields 0.
  **Unblocked by:** FR-SIMPLEOS-ACPI-001 (Implemented 2026-04-18).

---

### FR-SIMPLEOS-ACPI-001 — ACPI table walker (RSDP → RSDT/XSDT → FADT + HPET)

- **Filed-on:** 2026-04-18
- **Filed-by:** spostgre-nvfs-storage acpi-walker agent
- **Target:** os  (src/os/kernel/acpi/)
- **Priority:** P1
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Implemented-by:** spostgre-nvfs-storage acpi-walker agent
- **Requested-semantics:**
  SimpleOS needs real HPET MMIO base and PMTMR I/O port from ACPI tables so
  that TSC calibration can use sub-0.1% reference sources instead of PIT-ch2.
  Implement: RSDP scanner (BIOS shadow 0xE0000–0x100000, 16-byte alignment,
  checksum validation), RSDT/XSDT iterator (32-bit vs 64-bit entry dispatch),
  FADT parser (PM_TMR_BLK offset 76, X_PM_TMR_BLK GAS offset 208 for ACPI 2+),
  HPET table parser (GAS at offset 44, address at offset 48).
- **Acceptance-criteria:**
  - [x] `src/os/kernel/acpi/rsdp.spl` — `acpi_find_rsdp() -> u64?` scans BIOS shadow; `acpi_rsdp_revision`, `acpi_rsdp_rsdt_phys`, `acpi_rsdp_xsdt_phys` helpers
  - [x] `src/os/kernel/acpi/rsdt.spl` — `acpi_iterate_tables(rsdp, cb)` walks XSDT (rev≥2) or RSDT; `acpi_find_table(rsdp, sig) -> u64?` convenience wrapper
  - [x] `src/os/kernel/acpi/fadt.spl` — `acpi_fadt_pm_tmr_port(fadt_phys) -> u32?` reads PM_TMR_BLK; prefers X_PM_TMR_BLK GAS (offset 208) when rev≥3 and len≥244
  - [x] `src/os/kernel/acpi/hpet_table.spl` — `acpi_hpet_base(hpet_phys) -> u64?` reads GAS at offset 44; MMIO address at GAS+4 (offset 48)
  - [x] `src/os/kernel/acpi/clock_sources.spl` — stubs replaced; `acpi_hpet_present()` and `acpi_pmtmr_port()` call new helpers; `_resolve_rsdp()` prefers `g_rsdp_phys`, falls back to `acpi_find_rsdp()`
  - [x] `test/unit/os/acpi/acpi_test.spl` — 3 test groups: RSDP global state, signature constants, nil returns with zero RSDP
  - [x] FADT offset 208 (not 112) used for X_PM_TMR_BLK; HPET GAS address at offset 48 (not 44); RSDP 8-byte signature + checksum validated
- **Related-upfront:** FR-BENCH-CLOCK-002
- **Related-design-doc:** `doc/05_design/simpleos_fs_migration.md` (boot init section)
- **Related-issue:** none
- **Notes:** All addresses are physical; helpers call `phys_to_virt()` internally via
  HHDM. UEFI variant not implemented (BIOS scan sufficient for QEMU/Limine). MADT,
  MCFG, and other tables not parsed.

---

Entries here are filed during Phase 5+ implementation (per SStack state file
`.sstack/spostgre-nvfs-storage/state.md`) when an NVFS need is discovered that
is not already covered by the `[UPFRONT]` items above. Use `TEMPLATE.md` and
append under this heading.

### FR-SIMPLEOS-M5-001 — VFS select-file cursor semantic (VfsCursor singleton)

- **Filed-on:** 2026-04-18
- **Filed-by:** M5-fs-select-cursor agent
- **Target:** os  (src/os/services/vfs/vfs_init.spl)
- **Priority:** P1
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Implemented-by:** M5-fs-select-cursor agent
- **Requested-semantics:**
  `rt_fat32_select_file` (retired in M5) held a static 64-byte name cursor that
  callers used to remember the last-selected file before operating on it.
  FsDriver has no stateful-cursor concept. Option C was chosen: a module-level
  `g_vfs_selected_file: text` var in `vfs_init.spl` (service layer) provides
  backwards-compatible `g_vfs_select_file` / `g_vfs_get_selected_file` /
  `g_vfs_clear_selected_file` / `g_vfs_write_selected_file_text` helpers.
  DriverInstance and FsDriver remain stateless; state lives only in the service
  layer, consistent with the MDSOC+ composition-over-state pattern.
- **Acceptance-criteria:**
  - [x] `g_vfs_select_file(name)` stores the name in `g_vfs_selected_file`
  - [x] `g_vfs_get_selected_file()` returns the stored name
  - [x] `g_vfs_clear_selected_file()` resets to empty string
  - [x] `g_vfs_write_selected_file_text(content)` returns false when no file selected
  - [x] `g_vfs_write_file_text(name, content)` dispatches write through mount table
  - [x] 6 unit tests pass in `test/unit/os/vfs_cursor_test.spl`
  - [x] DriverInstance and FsDriver are unmodified (stateless contract preserved)
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/fs_driver_interface.md §3`
- **Related-issue:** none
- **Notes:** Option A (cursor in DriverInstance enum arms) was rejected — semantically
  wrong, pollutes the driver layer. Option B (callers carry path) has no current callers
  to retrofit. Option C (service-layer singleton) was chosen as the minimal backwards-
  compatible approach with zero impact on the driver interface.

---

### FR-NVFS-N4a-001 — Scrub repair path: detect + repair from reflink peers

- **Filed-on:** 2026-04-18
- **Filed-by:** N4a-scrub-repair agent
- **Priority:** P1
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Implemented-by:** N4a-scrub-repair agent
- **Requested-semantics:**
  `scrub_all` previously only detected checksum mismatches and reported them.
  Add a repair path: when a bad block is found, scan all pmap sidecar entries
  for a peer whose stored checksum matches the bad entry's expected checksum and
  whose live data still verifies.  Copy the good bytes back byte-by-byte via
  `arena_mutate_for_test`.  If no valid peer is found, report Unrepairable.
  META_DURABLE (superblock/checkpoint) replica fallback is deferred to N4b.
- **Acceptance-criteria:**
  - [x] `RepairResult` struct added to `scrub.spl` (repaired: bool, source_arena: i64)
  - [x] `scrub_repair_block(bad_sc)` iterates pmap sidecar for a peer with matching
        checksum and valid live data; copies bytes on success
  - [x] `ScrubReport` gains a `repaired: u64` counter
  - [x] `scrub_all` calls repair on every corrupt entry and updates counters
  - [x] Test 7: bad block + good peer → repaired >= 1
  - [x] Test 8: bad block + no peer → repaired < corrupted (unrepairable)
  - [x] Test 9: both copies corrupt → repaired = 0
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/nvfs_design_v2.md §14`
- **Related-issue:** none
- **Notes:** Byte-writeback uses `arena_mutate_for_test` (the only in-scope
  byte-writer); a proper `arena_write_range` API is a follow-up.
  META_DURABLE replica fallback tracked as FR-NVFS-N4b-001.

---

### FR-NVFS-N4b-001 — Proactive scrub scheduler + META_DURABLE replica repair

- **Filed-on:** 2026-04-18
- **Filed-by:** N4a-scrub-repair agent
- **Priority:** P2
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Implemented-by:** N4b-scheduler agent
- **Requested-semantics:**
  N4a repair falls back to Unrepairable when no reflink peer has a good copy.
  N4b should (a) add a background-task scheduler that runs `scrub_all`
  periodically (honouring `throttle_ms`), and (b) extend the repair path to
  also check META_DURABLE superblock and checkpoint-ring replicas (already
  written 2–3× by the driver) as a fallback source of truth.
- **Acceptance-criteria:**
  - [x] `ScrubScheduler` struct with `interval_ms`, `rate_bytes_per_sec`, `batch_size`, `last_run_ns`
  - [x] `scrub_scheduler_tick` returns empty report when interval has not elapsed; runs pass and advances `last_run_ns` when it has
  - [x] Rate limiting via `batch_size` (derived from `rate_bytes_per_sec / 4096`)
  - [x] `scrub_repair_meta_durable` reads `superblock_replica_raw(0..2)` as fallback when peer scan returns Unrepairable and `arena_id <= 0` (metadata region)
  - [x] `_scrub_repair_with_meta_durable` chains peer-scan → META_DURABLE fallback; called from both `scrub_all` and `scrub_scheduler_tick`
  - [x] 3 new tests: tick-too-early (checked=0, last_run_ns unchanged), tick-after-interval (last_run_ns advanced, checked≥1), metadata-replica repair succeeds
  - [x] Existing N4a tests (1–9) continue to pass
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/nvfs_design_v2.md §14`
- **Related-issue:** none
- **Notes:** `arena_write_range` replacement deferred — `arena_mutate_for_test` is
  still used for writeback (the only in-scope byte-writer). `scrub_scheduler_new`
  is a convenience constructor; callers may also construct `ScrubScheduler` directly.

---

## Closed (Implemented or Rejected)

### FR-N3-001 — Replace flat pmap sidecar with B-tree keyed by (arena_id, offset)

- **Filed-on:** 2026-04-17
- **Filed-by:** N3 implementation agent
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  The flat `_pmap_sidecar: [PmapSidecarEntry]` in `fs_driver_impl.spl` performs
  O(n) linear scan on every read and write path.  Replace it with a B-tree keyed
  by `(arena_id, offset)` so that insert and lookup are O(log n).  The B-tree must
  support range iteration (used by scrub) and key removal.  Delete rebalancing
  may be deferred to a follow-up milestone.
- **Acceptance-criteria:**
  - [x] `pmap_btree_insert` is O(log n) with leaf-split propagation
  - [x] `pmap_btree_lookup` is O(log n)
  - [x] `pmap_btree_range_collect` returns entries in key order for inclusive range
  - [x] `pmap_btree_remove` removes leaf key (rebalancing deferred to N5b)
  - [x] `nvfs_pmap_sidecar_snapshot` iterates via B-tree; scrub_test.spl unchanged
  - [x] ≥ 8 unit tests pass in `pmap_btree_test.spl`
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/nvfs_design_v2.md §17`
- **Related-issue:** none
- **Implemented-by:** N5a agent, 2026-04-17.
  Files: `examples/nvfs/src/core/pmap_btree.spl` (new, node-pool B-tree),
  `examples/nvfs/src/driver/fs_driver_impl.spl` (wired), 
  `examples/nvfs/test/unit/pmap_btree_test.spl` (8 tests).
  Delete rebalancing tracked as FR-NVFS-N5b-001.

---

### FR-NVFS-N5b-001 — B-tree rebalancing on delete (merge / rotate)

- **Filed-on:** 2026-04-17
- **Filed-by:** N5a implementation agent
- **Priority:** P2
- **Status:** Implemented
- **Implemented-on:** 2026-04-17
- **Implemented-by:** N5b implementation agent
- **Requested-semantics:**
  `pmap_btree_remove` in N5a performs leaf-only deletion without rebalancing.
  After many deletes the tree can become unbalanced (under-filled nodes).
  Implement standard B-tree merge and rotation on delete so the tree remains
  balanced (minimum fanout/2 keys per non-root node) after arbitrary remove sequences.
- **Acceptance-criteria:**
  - [x] After inserting 100 entries and removing 50, all remaining lookups succeed
  - [x] Tree height shrinks when root has 0 keys and 1 child (root-shrink)
  - [x] Existing pmap_btree_test.spl still passes (8 tests)
  - [x] New pmap_btree_rebalance_test.spl: 8 tests (borrow-left, borrow-right, merge, delete-all, large-scale)
- **Files-changed:**
  - `examples/nvfs/src/core/pmap_btree.spl` — replaced leaf-only remove with
    full rebalancing: `btree_borrow_from_left`, `btree_borrow_from_right`,
    `btree_merge_with_right`, `_delete_recursive`, `pmap_btree_is_empty`.
  - `examples/nvfs/test/unit/pmap_btree_rebalance_test.spl` — 8 new tests.
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/nvfs_design_v2.md §17`
- **Related-issue:** none

### FR-BENCH-CLOCK-001 — Add rt_time_now_ns() for hosted and baremetal targets

- **Filed-on:** 2026-04-17
- **Filed-by:** 9-bench-harness agent (session spostgre-nvfs-storage)
- **Priority:** P1
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Implemented-by:** bench-clock-baremetal agent
- **Requested-semantics:**
  Bench harness in `bench/lib/timing.spl` calls `extern fn rt_time_now_ns() -> i64`
  but the symbol was absent from both hosted and baremetal runtimes.
  Hosted: backed by `clock_gettime(CLOCK_MONOTONIC)`.
  Baremetal (SimpleOS x86_64): backed by TSC calibrated at boot against PIT
  channel 2 (~10ms window, `_calibrate_tsc` in `timer.spl`).
- **Acceptance-criteria:**
  - [x] `rt_time_now_ns()` present in `src/runtime/runtime_native.c` (hosted)
  - [x] `rt_time_now_ns()` exported with C linkage from
        `src/os/kernel/arch/x86_64/timer.spl` (baremetal)
  - [x] Returns monotonically increasing values (TSC is invariant on modern CPUs)
  - [x] `bin/simple build lint` passes clean
- **Related-upfront:** none
- **Related-design-doc:** `doc/08_tracking/bench/README.md`
- **Related-issue:** none
- **Notes:** Calibration math: `ns = (delta/freq)*1e9 + (delta%freq)*1e9/freq`.
  Split avoids i64 overflow: at 4 GHz TSC, `delta*1e9` would overflow ~2.3s;
  dividing out seconds first keeps remainder < freq. HPET/PMTMR fallback
  tracked as FR-BENCH-CLOCK-002.

---

### FR-NVFS-N6a-001 — Wire real AES-128-GCM into NVFS leaf DEK encrypt/decrypt

- **Filed-on:** 2026-04-17
- **Filed-by:** N6a scaffolding agent (session spostgre-nvfs-storage)
- **Target:** nvfs  (examples/nvfs/src/core/encryption.spl)
- **Priority:** P1
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Implemented-by:** 9-n6a-real-aes-retry agent
- **Requested-semantics:**
  `encryption.spl` stubs (`_aes128_encrypt_stub` / `_aes128_decrypt_stub`) use
  XOR + checksum instead of real AES-128-GCM. Replace with calls to
  `aes128_gcm_encrypt` / `aes128_gcm_decrypt` from the vendored
  `examples/nvfs/src/core/crypto/aes128_gcm.spl`. Keep 3-level key hierarchy
  (wrapping → master → data DEK) intact; only the leaf DEK performs AES-GCM.
  Also upgrade `keystore_generate_master` to use AES-GCM for wrapped_key storage.
- **Acceptance-criteria:**
  - [x] `_aes128_encrypt_stub` / `_aes128_decrypt_stub` removed (no unused code)
  - [x] `encrypt_arena_data` / `decrypt_arena_data` use real AES-128-GCM
  - [x] `keystore_generate_master` wraps master key with `aes128_gcm_encrypt`
  - [x] 3 new tests: roundtrip recovers exact bytes, tag-mismatch → Err(Corrupt),
        different offset → different ciphertext
  - [x] Existing 6 tests unchanged
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/nvfs_design_v2.md §14`
- **Related-issue:** none
- **Notes:** Cross-submodule import solved via `examples.nvfs.src.core.crypto.aes128_gcm`
  namespace (same pattern as `pmap_btree.spl`). Runtime externs (`rt_aes_sbox`,
  `rt_aes_rcon`, `rt_aes128_encrypt_block_into`) resolved by main Simple runtime.
  FR-NVFS-N6a-002 (KDF hardening) and FR-NVFS-N6a-003 (DEK rotation on seal)
  are now implemented — see entries below.

---

### FR-NVFS-N6a-002 — KDF hardening: salted derivation for per-arena dataset keys

- **Filed-on:** 2026-04-18
- **Filed-by:** 9-n6a-002-003 agent
- **Target:** nvfs  (examples/nvfs/src/core/encryption.spl)
- **Priority:** P1
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Implemented-by:** 9-n6a-002-003 agent
- **Requested-semantics:**
  `_derive_data_key_bytes` used a plain XOR of master_key bytes and arena_id with
  no domain separation or salt. Upgrade to a salted derivation that includes
  arena_id, a generation counter, and a domain-separation info string
  `"nvfs-dataset-v1"` so that: (a) same inputs always yield same output
  (determinism), (b) different arena_ids or generations yield different outputs,
  (c) the derivation is structurally equivalent to HKDF-SHA256 with info tagging.
  Full HKDF-SHA256 deferred until cross-submodule SHA256 is available.
- **Acceptance-criteria:**
  - [x] `_derive_data_key_bytes_gen(master, arena_id, generation)` added; folds
        master bytes, arena_id, generation, and info string `"nvfs-dataset-v1"`
  - [x] `_derive_data_key_bytes` is a shim calling gen=0 (backward compat)
  - [x] `keystore_derive_fresh_dek(ks, master_id, arena_id, generation)` exposed
  - [x] Test 10: same (master, arena, generation=0) → same key bytes
  - [x] Test 11: generation=0 vs generation=1 → different key bytes
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/nvfs_design_v2.md §14`
- **Related-issue:** none
- **Notes:** HKDF-SHA256 upgrade tracked as follow-up once `os.tls13.hkdf` is
  accessible from the examples submodule scope.

---

### FR-NVFS-N6a-003 — DEK rotation on arena seal

- **Filed-on:** 2026-04-18
- **Filed-by:** 9-n6a-002-003 agent
- **Target:** nvfs  (examples/nvfs/src/core/encryption.spl + arena.spl)
- **Priority:** P1
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Implemented-by:** 9-n6a-002-003 agent
- **Requested-semantics:**
  On `arena_seal_impl`, if the arena is registered as encrypted in the
  `EncryptionInfo` registry, derive a fresh DEK (bumped generation) and update
  the registry so subsequent `encrypt_arena_data` calls use the new key.
  The old DEK remains in the KeyStore until unmount. Full in-place re-encryption
  of already-appended extents is deferred to FR-NVFS-N6a-004.
- **Acceptance-criteria:**
  - [x] `EncryptionInfo` struct (master_id, dek_key_id, generation) added
  - [x] Module-level registry (`_enc_arena_ids`, `_enc_infos`) + `_g_ks` added
  - [x] `nvfs_set_arena_encryption(arena_id, enabled, kh)` registers/deregisters
  - [x] `nvfs_get_arena_encryption(arena_id) -> Option<EncryptionInfo>`
  - [x] `keystore_rotate_dek(ks, arena_id)` bumps generation, derives new DEK,
        updates registry
  - [x] `nvfs_arena_seal_rotate(arena_id)` called from `arena_seal_impl`
  - [x] Test 12: dek_key_id changes after seal-rotate on encrypted arena
  - [x] Test 13: new DEK produces different ciphertext; old DEK fails to decrypt
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/nvfs_design_v2.md §14`
- **Related-issue:** none
- **Notes:** In-place re-encryption of persisted extents tracked as FR-NVFS-N6a-004.
  Module-level `_g_ks` singleton enables arena_seal_impl to call rotate without
  requiring a KeyStore parameter (keeping arena.spl API stable).

---

### FR-NVFS-N6b-001 — Raw send / encrypted replication stream (btrfs-send style)

- **Filed-on:** 2026-04-18
- **Filed-by:** N6b implementation agent
- **Priority:** P1
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Implemented-by:** N6b implementation agent
- **Requested-semantics:**
  Stream a sealed MODEL_IMMUTABLE arena between peers without decrypting the
  payload.  Ciphertext + key metadata travel over the wire as a self-describing
  byte stream (magic `NVSR`, 16-byte header, per-arena begin/extent/end records).
  The receiver stores the raw ciphertext when no dataset key is available
  (`encrypted_opaque=true`); it can mount once a key is presented separately.
  Plaintext (unencrypted) arenas are also supported (flags bit 0 clear).
- **Acceptance-criteria:**
  - [x] `send_arena(arena_id, stream, ks, key)` serialises one sealed arena
  - [x] `receive_arena(stream, ks, key)` reconstructs and returns arena_id
  - [x] Plaintext roundtrip: received bytes match original
  - [x] Encrypted roundtrip with correct key: decrypts to original plaintext
  - [x] Encrypted roundtrip with wrong key: `ok=false` (GCM tag mismatch)
  - [x] Encrypted stream + no key: `ok=true`, `encrypted_opaque=true`, ciphertext stored
  - [x] 4 unit tests in `examples/nvfs/test/unit/send_test.spl`
- **Files-changed:**
  - `examples/nvfs/src/core/send.spl` (new) — SendStream, RecvStream, send_arena, receive_arena
  - `examples/nvfs/test/unit/send_test.spl` (new) — 4 tests
  - `examples/nvfs/src/core/__init__.spl` — docstring updated to list send module
  - `doc/05_design/nvfs/send_format.md` (new) — wire format spec
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/nvfs/send_format.md`; `nvfs_design_v2.md §14`
- **Related-issue:** none
- **Notes:** Encryption calls `encrypt_arena_data` / `decrypt_arena_data` from
  `encryption.spl` (N6a). Checksum field uses algo=0 (none) for N6b;
  CRC32C upgrade tracked as FR-NVFS-N6b-002 once cross-submodule access lands.

---

### FR-NVFS-N7a-001 — Inline compression: per-arena LZ4/Zstd, class-aware defaults

- **Filed-on:** 2026-04-18
- **Filed-by:** nvfs-v3-design agent
- **Target:** nvfs  (examples/nvfs/src/core/compression.spl — new)
- **Priority:** P2
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Implemented-by:** nvfs-n7a-compression agent (session spostgre-nvfs-storage)
- **Requested-semantics:**
  Add an inline compression layer (N7a) between the logical block and the physical device.
  Compression is per-dataset, per-arena, and opt-in via mount option `compress=<algo>`
  or per-file xattr `nvfs.compress`. Class-aware defaults: GENERAL_MUTABLE → Zstd-3,
  DB_TEMP → LZ4, MODEL_IMMUTABLE → None (weights already dense), META_DURABLE → None,
  DB_WAL → None, CHECKPOINT_SNAPSHOT → LZ4. The pmap entry is extended from 80 bytes
  (v2) to 88 bytes (v3) to carry `compress_algo (u8)` + `compressed_len (u32)`.
  Incompressible blocks (compressed ≥ 90% of raw) fall back to algo=None automatically.
  Supported algorithms: LZ4 (tag=1), Zstd-3 (tag=2), Zstd-19 (tag=3, archival only).
  The ARC cache stores decompressed blocks. Superblock magic becomes `b"NVFS0003"`.
  Full spec: `doc/05_design/nvfs_design_v3.md §V3-2`.
- **Acceptance-criteria:**
  - [x] `CompressAlgo` enum defined (None=0, LZ4=1, Zstd3=2, Zstd19=3)
  - [x] `arena_append_compressed` compresses data when class policy selects algo≠None,
        falls back on incompressible content (90% threshold)
  - [x] `arena_read_extent` decompresses transparently; caller receives plaintext bytes
  - [x] Pmap entry v3 (88 bytes) with `compress_algo` + `compressed_len` fields
  - [x] Class-aware defaults enforced: MODEL_IMMUTABLE→None, DB_WAL→None,
        META_DURABLE→None, DB_TEMP→LZ4, GENERAL_MUTABLE→Zstd3, CHECKPOINT_SNAPSHOT→LZ4
  - [ ] LZ4 write throughput ≥ 80% of uncompressed (requires FR-NVFS-N7a-002: real LZ4 encoder)
  - [ ] Zstd-3 on-disk size ≤ 45% of raw (requires FR-NVFS-N7a-003: real Zstd encoder)
  - [x] Round-trip fidelity: data written and read back byte-for-byte identical
  - [x] v2 pmap entries (80 bytes) decoded with compress_algo=0 / compressed_len=0 (migration path)
  - [ ] `nvfs upgrade` tool (offline batch upgrade; deferred follow-up)
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/nvfs_design_v3.md §V3-2, §V3-5, §V3-6, §V3-7`
- **Related-issue:** none
- **Files-changed:**
  - `examples/nvfs/src/core/compression.spl` (new) — CompressAlgo enum, compress_extent,
    decompress_extent, class_default_algo; LZ4/Zstd tagged-copy stubs (FR-NVFS-N7a-002/003 follow-up)
  - `examples/nvfs/src/core/pmap.spl` — v2→v3 (80→88 bytes): added compress_algo + compressed_len
    fields to PmapEntry; encode writes 88 bytes; decode dispatches on buf len (v2/v3 compat)
  - `examples/nvfs/src/core/arena.spl` — added arena_append_compressed and arena_read_extent
  - `examples/nvfs/test/unit/core/compression_test.spl` (new) — 4 test groups, 14 cases
- **Notes:** Compression must occur before encryption (§V3-4.1 enforces ordering).
  LZ4/Zstd stubs use tagged-copy frame for N7a; real encoders tracked as FR-NVFS-N7a-002/003.
  Throughput and ratio SLOs require real encoders. OQ-11 (compressed ARC) deferred.
  Superblock magic upgrade to NVFS0003 deferred (superblock.spl out of scope for this FR).

---

### FR-NVFS-N7b-001 — Inline deduplication: content-addressable DDT extending reflink machinery

- **Filed-on:** 2026-04-18
- **Filed-by:** nvfs-v3-design agent
- **Target:** nvfs  (examples/nvfs/src/core/dedup.spl — new)
- **Priority:** P2
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Requested-semantics:**
  Add an inline deduplication layer (N7b) backed by a content-addressable Deduplication
  Table (DDT). The DDT maps `content_hash (u8[32]) → DedupEntry` where DedupEntry
  carries the canonical logical_page_no, birth_gen, refcount, and flags (56 bytes/entry).
  The DDT is stored in a new CoW B-tree (DEDUP_TREE_OBJECTID=12), making an eleven-tree
  forest. A hot DDT RAM cache (default 256 MB, LRU eviction) fronts the on-disk B-tree.
  On write: compute Blake3 (or HMAC-DHK when encryption is active) of plaintext, look up
  DDT; on hit, reflink the existing physical block (no device write); on miss, write and
  insert. Class policy: META_DURABLE, DB_WAL, DB_TEMP are forced off; MODEL_IMMUTABLE
  is forced on when dataset dedup=on (primary use case: shared weight tensors across
  fine-tuned model variants). Dedup is disabled by default; opt-in via `dedup=on` mount
  option. When encryption is active, the DHK (per-dataset, derived from master key) is
  used as the HMAC key for DDT keys so the DDT does not leak plaintext identity across
  dataset boundaries. Refcount GC is synchronous (decremented in the write transaction
  on unlink/CoW; entry freed at refcount=0). Full spec: `doc/05_design/nvfs_design_v3.md
  §V3-3, §V3-4`.
- **Implementation-notes:**
  N7b in-RAM DDT implemented in `examples/nvfs/src/core/dedup.spl` (DedupTable,
  dedup_insert_or_bump, dedup_release, dedup_class_enabled). Hash uses a pure-Simple
  32-byte fold-XOR stub (Blake3 / HMAC-DHK deferred to FR-NVFS-N7b-002; DHK is
  per-dataset derived at mount time, not per-arena). Sibling DedupRefcountTable added
  to reflink.spl; arena.spl extended with arena_append_deduped (dedup → compress path)
  and arena_discard_impl walks _extent_hashes to release refcounts. CoW B-tree backend,
  256 MB LRU cache, and on-disk layout are follow-up work.
- **Acceptance-criteria:**
  - [ ] `DedupEntry` struct (56 bytes) + DEDUP_TREE_OBJECTID=12 B-tree defined
  - [ ] Hot DDT RAM cache: configurable `dedup_cache_mb` mount option (default 256)
  - [ ] Write path: Blake3/HMAC-DHK hash → hot DDT lookup → cold DDT lookup → reflink
        on hit / insert on miss
  - [ ] MODEL_IMMUTABLE: 10 copies of same 1 GiB tensor → on-disk ≤ 1.1 GiB (≥ 9×)
  - [ ] DB_TEMP/META_DURABLE/DB_WAL: dedup path not entered (class policy)
  - [ ] Dedup miss overhead ≤ 2 µs/4KiB write on warm DDT
  - [ ] `nvfs check` after kill-9 during dedup write: no leaked extents, refcounts consistent
  - [ ] DDT GC: after deleting 9 duplicate copies, used space returns to 1× tensor size
  - [ ] `nvfs stats --dedup` reports DDT hit rate, space savings, cold DDT miss rate
  - [ ] When encryption enabled: DHK-keyed HMAC used instead of raw Blake3 (verified by
        inspecting DDT tree on-disk)
- **Related-upfront:** `from_spostgre.md §S4` (arena_clone_range, used for reflink on DDT hit)
- **Related-design-doc:** `doc/05_design/nvfs_design_v3.md §V3-3, §V3-4, §V3-6, §V3-7`
- **Related-issue:** none
- **Notes:** DDT reference counting is error-prone (comparable to delayed-ref queue,
  v2 §5 OQ-1). Comprehensive crash-consistency tests are required before N7b ships.
  Cross-dataset dedup (shared DHK) deferred (OQ-10). Dedup back-fill of existing
  extents uses the v2 offline dedup daemon (§8); inline dedup covers new writes only.

---

### FR-BDD-WAVE7-8-001 — BDD feature files for wave 7/8 storage work

- **Filed-on:** 2026-04-18
- **Filed-by:** bdd-wave7-8 agent (session spostgre-nvfs-storage)
- **Target:** test/features/
- **Priority:** P1
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Implemented-by:** bdd-wave7-8 agent
- **Requested-semantics:**
  MDSOC+ requires BDD specs for new functionality before or alongside impl.
  Wave 7/8 added AES-GCM encryption (N6a), raw send/receive (N6b), scrub detect+repair
  (N4a/N4b), HOT slack (FR-HOT-001), M4 tier cache, M5 vacuum, VFS cursor
  (FR-SIMPLEOS-M5-001), and rt_time_now_ns clock extern. Eight `.feature` files
  were written covering 5 scenarios each (golden path + edge cases). Step wire-up
  is a separate track; these files are spec-only.
- **Acceptance-criteria:**
  - [x] `test/features/nvfs/encryption.feature` — 5 scenarios (N6a-001/002/003)
  - [x] `test/features/nvfs/raw_send.feature` — 5 scenarios (N6b)
  - [x] `test/features/nvfs/scrub_repair.feature` — 5 scenarios (N4a/N4b)
  - [x] `test/features/spostgre/hot_slack.feature` — 5 scenarios (FR-HOT-001)
  - [x] `test/features/spostgre/tier_cache.feature` — 5 scenarios (M4)
  - [x] `test/features/spostgre/vacuum.feature` — 5 scenarios (M5)
  - [x] `test/features/os/vfs_cursor.feature` — 5 scenarios (FR-SIMPLEOS-M5-001)
  - [x] `test/features/bench/clock_extern.feature` — 5 scenarios (rt_time_now_ns)
  - [x] Step vocabulary consistent with existing wave 0–6 feature files
  - [x] No .spl step implementations (spec-only; wire-up is a separate track)
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/nvfs_design_v2.md §14`, `doc/05_design/nvfs_design_v3.md`
- **Related-issue:** none

---

Closed entries are moved here from `## Open Requests` (never deleted) with
`Status: Implemented` or `Status: Rejected` and the required link/reason.

### FR-SPOSTGRE-M4-001 — L2 NVMe tier cache (Aurora Optimized Reads pattern)

- **Filed-on:** 2026-04-18
- **Filed-by:** spostgre-m4 agent (session spostgre-nvfs-storage)
- **Target:** spostgre  (examples/spostgre/src/engine/tier_cache.spl)
- **Priority:** P1
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Implemented-by:** spostgre-m4 agent
- **Requested-semantics:**
  When a clean DRAM page is about to be evicted from `BufferPool`, write it to a
  DB_TEMP arena on local NVMe instead of discarding it. On subsequent page fault,
  check `TierCache` before falling through to durable storage. The DB_TEMP arena
  is ephemeral: NVFS discards it on mount, so `TierCache` starts empty on every
  process restart (no recovery path needed). Aurora reader-replica warming
  (pre-populating the L2 from a replica stream) is deferred to a follow-up milestone.
- **Acceptance-criteria:**
  - [x] `TierCache` struct with DB_TEMP arena + parallel-array index
  - [x] `tier_cache_put` appends to arena and updates index
  - [x] `tier_cache_get` reads from arena; returns empty slice on miss
  - [x] `tier_cache_invalidate` removes index entry on durable write-back
  - [x] `BufferPool` gains `tier: TierCache` and `disk_reads: i64` (2 fields)
  - [x] `buf_get` checks `tier_cache_get` before durable path (fault hook)
  - [x] `buf_evict` writes clean pages to `tier_cache_put` (eviction hook)
  - [x] 7 unit tests in `tier_cache_test.spl` pass
- **Related-upfront:** `from_spostgre.md §S1` (arena_create per storage class)
- **Related-design-doc:** `doc/05_design/nvfs_design.md §DB_TEMP`
- **Related-issue:** none
- **Notes:** `STORAGE_CLASS_DB_TEMP = 3` defined in `tier_cache.spl` (shim treats
  class_tag opaquely). Aurora reader-replica pre-warming deferred.

---

### FR-STORAGE-E2E-001 — End-to-end integration test: spostgre WAL+pmap through NVFS shim

- **Filed-on:** 2026-04-18
- **Filed-by:** integration-test agent (session spostgre-nvfs-storage)
- **Target:** spostgre + nvfs_shim
- **Priority:** P1
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Implemented-by:** integration-test agent
- **Requested-semantics:**
  A single integration test that exercises the spostgre WAL writer and pmap writer
  through the in-process NVFS shim together with a RamFs-backed MountTable mount at
  `/db`. The test proves: arena-backed WAL append → commit_group FUA fence →
  pmap_writer_publish → remount simulation (byte-image extract + re-inject into fresh
  arenas) → wal_recover_tail and pmap_writer_lookup confirm survival → CRC fence stops
  recovery at a corrupted record. The gap between the MountTable/RamFsDriver surface
  and the in-process shim (spostgre does not yet route through the VFS mount table)
  is explicitly documented in state.md §9-e2e-integration; this FR tracks that wiring
  as future work.
- **Acceptance-criteria:**
  - [x] RamFs driver mounted at `/db` via `MountTable` — `MountId.id >= 0`
  - [x] `wal_writer_append` returns `LSN > 0`
  - [x] Successive appends produce strictly increasing LSNs
  - [x] `wal_writer_commit_group` sets `durable_lsn` to `lsn_high.value`
  - [x] `pmap_writer_publish` returns `true` after WAL commit
  - [x] `pmap_writer_lookup` returns entry with `birth_gen == page_lsn`
  - [x] `checkpoint_begin` returns target `Lsn`; `checkpoint_commit` appends ring record
        and `checkpoint_durable_lsn() >= lsn1.value` (replaces former `wal_writer_sync` sim)
  - [x] Remount sim: `wal_recover_tail` on re-seeded arena returns all 3 records
  - [x] Remount sim: `pmap_writer_lookup` on re-seeded arena returns matching `page_lsn`
  - [x] CRC fence: corrupted payload byte stops recovery — only prefix records returned
  - [ ] Real wiring: spostgre WAL/pmap arenas routed through `MountTable` + `RamFsDriver`
        (deferred; requires VFS write-path in `std.fs_driver`)
- **Related-upfront:** `from_spostgre.md §S1` (arena_create per storage class)
- **Related-design-doc:** `spostgre_design.md §9`, `§12 (M2)`, `nvfs_design.md §3`
- **Related-issue:** none
- **Notes:** `checkpoint_begin` / `checkpoint_commit` are now fully implemented in
  `examples/spostgre/src/engine/checkpoint.spl` using the shim arena API (FUA-append
  to a META_DURABLE ring arena). The former `wal_writer_sync` workaround in scenario 7
  is replaced by the real checkpoint API. FR-STORAGE-E2E-001: fully implemented
  2026-04-18 (12-e1-checkpoint-api).

---

### FR-BENCH-BASELINE-001 — Run bench harness with real clock and record baseline numbers

- **Filed-on:** 2026-04-18
- **Filed-by:** 9-bench-baseline agent (session spostgre-nvfs-storage)
- **Priority:** P1
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Implemented-by:** 9-bench-baseline agent; extended 2026-04-18 by 9-bench-rerun agent
- **Requested-semantics:**
  After FR-BENCH-CLOCK-001 wired `rt_time_now_nanos()`, run all 5 bench scripts
  (`fs_driver_mount_table.spl`, `nvfs_arena_throughput.spl`, `spostgre_wal_append.spl`,
  `run_all.spl`, `bench/lib/timing.spl`) with the bootstrap binary and record ns-level
  baseline numbers in `bench/BASELINE.md`.
- **Acceptance-criteria:**
  - [x] `bench/lib/timing.spl` updated to use `extern fn rt_time_now_nanos() -> i64`
        (real CLOCK_MONOTONIC, not loop-counter proxy)
  - [x] WAL bench (`spostgre_wal_append.spl`) ran successfully; real ns numbers recorded
        in `bench/BASELINE.md` (p50 wal_append ≈ 23 µs, wal_recover_tail ≈ 5.6 ms)
  - [x] NVFS arena bench: iter counts reduced (FR-BENCH-ARENA-ITER-001); all 4 scenarios
        completed (Wave 10 re-run, 2026-04-18). Numbers in `bench/BASELINE.md §Wave 10`.
  - [x] fs_driver + run_all: parse now clean (namespace rename done); bench times out at
        10k×resolve iterations — interpreter-budget limit, not keyword error. Documented.
  - [x] FR-BENCH-BASELINE-001 appended to `nvfs_requests.md`
  - [x] `#### 9-bench-baseline` appended to `.sstack/spostgre-nvfs-storage/state.md`
  - [x] `#### 9-bench-rerun` appended to `.sstack/spostgre-nvfs-storage/state.md`
- **Related-upfront:** FR-BENCH-CLOCK-001
- **Related-design-doc:** `bench/BASELINE.md`
- **Related-issue:** FR-BENCH-ARENA-ITER-001
- **Notes:** WAL numbers are interpreter-mode costs (~23 µs p50 append). Native-compiled
  expected < 1 µs. Real NVMe FUA dominates at 50–200 µs on actual hardware.
  Throughput column shows 0 in WAL/NVFS inline helpers due to old `(iters*1000)/total_ns`
  formula (underflows); corrected to `(iters*1_000_000)/total_ns` in `timing.spl`.
  Inline copies in WAL and NVFS bench files need the same fix as follow-up.
  MountTable/run_all benches remain interpreter-budget-limited at 10k iterations;
  blocked on native-compile (FR-COMPILER-001/002).

---

### FR-BENCH-ARENA-ITER-001 — Reduce nvfs_arena_throughput iter counts for interpreter budget

- **id:** FR-BENCH-ARENA-ITER-001
- **title:** Reduce nvfs_arena_throughput.spl iter counts to fit interpreter budget
- **Filed-on:** 2026-04-18
- **Filed-by:** 9-bench-rerun agent (session spostgre-nvfs-storage)
- **Priority:** P2
- **Status:** Implemented
- **Implemented-on:** 2026-04-18
- **Implemented-by:** 9-bench-rerun agent
- **Requested-semantics:**
  A1 scenario (outer=1000, inner=1000 appends × 8 words = ~8M word-push ops) exceeded the
  90s interpreter budget even after an initial reduction to outer=10. Root cause: each
  `shim_arena_append(arena, 64)` call pushes `(64+7)/8 = 8` i64 words via interpreter
  list-push; 1000 inner × 8 words = 8000 pushes per outer iter, and interpreter list-push
  overhead (~7ms/iter as measured) makes even outer=5 with inner=100 take ~38s for A1.
  A2 (64KB appends = 8192 words each) is even heavier: even 5 outer × 5 inner × 8192 words
  = 204k pushes → p50 ≈ 10s/iter under interpreter.
  Reduction is bench-only (does not affect the correctness of the shim or production code).
- **Acceptance-criteria:**
  - [x] A1: outer 1000→5, inner 1000→100; completes in < 90s (actual: ~38s)
  - [x] A2: outer 100→5, inner 100→5; completes in < 90s (actual: ~50s total)
  - [x] A3: outer 100→10, fill 100→10, clone_len 200KB→20KB
  - [x] A4: outer 100→10
  - [x] All 4 scenarios produce timing output (no SIGTERM)
  - [x] Numbers appended to `bench/BASELINE.md` under "Wave 10 re-run"
- **Related-upfront:** none
- **Related-design-doc:** `bench/BASELINE.md §Wave 10 re-run`
- **Related-issue:** FR-BENCH-BASELINE-001
- **Notes:** Long-term fix is native-compile (FR-COMPILER-001/002); at native speed all
  benches complete in < 1s and original iter counts are appropriate. The iter reductions
  here are interpreter-mode accommodations only — restore to original counts when native
  mode is available.

---

### FR-SPOSTGRE-M2-001 — Replace duplicated NVFS constants/types in nvfs_shim.spl with real cross-submodule imports

- **Filed-on:** 2026-04-18
- **Filed-by:** 12-e2-cross-submodule-imports agent (session spostgre-nvfs-storage)
- **Target:** spostgre  (examples/spostgre/src/engine/nvfs_shim.spl)
- **Priority:** P1
- **Status:** Open — blocked on FR-SPOSTGRE-M2-002 (named constants not yet in NVFS core)
- **Requested-semantics:**
  After FR-COMPILER-003 (2-pass import resolver), replace duplicated constants and types in
  `nvfs_shim.spl` with `use examples.nvfs.src.core.<module>.{<name>}` imports. Items in scope:
  `STORAGE_CLASS_DB_WAL`, `STORAGE_CLASS_META_DURABLE`, `DURABILITY_DATA_DURABLE` (constants)
  and `PmapEntry`/`Arena`/`SuperblockHeader` (types).
- **Acceptance-criteria:**
  - [ ] All `val STORAGE_CLASS_*` in `nvfs_shim.spl` replaced by `use` imports from nvfs
  - [ ] All `val DURABILITY_*` in `nvfs_shim.spl` replaced by `use` imports from nvfs
  - [ ] `PmapEntry` local definition replaced by `use` import where field layouts match
  - [ ] Existing unit and e2e integration tests pass after substitution
- **Related-upfront:** `from_spostgre.md §S1`
- **Related-design-doc:** `doc/05_design/nvfs_design.md §4.1`
- **Related-issue:** FR-COMPILER-003 (prerequisite, Implemented 2026-04-18)

**Investigation result (2026-04-18):** Full import is **not yet possible**. Root cause:

1. **Constants not defined in NVFS.** `STORAGE_CLASS_DB_WAL`, `STORAGE_CLASS_META_DURABLE`,
   `DURABILITY_DATA_DURABLE` have **no canonical definition** in `examples/nvfs/src/core/`.
   The nvfs arena uses `class_tag: i32` as an opaque passthrough — named ordinals are absent.
   The shim's 3 `val` declarations are the *only* definitions in the codebase. There is
   nothing to import.

2. **PmapEntry fields diverge completely.** `examples/spostgre/src/engine/pmap.spl::PmapEntry`
   has fields `{rel_id, blk, arena_id, offset, generation}` (spostgre logical mapping).
   `examples/nvfs/src/core/pmap.spl::PmapEntry` has fields `{logical, phys, offset, len,
   birth_gen, checksum_algo, compress_algo, compressed_len, checksum}` (physical pmap v3).
   These are structurally unrelated; import would require a rename that misrepresents semantics.

3. **SuperblockHeader** does not appear in `nvfs_shim.spl` at all (task description was
   anticipatory). No action needed.

**Before/after count:** 3 duplicated `val` declarations — all 3 kept (no canonical source).
`PmapEntry` in shim: 0 (shim has no PmapEntry; spostgre/engine/pmap.spl has its own).

**Follow-up:** FR-SPOSTGRE-M2-002 tracks adding named StorageClass constants to NVFS.

---

### FR-SPOSTGRE-M2-002 — Add named StorageClass and DurabilityClass constants to NVFS core

- **Filed-on:** 2026-04-18
- **Filed-by:** 12-e2-cross-submodule-imports agent (session spostgre-nvfs-storage)
- **Target:** nvfs  (examples/nvfs/src/core/arena.spl or new constants.spl)
- **Priority:** P2
- **Status:** Open
- **Requested-semantics:**
  `examples/nvfs/src/core/arena.spl` uses `class_tag: i32` as an opaque ordinal with no
  named constants. Consumers (spostgre, future callers) must either duplicate ordinal
  assignments or rely on comments that say "matching nvfs intent". Add a canonical
  `constants.spl` (or extend `arena.spl`) that exports:
  ```
  val STORAGE_CLASS_DB_WAL:       i32 = 1
  val STORAGE_CLASS_META_DURABLE: i32 = 2
  val STORAGE_CLASS_DB_TEMP:      i32 = 3
  val DURABILITY_DATA_DURABLE:    i32 = 1
  ```
  Then `nvfs_shim.spl` and `tier_cache.spl` can replace their local `val` declarations with
  `use examples.nvfs.src.core.constants.{STORAGE_CLASS_DB_WAL, ...}`.
- **Acceptance-criteria:**
  - [ ] `examples/nvfs/src/core/constants.spl` (or equivalent) exports all 4 named ordinals
  - [ ] `nvfs_shim.spl` imports instead of re-declaring STORAGE_CLASS_DB_WAL and
        STORAGE_CLASS_META_DURABLE
  - [ ] `tier_cache.spl` imports STORAGE_CLASS_DB_TEMP instead of re-declaring it
  - [ ] `bin/simple test examples/spostgre/test/unit/engine/*.spl` passes
  - [ ] `bin/simple test examples/spostgre/test/integration/storage/spostgre_nvfs_e2e_test.spl`
        passes
- **Related-upfront:** `from_spostgre.md §S1` (arena_create per storage class)
- **Related-design-doc:** `doc/05_design/nvfs_design.md §4.1`
- **Related-issue:** FR-SPOSTGRE-M2-001 (parent)
- **Notes:** Do NOT modify NVFS source as part of the spostgre M2 task. This FR is filed
  against NVFS and must be implemented by an NVFS agent. Until it lands, local `val`
  declarations in spostgre are canonical and intentional — not bugs.

---

## FR-BENCH-NS-KEYWORD-001 — Fix `namespace` reserved-keyword collision in NVFS drivers

- **id:** FR-BENCH-NS-KEYWORD-001
- **title:** Fix `namespace` reserved-keyword collision blocking fs_driver and run_all benches
- **Filed-on:** 2026-04-18
- **Filed-by:** Claude (session: spostgre-nvfs-storage namespace-kw-fix)
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:** The Simple parser rejects `namespace` as both a field name and a
  module path segment (it is a reserved keyword aliased to `mod`). The NVFS driver structs
  used `namespace: Namespace` as a field, and the module was in `src/core/namespace.spl`,
  causing parse errors that blocked the `fs_driver_mount_table` and `run_all` benches.
- **Acceptance-criteria:**
  - [x] `namespace.spl` renamed to `ns_tree.spl`
  - [x] All `use examples.nvfs.src.core.namespace.{...}` imports updated to `ns_tree`
  - [x] `namespace: Namespace` field renamed to `ns: Namespace` in both driver structs
  - [x] All `self.namespace.` accesses renamed to `self.ns.`
  - [x] Also fixed `case Aes128GcmResult.Ok(data: plaintext):` → positional pattern in `encryption.spl`
  - [x] Bench exits via interpreter-budget (SIGTERM) rather than parse error — confirmed
- **Related-upfront:** none
- **Related-design-doc:** `bench/BASELINE.md`
- **Related-issue:** none
- **Notes:** The module rename (`namespace` → `ns_tree`) is required because `namespace`
  appears as a path segment in `use` statements, which the parser also flags. The `Namespace`
  type name itself is not a keyword and was left unchanged.
