# SimpleOS path-based POSIX syscalls: fake success replaced with honest ENOSYS; real FAT32 backend exists but is not wired to the syscall path

Status: PARTIALLY FIXED 2026-08-06 (honesty landed 2026-08-06 AM; kernel-global
mount + open/stat/mkdir/readdir/unlink/rmdir wiring landed 2026-08-06 PM;
read/write-after-open wiring landed 2026-08-06 evening, see "Update 3" below;
Wall 2 (mount-accessor persistence) INVESTIGATED and CONFIRMED REAL 2026-08-06
night — see "Update 4" below; boot-reachability still open)

## Ownership update 2026-08-14 — ARM64 database atomic-replace boundary claimed

Owner: `/root/arm_file_rename_owner` (SimpleOS server execution matrix lane).

Initial source inspection found the boot-kernel runtime's fatal
`S2(rt_file_rename)` trap, but retained target-object evidence corrected that
scope: the ARM64 **user payload** runtime archive exports a strong
`rt_file_rename` from `simple_core/core_fs.spl`, with an unresolved `rename`
that the SimpleOS libc maps to syscall 44.  The runtime boundary is therefore
present for the server payload.  The real kernel syscall below it reaches
`Fat32Filesystem.rename_at`, but that primitive is link-new/delete-old, returns
`EEXIST` for an existing destination, and is explicitly non-atomic across its
directory-entry writes.  Therefore neither the existing mapping nor unlinking
the destination first can honestly implement the canonical database owner's
atomic replacement commit.

Claimed acceptance boundary: keep the database adapter fail-closed, distinguish
"runtime rename is not linked" from "linked FAT32 rename cannot atomically
replace", and retain focused source/object-symbol evidence.  Current target
classification is the latter.  Unblock only when
the mounted target filesystem has one crash-consistent atomic replace owner
(including destination replacement) and the ARM runtime maps `rt_file_rename`
to that owner without a trap/fallback.  No full payload rebuild is authorized
in this lane.

## Update 4 (2026-08-06, this lane): Wall 2 confirmed REAL, root-caused, and NOT independently fixable in this pass — same pre-existing, already-closed seed-only defect, not a new bug

**Verdict up front:** Wall 2 is real. It reproduces exactly as "Update 3"
described. It is **not** a new defect and **not** specific to
`fat32_mount_dev()`/`fat32_mount_fs()`, `BlockDevice`, or FAT32 at all — it is
the same universal, already-diagnosed, already-CLOSED seed-interpreter defect
tracked in
`doc/08_tracking/bug/interp_trait_slot_receiver_reboxed_per_call_mutation_loss_2026-07-07.md`
("Copy at `Optional` bind, universally"). That doc's own "Why no fix here"
section applies unchanged: the seed is bootstrap-only and repairing its value
model is out of scope for pure-Simple-first work. No code fix is landed in
this update; what follows is the reproduction, exact matching, and a scoped
severity re-assessment specific to FAT32/board-runnable concerns.

### Direct reproduction (this session, not committed — throwaway diagnostic)

A minimal spec, structurally identical to "Update 3"'s data point 3, calling
`fat32_mount_dev()` from two genuinely separate top-level functions (not
nested in one scope):

```
fn _write_via_separate_call():
    val dev = fat32_mount_dev()
    dev.write_sector(99u64, marker_byte_0x42)

fn _read_via_separate_call() -> u8:
    val dev = fat32_mount_dev()
    dev.read_sector(99u64)[0]
```

Run via `bin/simple test <file>` (the harness every FAT32 spec in this repo
runs under): `expected 0 to equal 66` — the write made in
`_write_via_separate_call()` is invisible to the read in
`_read_via_separate_call()`. Confirmed, not a harness artifact: the write IS
visible when both operations run against the SAME held local reference
(matching "Update 3"'s data point 1), only breaking across two separate
`fat32_mount_dev()` fetches — the defining signature of the closed bug.

### Root cause — confirmed, not new

`bin/simple test` unconditionally delegates to the Rust seed's child process
regardless of which `bin/simple` invoked it (see
`.claude/memory/ref_*` note "`simple test` silently delegates to seed
child"); this session's repro's own output shows `child binary:
.../src/compiler_rust/target/debug/simple`. The seed interpreter represents a
class instance as `Object { class, fields: Arc<HashMap<String, Value>> }`
(`src/compiler_rust/compiler/src/value.rs:1161`) and mutates via
`Arc::make_mut(fields)`
(`src/compiler_rust/compiler/src/interpreter/place.rs:132,176-177`) — pure
copy-on-write value semantics. `g_fat32_mount_dev: BlockDevice? = nil` is
exactly the trigger shape the closed bug names: an `Option`-wrapped
class/trait instance held in a module-level `var`, unwrapped fresh on every
call (`fat32_mount_dev()` calls `.unwrap()` each time) — each unwrap forks a
new copy of the underlying fields map, so a write through one fetch is
invisible to the next. The already-closed bug doc states this was fixed for
the **product** self-hosted interpreter as of `29c2a91a030` (2026-07-04);
this session could not independently re-confirm that against the product
interpreter specifically, because the `bin/simple` currently deployed at this
repo root (`bin/release/x86_64-unknown-linux-gnu/simple`) prints the
bootstrap-seed warning banner itself, and the only non-seed-flagged binary
found (`bootstrap/stage3/x86_64-unknown-linux-gnu/simple`) supports only
`compile`/`native-build` — no `test` or interpreted `run` — so it cannot
execute this repro's spec form at all.

### Attempted the same repro on the path that actually matters for
board-runnable: native codegen

Since the real kernel ships as a native-compiled binary, not interpreted
code, whether the interpreter's COW bug applies is secondary to whether
native codegen handles this shape at all. A userspace analog (same
trait/class/`Option`-global/two-separate-calls shape) was compiled with
`bootstrap/stage3/.../simple native-build`: it does **not** compile. MIR
lowering cannot resolve a trait method called through
`Option<Trait>.unwrap()` — it logs `unresolved method call 'write_it' lowered
to const-0 placeholder (silent-null risk, Task #145)`, then hits `MIR error:
unresolved method call: unwrap` / `unresolved method call: read_it` and the
compiler process core-dumps. This is a **different, deeper, pre-existing gap**
in native trait dispatch (consistent with the already-tracked
`native_with_trait_impl_no_vtable_duck_trap_2026-07-28.md`), not evidence the
COW-copy bug does or doesn't reproduce natively — the pattern doesn't reach
codegen at all today.

### Severity/blast-radius re-assessment (narrower than "Update 3" feared)

- **Confirmed affected:** the seed-interpreter test harness (`bin/simple
  test`), which is how every existing FAT32 spec in this repo runs. Any spec
  that writes through one `fat32_mount_dev()`/`fat32_mount_fs()` fetch and
  reads back through a separately-fetched reference will silently see stale
  data. This is exactly why "Update 3"'s own new specs were written to build
  a **fresh `Fat32Filesystem` from the SAME `dev` local variable** every time
  (`_fs_from(dev)` takes `dev: MockDev` directly, never re-fetching through
  `fat32_mount_dev()`), not through the mount accessors — that pattern
  happens to sidestep the bug, but not by design against this specific
  defect.
- **NOT currently reachable on real hardware/board or QEMU:** the only real
  `BlockDevice` implementer, `CNvmeBlockAdapterFs`
  (`src/os/kernel/boot/c_nvme_adapter.spl`), is an intentional link-clean stub
  whose `read_sector`/`write_sector` unconditionally return `Err(...)` — it
  does no real I/O today (pre-existing gap, "Update 2"/"Update 3"), and
  `boot_fs_mount_fat32_from_device` still has no live-boot caller. So even if
  the COW bug reproduced identically on real hardware, there is currently no
  code path that would exercise it there.
- **Also structurally lower-risk than feared for a *real* `BlockDevice`:** the
  in-memory `MockDev` used by every FAT32 spec stores sector bytes as a
  Simple-level struct-array field (`sectors: [MockSector]`), which is exactly
  what the COW-copy bug corrupts. A real hardware/NVMe adapter instead holds
  a raw MMIO address (`sector_buf_addr: u64`) and would do reads/writes via
  FFI/`mmio_*` primitives against that fixed address, not via Simple-level
  field mutation on the class instance — so even once a real block device is
  wired in, it plausibly would not trigger this specific copy-on-unwrap
  mechanism the way the mock does. This is a plausibility argument, not
  proof; it should be re-verified once a real `BlockDevice` implementer with
  actual I/O exists.

### Why no fix lands in this update

The applicable fix (repair the seed interpreter's `Arc<HashMap>` COW value
model) is explicitly out of scope per the existing closed bug's own "Why no
fix here": the seed is bootstrap-only, repairing it is a refactor of a
bootstrap-only engine, against the pure-Simple-first rule, and the product
interpreter is already claimed correct for this shape. This session could not
independently verify the product-interpreter claim (no runnable non-seed
interpreter binary was available), and the native path — the one that
actually matters for board-runnable — does not compile this shape at all
today, a separate pre-existing gap. No `.spl`-level workaround was applied to
`fat32_mount_dev()`/`fat32_mount_fs()` either: the established workaround from
the closed bug (keep mutable state in a module-level `var`, not behind a
`Trait?`-typed accessor) does not generalize to an arbitrary `BlockDevice`
implementer's internal state without changing the trait's shape, and no
concrete near-term consumer needs it fixed today (the only real implementer
is a no-op stub; every current syscall handler fetches `fs`/`dev` once per
call and stays self-consistent, matching the one case that already works).

**Recorded as an open, scoped follow-up, not silently dismissed:** before a
real `BlockDevice` (real NVMe/virtio-blk) is wired to
`fat32_mount_publish`, re-run this exact write-then-read-via-separate-fetch
repro against that real implementer (or, failing real hardware, first get the
native-codegen trait-dispatch-through-`Option.unwrap()` gap fixed so an
in-QEMU native repro becomes possible at all) to confirm or rule out the same
failure mode before trusting cross-syscall FAT32 correctness for anything
beyond a single self-contained syscall call.

## Update 3 (2026-08-06, this lane): fd read/write reach FAT32 for real — plus a critical, deeper wall found while verifying it

**What's real now.** `_handle_file_open` (`src/os/kernel/ipc/syscall_file.spl`)
now allocates the fd typed `FD_TYPE_FAT32` (new constant, `src/os/kernel/fd_table.spl`)
instead of the generic `FD_TYPE_FILE` that `os.kernel.fd_io`'s
`posix_read`/`posix_write` route to `sosix_sync_read`/`sosix_sync_write` (a
subsystem with no FAT32 backend — the exact gap "Update 2" flagged). The real
`Fat32Filesystem.FileHandle` `open_at`/`create_at` returns is registered,
keyed by `(task_id, fd)`, in a new module `src/os/kernel/fs/fat32_fd_table.spl`
(`fat32_fd_register`/`fat32_fd_is_registered`/`fat32_fd_clear`/
`fat32_fd_read_into`/`fat32_fd_write_from`). `_handle_file_read`/
`_handle_file_write` now check `fd_get_type(fd) == FD_TYPE_FAT32` and, when
true, call `fat32_fd_read_into`/`fat32_fd_write_from` (real
`Fat32Filesystem.read`/`.write` calls against the mounted filesystem) instead
of falling through to `posix_read`/`posix_write`. `_handle_file_close` purges
the fd's table entry before the fd number is released back to `fd_alloc`, so
a reused fd cannot observe a stale handle. `_handle_lseek` now explicitly
returns `-ENOSYS` for `FD_TYPE_FAT32` fds rather than falling through to
`posix_lseek` (which writes an offset scalar nothing in the FAT32 path reads,
and whose `SEEK_END` branch sends IPC to the never-spawned "VFS service"
documented elsewhere in this file — reachable now that FAT32 fds are real,
so it had to be closed off, not just left as a latent trap).

**Why a separate module.** `os.kernel.ipc.syscall_file` transitively imports
`os.kernel.ipc.syscall`'s huge dependency graph (scheduler/vmm/pmm/ipc/ELF
loader/...). The fd-table logic (task-scoped keys, offset-delta
re-application after a value-type `FileHandle` read, the append-only honesty
guard below) was split into `os.kernel.fs.fat32_fd_table`, which imports only
`os.kernel.fs.fat32` — the same import weight as `fat32_mount_and_dir_ops_spec.spl`
(passes 8/8) — specifically so it could be unit-tested for real instead of
only reachable through a spec that (see below) cannot currently run.

**Task-scoped, not fd-only, keying.** `os.kernel.fd_table`'s fd numbers are
per-task-context (`fd_context_*` arrays + `fd_activate_task`): two different
tasks can legitimately both hold fd 3 for two entirely different files. The
new table is keyed by `(task_id, fd)`, mirroring `g_cwd_table`'s
`task_id`-keying in the same file, for exactly this reason — a fd-only key
would let one task's read/write observe or corrupt another task's handle.

**Append-only honesty guard.** `Fat32Filesystem.write` is APPEND-ONLY — it
always writes at `h.file_size`, never at an arbitrary tracked read offset.
That matches POSIX for a fresh/empty file (`offset == file_size == 0`), but
for an EXISTING non-empty file reopened for write, POSIX expects a plain
`write()` to overwrite starting at offset 0 — silently calling the
append-only primitive there would write the right bytes to the WRONG place
with no error. `fat32_fd_write_from` refuses this with `Err(-ENOSYS)` when
`handle.offset != handle.file_size` instead of fabricating overwrite support
`Fat32Filesystem.write` does not have. **Concretely: `open(path, O_CREAT |
O_WRONLY)` on a path that already exists and is non-empty, followed by
`write()`, now returns `-ENOSYS` on that write** — the ordinary "create-or-
overwrite" flow does not work end-to-end for an existing file today. Only
create-fresh-then-write (or append-after-append, when both writes go through
without an intervening reopen) is supported.

### Test evidence (real, passing, sabotage-verified)

`test/01_unit/os/kernel/fs/fat32_fd_table_spec.spl` (6/6 passing) covers, via
the actual `fat32_fd_register`/`fat32_fd_write_from`/`fat32_fd_clear` entry
points `_handle_file_open`/`_handle_file_write`/`_handle_file_close` call —
not `Fat32Filesystem` directly:

- a fresh `create_at` + register + write returns the payload's real,
  disk-backed byte count;
- `EBADF` (`-9`) on an fd nothing ever registered;
- clear-on-close makes a reused fd number unable to observe a stale handle;
- two tasks holding the SAME fd number write to two different files
  independently, no crash or cross-task collision;
- the append-only guard both allows the supported case (`offset ==
  file_size`) and refuses the unsupported one (`offset != file_size` ->
  `-ENOSYS`), evaluated purely from the registered handle's own fields
  before any disk I/O is attempted.

**Sabotage-verified this session** (each: broke it, confirmed the specific
example(s) went red, restored, confirmed green again):
1. Replacing `fat32_fd_write_from`'s `Ok(bytes.len() as u64)` with `Ok(0u64)`
   dropped the suite from 6/6 to 4/6 (both the "write returns the real byte
   count" example AND the "two tasks... independently" example went red,
   since the latter also checks byte counts).
2. Replacing the `handle.offset != handle.file_size` guard condition with
   `false` (never refuse) dropped the suite to 5/6 — the "refuses ENOSYS"
   example went red (got `Ok` instead of `Err`).
3. Removing `task_id` from `_fat32_fd_index`'s equality check (comparing `fd`
   alone) dropped the suite to 5/6 — the "two tasks, same fd number" example
   went red.

Existing `fat32_write_path_spec.spl` (25/25) and
`fat32_mount_and_dir_ops_spec.spl` (8/8) still pass unmodified — no
regression in the primitives/mount-publish infrastructure this change reuses.

### Wall 1 (narrows, does not confirm, "Update 2"'s stated cause): a spec importing `os.kernel.ipc.syscall_file` reproducibly fails `no examples executed` — but NOT because of import weight

"Update 2" attributed this to the size of the `os.kernel.ipc.syscall`
dependency graph. That attribution is **wrong, or at least incomplete** — a
trivial one-line spec (`use os.kernel.ipc.syscall_file.{_handle_file_open}`
+ a single `it "reaches this file": assert_true(true)`, nothing else) with
the IDENTICAL import graph **passed 1/1** on this same deployed binary.
Narrowed further with a second trivial probe: a spec whose single `it` body
does nothing but `Scheduler.new()`, `IpcManager.new()`, `pmm_alloc_page_raw()`,
`vmm_map_page(...)` — the exact userspace-page-mapping recipe
`syscall_spec.spl` established for calling `_handle_file_*` with real
arguments — reproduces `error: test-runner: no examples executed` on its
own, with NO `os.kernel.ipc.syscall_file` import at all. **The actual trigger
is calling `pmm_alloc_page_raw`/`vmm_map_page`/`Scheduler.new()` (freestanding
kernel memory/scheduler primitives that assume a running kernel, not a
userland test process) from inside a spec `it` body**, not the size of any
import graph. This is why a syscall-DISPATCH-level round-trip test
(`_handle_file_open` -> `_handle_file_write` -> `_handle_file_close` ->
reopen -> `_handle_file_read`, with real userspace pages) could not be
written for this change, or for "Update 2"'s six handlers either — every
attempt that constructs a real `Scheduler` and maps a real page hits this
wall. Not something this lane introduced or can fix within its own scope.
`test/01_unit/os/kernel/abi/syscall_shim_spec.spl`'s own header independently
documents the same constraint for a sibling module ("These tests verify the
shim's public surface... They do NOT invoke shims because that requires
kernel context").

### Wall 2 (NEW, more consequential, found while verifying this change): `fat32_mount_dev()`/`fat32_mount_fs()` do not reliably share write-visible state across two SEPARATE calls

This is the wall that actually blocks a genuine write-then-read round-trip
test, independent of Wall 1. Reproduced with a throwaway diagnostic spec
(not committed) against the same `MockDev`-shaped fixture
`fat32_mount_and_dir_ops_spec.spl`/`fat32_write_path_spec.spl` already use,
narrowed to four data points on the SAME published mount:

1. `write_sector` via ONE `fat32_mount_dev()` fetch, then `read_sector` via
   THE SAME held reference — sees the write. PASS.
2. `write_sector` via `fat32_mount_dev()`, then `read_sector` via the
   ORIGINAL `dev` variable that was passed INTO `fat32_mount_publish` — does
   NOT see the write (reads back the pre-write byte). FAIL.
3. `write_sector` via one `fat32_mount_dev()` call, `read_sector` via a
   SECOND, separate `fat32_mount_dev()` call — does NOT see the write. FAIL.
4. The same failure reproduces one level up: `fat32_mount_fs().write(dev,
   h0, bytes)` (the exact idiom every `_handle_file_*` handler uses:
   fetch `fs`/`dev` once, write once) followed by reading the sector back
   through that SAME fetched `dev` — FAILS to see the write, even though
   data point 1 (bare `write_sector`/`read_sector` on the same reference,
   no `Fat32Filesystem` in between) passes.

Ruled out: mutating trait methods needing `me` — the mock's
`read_sector`/`write_sector` were changed from plain `fn` to `me
read_sector`/`me write_sector` (matching the real `CNvmeBlockAdapterFs`
implementer's declaration) and re-run; the failure was unchanged. **This is
reported as OBSERVED BEHAVIOR with an exact reproduction, not a diagnosed
root cause** — the mechanism (Option<trait> boxing, a copy-on-pass semantics
gap, or something else in this compiler's trait-object handling) is not
confirmed and should not be assumed. `BlockDevice`
(`src/lib/nogc_sync_mut/fs_driver/block_device.spl`) is a `trait`; `fat32.spl`'s
own module doc for `g_fat32_mount_fs`/`g_fat32_mount_dev` explicitly reasons
that both are safe as bare `Option`-boxed globals because "`Fat32Filesystem`
and `BlockDevice` are both reference (class) types" — that reasoning is
correct for `Fat32Filesystem` (a `class`) but `BlockDevice` is a `trait`, a
different kind of type this codebase's Option<struct>-landmine family has not
previously covered.

**Why "Update 2"'s existing tests did not catch this.** The single
"kernel-global FAT32 mount publish" example in
`fat32_mount_and_dir_ops_spec.spl` that exercises `fat32_mount_fs()`/
`fat32_mount_dev()` at all does a READ-ONLY check (`published.stat_at(...)`)
against pre-seeded data — it never writes through the accessor and rereads.
Every other example in that file (and in `fat32_write_path_spec.spl`) calls
`Fat32Filesystem` methods on `fs`/`dev` DIRECTLY, never through
`fat32_mount_fs()`/`fat32_mount_dev()`. This wall was invisible to every
FAT32 test written before this session.

**Severity/scope, honestly stated, not resolved:** every `_handle_file_*`
handler in `syscall_file.spl` (both "Update 2"'s six and this lane's two)
fetches `fs`/`dev` via `fat32_mount_fs()`/`fat32_mount_dev()` ONCE per
syscall call and uses that fetch consistently for the rest of the call —
matching data point 1 above (same reference, self-consistent), not data
points 2-4. Whether writes done by one syscall call are visible to a LATER,
separate syscall call (e.g. `write()` then a subsequent `read()`, or
`mkdir()` then a subsequent `readdir()`) is **UNVERIFIED** and, per data
point 3, actively suspect: two independent `fat32_mount_dev()` fetches (no
`Fat32Filesystem` involved at all) fail to share state. It is also
**unconfirmed whether this threatens a real hardware-backed `BlockDevice`**
— the mock stores actual sector bytes as struct fields (`sectors: [MockSector]`),
so a copy diverges real data, whereas the one real implementer inspected,
`CNvmeBlockAdapterFs` (`src/os/kernel/boot/c_nvme_adapter.spl`), is a thin
handle (`sector_buf_addr: u64, ready: bool`) and is currently a link-clean
stub that always returns `Err` — it does no real I/O today either way, and
`boot_fs_mount_fat32_from_device` still has no caller in the live boot
sequence (pre-existing gap, "Update 2"). **This must be resolved — ideally
with a real hardware or QEMU-backed `BlockDevice` round-trip, since the mock
cannot currently prove it either way — before this FAT32 syscall path can be
trusted for anything beyond a single self-contained syscall call.**

A second write in a SEPARATE `fat32_fd_write_from` call on the same fd was
attempted as a spec example and dropped (not committed as a red spec) for
the identical reason: the second call's freshly-fetched device does not see
the first call's FAT-table cluster allocation, so `Fat32Filesystem.write`'s
internal chain re-walk fails. This is Wall 2 manifesting through the actual
feature this update ships, not just the diagnostic probes above.

## Update 2 (2026-08-06, this lane): kernel-global mount + six handlers wired for real

Implemented exactly the "Required next step" this doc specified, plus the two
directory-removal primitives it flagged as missing at every layer:

**`src/os/kernel/fs/fat32.spl`**
- New kernel-global mount state, mirroring the `g_cwd_table` lazy-scalar
  pattern in `syscall_file.spl` and the `vmm_publish_kernel_pml4` pattern in
  `vmm_core.spl`: `fat32_mount_publish(fs, dev)`, `fat32_mount_ready()`,
  `fat32_mount_fs()`, `fat32_mount_dev()`, `fat32_mount_clear()` (test-only).
  `Fat32Filesystem`/`BlockDevice` are reference types, so the `Option`-typed
  globals hold a plain nullable pointer — the codegen landmine about
  `Option<struct>` reading nil on the hit path does not apply here, and no
  `if val` binding-if is used on them regardless.
- New `Fat32Filesystem.readdir_at(dev, path)` — enumerates a directory's live
  entries (root or nested), reusing the same LFN-accumulation / 8.3-decode
  logic `fat32_dir_find_entry` already had (factored into a new free function
  `fat32_dir_list_entries`).
- New `Fat32Filesystem.unlink_at(dev, path)` — frees the file's whole FAT
  cluster chain via the existing `read_cluster_chain`/`_write_fat_entry`
  primitives, then marks the 32-byte dirent's first byte `0xE5` via a new
  `_mark_dirent_deleted` helper (same root_dir_data cache-sync guard
  `_update_dirent` already used). Refuses a directory with `EISDIR` (new
  const, `-21`).
- New `Fat32Filesystem.rmdir_at(dev, path)` — same free+mark-deleted shape,
  gated on the directory holding only `.`/`..` (`ENOTEMPTY`, new const `-39`),
  `ENOTDIR` on a file.
- **UPDATE 2026-08-06 (later same day):** `rename_at` WAS added — see
  "`rename` now real" below, which supersedes "`rename` deliberately left
  ENOSYS" further down this doc.

**`src/os/kernel/boot/boot_fs_mount.spl`**
- `boot_fs_mount_fat32_from_device` now does more than validate the BPB: on a
  successful `parse_bpb`, it constructs a `Fat32Filesystem`, calls
  `.mount(dev)`, and on success calls `fat32_mount_publish(fs, dev)`. A
  `mount()` failure after a valid BPB now returns `Err(...)` instead of
  reporting mounted.

**`src/os/kernel/ipc/syscall_file.spl`** — six handlers went from
unconditional `-ENOSYS` to real:
- `_handle_file_open` — resolves the path against cwd, calls
  `Fat32Filesystem.open_at` (falling back to `create_at` on `ENOENT` when
  `O_CREAT` is set), allocates a real fd via `os.kernel.fd_table.fd_alloc`/
  `fd_set`. Never returns 0 on this path (no stdin collision).
- `_handle_file_stat` — calls `stat_at`, builds a real `struct stat` byte
  image (mode/nlink/size/mtime at the offsets documented in
  `src/os/libc/include/sys/stat.h`'s x86_64 natural-alignment layout: mode
  `u32@16`, nlink `u64@24`, size `i64@48`, mtime `i64@80`, 96 bytes total),
  writes it via `mmio_write8` per byte — the same primitive `_handle_getcwd`
  already used for a userspace write.
- `_handle_file_mkdir` — calls `mkdir_at`.
- `_handle_file_readdir` — arg layout grew a path-length slot (`arg0`=path
  ptr, `arg1`=path len, `arg2`=buf ptr, `arg3`=buf size — the original
  IPC-stub signature never needed a path length since it never copied path
  bytes). Calls `readdir_at`, encodes names as NUL-terminated runs, writes
  them into the caller buffer, returns the entry count. Returns `-ERANGE`
  rather than silently truncating when the encoding doesn't fit.
- `_handle_file_unlink` — calls `unlink_at`.
- `_handle_file_rmdir` — calls `rmdir_at`.

All six are gated on `fat32_mount_ready()` and return `-ENOSYS` — never a
fabricated success — when nothing has published a mount yet.

**Tests:** `test/01_unit/os/kernel/fs/fat32_mount_and_dir_ops_spec.spl` (new,
8/8 passing) covers the mount-publish accessors and the three new
`Fat32Filesystem` methods end to end against a synthetic in-memory FAT32
volume (same `MockDev` shape `fat32_write_path_spec.spl` established),
including negative paths (ENOENT after unlink, ENOTEMPTY on a non-empty
rmdir, EISDIR unlinking a directory, ENOTDIR on both readdir and rmdir of a
file) and a re-read-through-a-fresh-view discipline so a cache-only mutation
cannot pass. **Sabotage-verified this session:** stubbing `unlink_at` to
`return Ok(())` before doing any real work dropped the suite to 7/8
(the "fresh stat_at reports ENOENT" example went red); disabling `rmdir_at`'s
`ENOTEMPTY` check (`... and false`) also dropped it to 7/8 (the
non-empty-directory example went red). Both restored to 8/8. Existing
`fat32_write_path_spec.spl` (25/25) and `fat32_subdir_spec.spl` (17/17) still
pass unmodified — no regression in the primitives this change reuses.

## Why this doc does NOT claim `_handle_file_*` were exercised through the syscall layer dynamically

Attempted first: a spec importing `os.kernel.ipc.syscall_file` and driving
`_handle_file_open`/`_handle_file_stat`/etc. directly, using the exact
`pmm_alloc_page_raw` + `vmm_map_page` + `mmio_write8`/`mmio_read8` userspace-page
recipe `test/01_unit/os/kernel/ipc/syscall_spec.spl` already established for
other syscall handlers. It failed with `error: test-runner: no examples
executed`. Before concluding this was caused by the change in this lane, the
EXISTING, completely unmodified `syscall_spec.spl` was run against the same
deployed `bin/simple` (confirmed via `readlink -f bin/simple` to be the
bootstrap-seed binary, not the self-hosted one) and produced the IDENTICAL
`error: test-runner: no examples executed` / `1 total, 0 passed, 1 failed`.
A rerun of `syscall_spec.spl` AFTER this lane's `syscall_file.spl` edits
produced the byte-identical failure (same line position in the log), i.e. no
new/different failure was introduced. Meanwhile `fat32_write_path_spec.spl`
(no `os.kernel.ipc.*`/scheduler/vmm/pmm import) passed 25/25 on the exact same
binary. Conclusion: this is a pre-existing seed/harness limitation specific to
specs that pull in the full scheduler/vmm/pmm/ipc/syscall dependency graph,
not something this change caused or can fix within its own scope. The new
`_handle_file_*` bodies were verified by careful code review and by testing
every `Fat32Filesystem` primitive they call in isolation instead (see Tests
above) — a materially weaker guarantee than a dynamic syscall-layer test would
have been, stated here rather than glossed over.

## Wall discovered this lane: a fd from `_handle_file_open` does not make `read`/`write` reach FAT32 — FIXED, see "Update 3" above

`_handle_file_open` allocates a real fd typed `FD_TYPE_FILE` (same type byte
`fd_io.spl` uses for the read/write routing table). But
`fd_io.posix_read`/`posix_write` route `FD_TYPE_FILE` through
`os.kernel.async_io_rw.sync_read`/`sync_write`, which call
`sosix_sync_read`/`sosix_sync_write` — a wholly separate subsystem from
`Fat32Filesystem`, unrelated to the mount published by this change. So: `open`
on a FAT32 path now does real disk I/O (path resolution, `open_at`/`create_at`,
fd allocation) and `stat`/`mkdir`/`readdir`/`unlink`/`rmdir` are fully real,
but a subsequent `read()`/`write()` syscall on the fd `open` returned will NOT
reach the FAT32 driver until `sosix_sync_read`/`sosix_sync_write` (or the
`FD_IO_ROUTE_FILE` dispatch ahead of them) is taught about the FAT32 backend.
This is a genuinely separate integration gap from the one this doc originally
tracked (that one was "no reachable Fat32Filesystem instance"; this one is
"two unrelated file-fd subsystems coexist under the same `FD_TYPE_FILE` tag").

**FIXED 2026-08-06 (later this session) — see "Update 3" above.** `open`
now allocates the fd typed `FD_TYPE_FAT32` (a dedicated type, not
`FD_TYPE_FILE`) and `read`/`write` route to `os.kernel.fs.fat32_fd_table`
instead of `posix_read`/`posix_write`. Real, single-call, sabotage-verified.
Whether it holds up across SEPARATE syscall calls is exactly Wall 2 in
Update 3 — unresolved, not silently assumed solved either.

## Wall discovered this lane: `boot_fs_mount_fat32_from_device` has no caller in the live boot sequence

`grep -rn boot_fs_mount_fat32_from_device src/os/` outside `boot_fs_mount.spl`
itself is empty — nothing in the real boot path calls it. This means the
`fat32_mount_publish` call added to it in this lane, while correct and now the
designated hook, is not YET reachable on real hardware/QEMU: on boot, nothing
publishes a mount, so `fat32_mount_ready()` stays false and all six wired
handlers correctly (honestly) return `-ENOSYS`, never a fake success. Wiring
something in the live boot sequence to call `boot_fs_mount_fat32_from_device`
(or `fat32_mount_publish` directly) with a real disk `BlockDevice` is the next
required step before these handlers do anything on the dev board. This gap
pre-dates this lane (`boot_fs_mount.spl`'s own module docstring already
describes itself as "the production boundary" without describing who crosses
it) and was not introduced or closed here — board-runnable rule requires
saying so explicitly rather than leaving it implicit.

## `rename` now real (UPDATE 2026-08-06, later same day)

The original entry below ("`rename` deliberately left ENOSYS") is preserved
for history but is SUPERSEDED: a follow-on lane the same day added
`Fat32Filesystem.rename_at(dev, old_path, new_path)` and wired
`_handle_file_rename` to it.

Resolution of the "IN PLACE rewrite" blocker described below: in-place
byte-rewrite of an LFN entry's name field(s) was considered and rejected —
an LFN name occupies a variable number of 32-byte slots plus a checksum byte
derived from the 8.3 short name, so a rename to a name needing a different
slot count cannot be a same-size in-place patch regardless. Instead
`rename_at` reuses the already-tested `_link_entry` (LFN chain + 8.3 alias +
checksum, the same primitive `create_at`/`mkdir_at` use) to link a new
directory entry — copying only `start_cluster`/`file_size`, never the file's
data — then calls `_mark_dirent_deleted` on the old entry, same as
`unlink_at`/`rmdir_at`.

**Honesty, not overclaiming atomicity:** this is NOT a single-sector atomic
operation, including for same-directory renames (no special-casing — same
LFN slot-count reasoning applies). A crash between "new entry linked" and
"old entry marked deleted" leaves BOTH names live pointing at the same data
— never neither, and file data is never touched or duplicated either way.
Cross-directory moves of a directory also patch the moved directory's own
`".."` entry to the new parent (one more dirent write, one more step in the
non-atomic window — documented, not hidden). Destination-exists returns
`EEXIST` — no atomic replace (POSIX `rename()`'s replace semantics are out of
scope; would require freeing the destination's cluster chain inside this
already non-atomic two-step, a strictly bigger data-loss window).

Tests: `test/01_unit/os/kernel/fs/fat32_rename_spec.spl`, 6/6 passing —
same-directory rename with content readback (proves DATA, not just the
dirent, survives), EEXIST-on-collision, cross-directory file move with
content readback, cross-directory directory move verifying the patched
`".."`, EINVAL on move-into-self, and an explicit
"old entry actually removed" check. Sabotage-verified in-session (reverted
before landing): skipping the old-entry-delete step failed 4/6 examples;
corrupting the copied `start_cluster` (0 instead of the real cluster) failed
3/6.

Landing note: `_handle_file_rename`'s wiring in `syscall_file.spl` landed
inside `f92f60da224` (an unrelated fd-read/write-wiring commit) via a shared
working tree — both lanes were editing the checkout concurrently and that
commit's `git add` swept up this lane's already-written handler code too.
`fat32.spl`'s `rename_at` primitive itself — the piece `f92f60da224` did NOT
carry, so `syscall_file.spl` briefly referenced a nonexistent method on
`origin/main` — followed immediately after as `cf12235211a`, restoring
compilability.

## `rename` deliberately left ENOSYS (ORIGINAL, SUPERSEDED — see above)

Unlike unlink/rmdir (mark-deleted — a single-byte dirent patch reusing
existing `_link_entry`/`resolve_path` machinery) or readdir (pure read
enumeration), a real rename must rewrite a directory entry's LFN + 8.3 slots
IN PLACE while preserving `start_cluster` and size. `Fat32Filesystem` has no
primitive for that — `_link_entry` only APPENDS new slots; nothing edits or
relocates an existing one. Fabricating rename as "create the new name, delete
the old" would be observably wrong the moment either half fails partway (a
caller could end up with both names or neither, where POSIX guarantees
atomicity). Left as `-ENOSYS` in `_handle_file_rename` rather than a fake or
partially-correct implementation.

## Original report (2026-08-06 AM), preserved below

## Summary

`src/os/kernel/ipc/syscall_file.spl` handles the path-based POSIX syscalls
(`open`, `stat`, `mkdir`, `readdir`, `unlink`, `rename`, `rmdir`). Before this
change, each of these built an `IpcMessage` and fired it at port 0.
`IpcMessage` carries no payload pointer, `send()` queues an empty payload and
returns 0 immediately, and no reply was ever awaited. The result: the path
bytes never left the kernel, the caller's `struct stat*` / dirent buffers were
never written, and the syscall still reported success (0). `open`'s return
value in particular happened to look like a valid fd because it returned the
send() result (0) — colliding with fd 0 (stdin) — rather than a newly
allocated descriptor.

## Fix landed here

The fake IPC sends are removed. Each handler now range/pointer-validates its
arguments (as before) and returns `-ENOSYS` (-38) instead of a fabricated 0.
`open` in particular can never return 0 on this path, so a caller can no
longer have its writes silently redirected to the console. This is a pure
honesty fix: no caller behaviour is being "improved," a previously-silent
failure is now a loud, correctly-signalled one.

`read`/`write`/`close`/`lseek` were already real: they route through
`os.kernel.fd_io.{posix_read, posix_write, posix_close, posix_lseek}`, which
talk to the FD table and the active POSIX fd backend (serial/pipe/socket/file
routes). They are unaffected by this change and unaffected by the open/stat/
mkdir/readdir/unlink/rename/rmdir gap below, EXCEPT that nothing can now
allocate a *file*-backed fd through this path (see "Known gaps").

## What actually exists today (verified, not assumed)

`os.kernel.fs.fat32.Fat32Filesystem` (`src/os/kernel/fs/fat32.spl`) is a real,
freestanding-safe FAT32 driver operating directly on a `BlockDevice`:
`mount`, `open`, `read`, `stat`, `resolve_path`, `open_at`, `stat_at`,
`allocate_cluster`, `append_cluster`, `_update_dirent`, `write`, `create_at`,
`mkdir_at`, `flush`, `close`. It does real cluster allocation, real
directory-entry writing (8.3 + LFN), and real nested-path resolution.

Evidence this is real, not a shim: `test/01_unit/os/kernel/fs/fat32_subdir_spec.spl`
(17 examples) and `test/01_unit/os/kernel/fs/fat32_write_path_spec.spl`
(25 examples), 42/42 passing. Sabotage-verified during this change: stubbing
`mkdir_at` to `return Ok(())` (skipping all real work) turned 18 of the 25
`fat32_write_path_spec.spl` examples red — including "creates a directory
whose . and .. entries resolve on re-read", "nests directories two deep",
"refuses to create a directory that already exists", "grows the directory by
a cluster when an entry chain does not fit". Restoring the real implementation
returned it to 25/25. The suite is not vacuous.

## Known gaps — why the syscall handlers still return ENOSYS

1. **No kernel-global mounted `Fat32Filesystem`.** Every
   `Fat32Filesystem(...)` construction site in the tree is inside
   `fat32.spl` itself (its `impl` block's static constructors and its own
   specs) — `grep -rn "Fat32Filesystem(" src/os/` proves it. No boot path
   ever constructs one and stores it as persistent state the way
   `g_cwd_table` does for cwd. `syscall_file.spl` therefore has a real
   `mkdir_at`/`stat`/`open_at`/`create_at` to call but no filesystem instance
   to call it on.
2. **The hosted VFS layer (`os.services.vfs`) is a dead end for this module.**
   `os.services.vfs.vfs_init` / `vfs_dispatch` do have real dispatch
   (`g_vfs_file_size`, `g_vfs_read_file_bytes`, and DriverInstance-level
   `write_file_bytes`/`delete_file`/`file_exists`), and `boot_fs.spl` (the
   *hosted* boot sequence, used to load `/sbin/init`) does call them. But
   `boot_fs_mount.spl`'s own header explicitly forbids importing
   `os.services.vfs.vfs_init` from the freestanding boundary, and
   `syscall_file.spl` lives in that freestanding boundary (it only imports
   `os.kernel.*`). Wiring `os.services.vfs` in here would cross an
   architectural line the codebase already draws on purpose.
3. **`posix_open` in `fd_io.spl` is a separate, already-dead path**, not an
   alternative fix. It builds a real IPC payload and sends it to a "VFS
   service" at port 1 (`VFS_OPEN`), then blocks on a reply. But
   `src/os/kernel/boot/init_services.spl:125` documents that this service is
   never spawned in production ("In a full system this would be
   `spawn_task(vfs_service_start)` ... the caller can invoke
   `vfs_service_start()` when ready to block"). Routing `_handle_file_open`
   through `posix_open` today would not fake success — it would hang the
   calling task forever waiting on a reply nobody sends. ENOSYS is the
   correct current answer, not a workaround.
4. **`readdir`, `unlink`, `rename`, `rmdir` have no primitive at any layer.**
   `Fat32Filesystem` does not implement them yet (`grep -n "fn.*unlink\|fn.*rmdir\|fn.*rename\|fn.*readdir" src/os/kernel/fs/fat32.spl` is empty).

## Required next step (for the next lane) — DONE 2026-08-06 (this lane), see "Update 2" above

~~Mount a `Fat32Filesystem` into freestanding kernel-global state during boot
(mirroring the `g_cwd_table` lazy-init pattern in `syscall_file.spl`), expose
an accessor, and have `_handle_file_stat` / `_handle_file_mkdir` /
`_handle_file_open` (via `open_at`/`create_at`) call it directly instead of
returning ENOSYS. Map the returned `FileHandle` to a POSIX fd through the
existing fd table (`os.kernel.fd_table`) so `read`/`write`/`close` keep
working unchanged. `readdir`/`unlink`/`rename`/`rmdir` need new
`Fat32Filesystem` methods before they can move off ENOSYS at all.~~ All of
this landed except `rename` (deliberately, see above) and the fd
read/write-after-open connection (a separate, newly-discovered gap, see
above) — the fd this lane's `open` allocates is real but `read`/`write` on it
still don't reach FAT32. **UPDATE (later this session, see "Update 3"): the
read/write connection is now also done.** The required next steps are now:
(1) wire something in the live boot sequence to actually call
`boot_fs_mount_fat32_from_device`/`fat32_mount_publish` (still open); (2) Wall
2 from "Update 3" is now CONFIRMED and root-caused, see "Update 4" — it is the
same pre-existing, already-closed, seed-interpreter-only `Option`-bind COW
defect (`interp_trait_slot_receiver_reboxed_per_call_mutation_loss_2026-07-07.md`),
not fixable within this repo's pure-Simple-first scope, and not currently
reachable on real hardware/QEMU since the only real `BlockDevice` implementer
is still a no-op stub; re-verify against a real block device once one exists,
or once native codegen can even compile a trait-dispatch-through-`Option.unwrap()`
call (a separate, deeper, pre-existing gap found while investigating Wall 2 —
see "Update 4").

## Related, separately-landed honesty fixes in this same change

- `src/os/libc/simpleos_posix_ext.c`: added real `pread`/`pwrite` (seek+io,
  with a stated non-atomicity caveat) and honest `fsync`/`fdatasync`
  returning `ENOSYS` rather than falsely claiming durability — traced end to
  end to two real gaps (FAT32 size-writeback and unreachable NVMe FLUSH).
- See also `doc/08_tracking/bug/simpleos_fs_stream_ops_lack_host_fallback_2026-08-06.md`
  for a distinct, already-filed bug about the FILE-stream layer
  (`fopen`/`fread`/`fwrite`) bypassing the host-fallback dispatch — different
  functions, different root cause, not fixed by this change.
