# Lane MMAP — writable shared mmap

Status: **partial (model implemented + fault path wired in owned code; end-to-end
libc surface still fails closed; QEMU gate outstanding)**

> **Lane MMAP2 continuation (2026-07-27/28).** Verified the MMAP tree intact,
> found and fixed a real use-after-free in the frame path, extended the spec to
> 9 blocks / 45 examples, and added the deliberate-red calibration the first
> increment lacked. See § 6 at the bottom for the full MMAP2 record. Everything
> above § 6 is MMAP's original text and remains accurate except the spec counts
> (7/35 -> 9/45) and the `vmm_shared_set_page_frame` API name, which MMAP2
> replaced with `vmm_shared_frame_ref` / `vmm_shared_frame_unref`.

## 1. Memory-model survey (done BEFORE design)

Files: `src/os/kernel/memory/**` (5,599 lines), types in
`src/os/kernel/types/vmspace_types.spl`.

What already exists:

| Capability | Where | State |
|---|---|---|
| Physical frame allocator (bitmap) | `pmm.spl` `pmm_alloc_page_raw` / `pmm_free_page_raw` | present |
| **Per-frame refcounts** `g_page_refcounts: [u16]` | `pmm.spl` `pmm_ref_page` / `pmm_unref_page` / `pmm_put_page` / `pmm_get_refcount` | **present — this is the shared-frame primitive, already used by COW** |
| Page-table map/unmap/replace in an AS | `vmm_address_space.spl` `vmm_map_page_in`, `vmm_unmap_page_in`, `vmm_replace_pte_in` | present |
| VMA model (`VmArea`, `ProcessVmSpace`) | `vmspace_types.spl`, `vmm_vma.spl` | present; `kind` ∈ {ANON=0, FILE=1, SHARED=2}, `flags` = READ/WRITE/EXEC/COW |
| Demand paging: anon (zero-fill) | `vmm_vma.spl` `vmm_handle_anon_fault` | present |
| Demand paging: file-backed | `vmm_vma.spl` `vmm_handle_file_fault` | present, but **private-copy only** |
| "Page cache" | `vmm_vma.spl` `_file_cache_handles` / `_file_cache_bytes`, filled by `vmm_cache_file_backing` from `syscall_spm.spl:304` via `posix_pread_exact_bytes` | whole-file byte image keyed by fd handle; **read-only, never written back** |
| COW fork | `vmm_vma.spl` `vmm_cow_clone_result`, `vmm_handle_cow_fault` | present |

Findings that decided the design:

1. **There IS a shared-frame primitive** — `pmm_ref_page`/`pmm_put_page`. Nothing
   was missing at the allocator level.
2. **`VMM_VMA_SHARED = 2` was declared and completely unused** (`vmm_core.spl:67`,
   imported by `vmm_vma.spl:12`, referenced nowhere else). It was a placeholder.
3. **The real gap is the page cache, not the frames.** `vmm_handle_file_fault`
   allocates a *fresh private frame per fault* and copies bytes out of
   `_file_cache_bytes`. Two mappings of the same fd therefore land on two
   *different* frames — so writes cannot propagate. There is no
   (handle, file-page) → frame identity map, and no write-back edge at all.
4. **No rights are recorded for a backing handle.** `VmArea.backing` is a bare
   `u64` fd number; the kernel cannot tell a read-only handle from a writable
   one, so it could not attenuate a shared writable mapping today.
5. **Fault dispatch is `anon`-then-`file`** (`interrupts/idt.spl:382-385`) — it
   never consults `kind`, it just tries handlers in order. That means a new
   shared kind can be reached *without editing idt.spl* by delegating from
   inside `vmm_handle_file_fault` (which this lane owns).
6. **libc cannot reach any of it.** `mmap()` in `simpleos_libc.c:185` calls
   `simpleos_syscall(10, addr, length, prot, 0, 0)` — it hard-codes
   `kind = 0 (ANON)` and `backing = 0`, and the trampoline only carries 5
   argument slots (`arg0..arg4`), so `backing_offset` (arg5) is unreachable.
   Priming the page cache also happens kernel-side in
   `ipc/syscall_spm.spl:302-304`, which this lane does not own.

## 2. Design

Object model (MDSOC-consistent, capability-attenuating, fail-closed):

- **Shared file object** — one per backing handle: `(handle, rights, file image
  bytes, page table)`. Registered explicitly by the layer that *has* the file
  (`vmm_shared_register_backing`). An unregistered handle can never be
  shared-mapped: `-EOPNOTSUPP`.
- **Shared page** — one row per `(object, file page index)`: page-cache bytes,
  optional materialized physical frame, **map refcount**, dirty bit. The bytes
  are the authority shared between address spaces; the frame is the hardware
  realisation of those bytes.
- **Region descriptor** — one row per live mapping: `(space_id, start, len,
  handle, offset, flags, private?)`. Shared regions point at the object's pages;
  private regions carry a snapshot copy taken at map time.
- **Rights attenuation (deny-wins)**: `vmm_shared_map` with `VMA_WRITE` requires
  `(object.rights & VMA_WRITE) != 0`, else `-EACCES`. A read-only handle can
  yield only a read-only shared mapping. Writing through a read-only region is
  `-EACCES` even if the object is writable.
- **Write-back policy — explicitly msync-required.** Stores land in the shared
  page cache immediately (all shared mappings of the object observe them at
  once). The *backing file image* is updated only on `vmm_shared_msync(handle)`
  or when a page's map refcount falls to zero. A `read()` of the file before
  msync legitimately returns the pre-write bytes. This is documented, not
  accidental.
- **Unmap / process exit**: unmap decrements each page's map refcount; on the
  last drop the page is written back into the file image, the frame (if
  materialized) is released through `pmm_put_page`, and the page becomes
  non-resident. Idempotent — a second unmap of the same region is a no-op.
- **Private (`MAP_PRIVATE`) file mapping** is modelled as snapshot-at-map, so it
  never observes later shared writes. POSIX leaves that visibility unspecified;
  snapshot is a conforming choice and is what the spec asserts.

## 3. Implemented vs deferred

Implemented (this lane's paths only):

- `src/os/kernel/memory/vmm_shared.spl` — the whole object/page/region model
  above, pure Simple, no MMIO, no new `extern fn`. Flat parallel module arrays
  (no nested-struct mutation → dodges the 2-hop interpreter write-loss landmine).
- `src/os/kernel/memory/vmm_core.spl` — added `VMM_VMA_SHARED_FILE: u32 = 3`.
- `src/os/kernel/memory/vmm_vma.spl` —
  - `vmm_mmap` refuses `kind = SHARED_FILE` unless the backing is registered and
    the requested rights are attenuated-legal, and only then adds the VMA;
  - `vmm_handle_file_fault` delegates `kind = SHARED_FILE` to the new
    `vmm_handle_shared_file_fault`, which materializes **one frame per
    (handle, file page)** and maps that same frame into every address space,
    taking a `pmm_ref_page` per mapping;
  - `vmm_munmap_result` flushes shared frames back into the page cache and drops
    the region before detaching PTEs.
- `src/os/kernel/memory/vmm.spl` — facade re-export.
- `test/01_unit/os/kernel/memory/vmm_shared_mmap_spec.spl` — 7 describe blocks,
  35 examples. **JIT: 35 passed, 0 failed. Interpreter
  (`SIMPLE_EXECUTION_MODE=interpreter`): 35 passed, 0 failed.** Per-block counts
  identical in both modes (5/4/6/5/5/7/3).

Two real compiler-behaviour landmines were hit and worked around here (both
found by the spec, both would have silently corrupted refcounts otherwise):

1. `[] as [u8]` is rejected — *"semantic: type mismatch: unsupported cast target
   type: Array { element: Simple(\"u8\"), size: None }"*. Note
   `vmm_vma.spl:_file_cache_lookup` still uses that form in a bare return
   position and compiles, so the rejection is position-sensitive. Worked around
   with a typed `var empty: [u8] = []` local.
2. **`arr[idx] = arr[idx] + 1` on a module-level array inside a `while` loop
   only lands on the FINAL iteration under the JIT** (scalar-spill-in-loop
   class). A two-page shared mapping ended up with page 0 at map count 0 and
   page 1 at 1 — i.e. the first page would have been written back and freed
   while still mapped. Fixed by moving the mutation behind a call boundary
   (`_shm_add_page_map` / `_shm_drop_page_map`). The same shape in the unmap
   loop was pre-emptively converted. Worth filing as a compiler bug in its own
   right: silent, and only visible with >1 loop iteration.

## 3a. Working-copy clobber during this lane (process note)

Mid-lane, a parallel session's sync reverted this lane's uncommitted edits to
`vmm_shared.spl`, `vmm_vma.spl`, `simpleos_libc.c`, `posix_profiles.md` and
`production_status.sdn` to earlier in-session versions, while leaving the spec
and `vmm_core.spl` alone — a mixed snapshot, exactly the failure mode in
`.claude/rules/vcs.md` § "Sync must never clobber". All edits were re-applied
idempotently and re-verified by content grep. Anyone landing this lane should
content-grep for `vmm_handle_shared_file_fault`, `_shm_add_page_map`, and the
`kernel model` matrix row before trusting the tree.

Deferred / NOT done (and why):

- **libc `mmap()` still returns `EOPNOTSUPP`** for writable `MAP_SHARED` and for
  `fd >= 0`. This is deliberate. The C surface cannot reach the new kernel path:
  it hard-codes `kind = ANON`/`backing = 0`, the syscall trampoline has no arg5
  for `backing_offset`, and the page cache is primed in
  `ipc/syscall_spm.spl` — none of which this lane owns. Relaxing the errno now
  would re-introduce exactly the dishonesty P5 removed (userspace would get a
  VMA the fault path cannot serve, i.e. a hard #PF). Only the *comment* was
  updated, to name the model and the exact remaining wiring.
- **Real on-disk persistence.** Write-back lands in the kernel's file image
  (`vmm_shared_file_bytes`). Pushing that image to the VFS needs a `pwrite` in
  `ipc/syscall_spm.spl` — not owned.
- **TLB shootdown across CPUs** for a shared writable frame. Single-CPU-correct
  today; multi-core needs an IPI shootdown on the write-back/unmap edge. Filed.

## 4. Remaining wiring (for the coordinator to route to the owning lanes)

1. `src/os/kernel/ipc/syscall_spm.spl` `_handle_sys_mmap`: on
   `kind == VMM_VMA_SHARED_FILE`, call `vmm_shared_register_backing(fd, bytes,
   rights_of_fd)` (rights from the fd's open mode — deny-wins) before
   `vmm_mmap`; on `sys_msync`, call `vmm_shared_msync` + VFS `pwrite`.
2. Syscall trampoline: a 6-argument form so `backing_offset` (arg5) is
   reachable, or an `mmap2`-style page-offset convention.
3. `src/os/libc/simpleos_libc.c`: only after (1) and (2) land, narrow the
   `EOPNOTSUPP` to the cases still unsupported (non-zero offset, `MAP_FIXED`
   overlap, non-file fds).
4. SQLite WAL (`src/os/port/sqlite/sqlite_vfs_contract.spl`, **not this lane**):
   `xShmMap` stays fail-closed until (1)-(3) land. Not unblocked yet.

## 5. Validation gate still required

The byte-level model is spec-proven in userspace. The **frame-level** path
(`vmm_handle_shared_file_fault`, one frame in two page tables, `pmm_ref_page`
per mapping, write-back on last unmap) touches real page tables and HHDM and is
**not** proven by any spec. Exact gate a future session must run:

```
bin/simple test test/01_unit/os/kernel/memory/vmm_shared_mmap_spec.spl
SIMPLE_EXECUTION_MODE=interpreter bin/simple test test/01_unit/os/kernel/memory/vmm_shared_mmap_spec.spl
# then, after the syscall wiring above lands, under real firmware (OVMF pflash,
# never -kernel / isa-debug-exit):
#   two user tasks map the same file MAP_SHARED|PROT_WRITE, task A stores,
#   task B loads the stored value, msync, host-side read of the file matches.
```

Until that QEMU run exists, the matrix row stays **model/partial**, not
"implemented".

# ============================================================================
# 6. Lane MMAP2 continuation (2026-07-27/28)
# ============================================================================

## 6.1 Tree verification first

The MMAP tree survived intact (content-grepped `vmm_handle_shared_file_fault`,
`_shm_add_page_map`, the `kernel model` matrix row — all present). Nothing was
restarted. An out-of-tree backup was kept in `/tmp/mmap2_backup/` throughout and
refreshed after each edit batch, per the clobber history in § 3a.

## 6.2 Defect found and fixed: shared-frame use-after-free

**The bug.** `_shp_frame` (the physical frame realising a shared page) was
recorded once by `vmm_shared_set_page_frame` and only ever cleared when the
page ROW was dropped, i.e. when the **map** count hit zero. But the frame's
physical refcount is driven by *faults*, not by maps:

- `vmm_shared_map` increments the map count at map time;
- `vmm_handle_shared_file_fault` takes the physical ref at fault time;
- `vmm_munmap_result` issues one `pmm_put_page` per **present PTE**.

A region can be mapped and never touched. So: space A maps and faults page 0
(frame F, physical rc = 1, map count 1); space B maps the same page but never
touches it (map count 2, no PTE, no physical ref). A unmaps — map count falls
to 1, so the row and `_shp_frame = F` survive, while the PTE loop issues the
last `pmm_put_page` and F goes back to the allocator. B then faults, reads
`vmm_shared_page_frame` -> F, calls `pmm_ref_page(F)` on a **freed** frame and
maps it into B's address space. That is a use-after-free that hands B whatever
the allocator has since put in F — a cross-process information leak, and
exactly the class of silent dishonesty this lane exists to remove.

**The fix** (`src/os/kernel/memory/vmm_shared.spl`,
`src/os/kernel/memory/vmm_vma.spl`): a second, separate count.

- New parallel array `_shp_frefs` — **frame residency**: how many address
  spaces hold a live PTE on the page's frame. Invariant: `_shp_frefs <=
  _shp_maps`, and `_shp_frefs` mirrors the physical refcount exactly.
- `vmm_shared_set_page_frame` is REPLACED (not kept alongside — no dead code)
  by `vmm_shared_frame_ref(handle, page, frame)`, called by **every** faulting
  space, not just the first. A page has one frame identity; supplying a
  different frame is `EINVAL`, a zero frame is `EINVAL`, an unregistered handle
  is `EOPNOTSUPP`, an un-interned page is `EFAULT` — all fail closed.
- `vmm_shared_frame_unref(handle, page)` drops one residency ref and, **on the
  last drop, clears the recorded frame identity** — in the same window in which
  `vmm_munmap_result` releases the final `pmm_put_page`. A later fault then
  re-materialises from the page cache, which is the authority for contents
  anyway. It saturates at zero, so a double unref cannot underflow.
- `vmm_shared_flush_frames` now checks `vmm_read_pte_in(...) & PTE_PRESENT`
  before flushing and unref'ing, so a mapped-but-unfaulted page in the unmapped
  range is left alone instead of retiring a frame another space still holds.
- The `if not mapped:` rollback in `vmm_handle_shared_file_fault` now gives back
  BOTH refs (residency then physical), in the same order the unmap path uses.

`vmm_shared_page_frame_refs` was added as the read-only observer the spec
asserts on.

## 6.3 Spec: 7 blocks/35 examples -> 9 blocks/45 examples

`test/01_unit/os/kernel/memory/vmm_shared_mmap_spec.spl` gained:

- **`vmm_shared: frame residency refcount (use-after-free guard)`** — 9
  examples: no frame/no residency on a fresh intern; identity + 1 ref on first
  fault; a second space joining counts 2; a *different* frame identity refused
  (`EINVAL`) with the original preserved; identity retained while another space
  holds it; identity cleared to 0 on the last drop; **the mapped-but-unfaulted
  case that was the actual bug** (map count 2, residency 1, unref -> identity
  gone); no underflow on repeated unref; zero-frame/unregistered-handle/
  un-interned-page all fail closed with their exact errnos.
- **`vmm_shared: deliberate-red calibration`** — 1 example asserting the four
  load-bearing invariants at absolute values, each annotated in-line with the
  counter-value that must turn it red.

FRAME_P/FRAME_Q were declared at module level, not describe level, to dodge the
describe-`val`-capture landmine rather than rely on a bare-identifier touch.

## 6.4 Verdicts (absolute, both engines)

| Run | Command | Result |
|---|---|---|
| Green, JIT | `bin/simple test test/01_unit/os/kernel/memory/vmm_shared_mmap_spec.spl` | **45 total, 45 passed, 0 failed** |
| Green, interpreter | same with `SIMPLE_EXECUTION_MODE=interpreter` | **45 total, 45 passed, 0 failed** |
| Deliberate red | `bin/simple test build/mmap_red/vmm_shared_mmap_red_spec.spl` | **45 total, 43 passed, 2 failed** |

Per-describe counts, identical on JIT and interpreter:
`5 / 4 / 6 / 5 / 5 / 7 / 3 / 9 / 1`.

**Deliberate-red evidence.** `build/mmap_red/vmm_shared_mmap_red_spec.spl` is a
copy of the spec with six assertions flipped to their documented counter-values
(the four calibration invariants, plus two residency assertions). It fails with
exactly two failing examples and the other seven blocks still green:

```
✗ clears the frame identity on the last residency drop
    expected 0 to equal 2
✗ holds the four load-bearing invariants at their exact values
    expected 163 to equal 90        # 0xA3 vs 0x5A — cross-space visibility
FAIL build/mmap_red/vmm_shared_mmap_red_spec.spl
```

This proves the green run is not vacuous: the assertions do discriminate. The
red copy lives under `build/` (outside `test/`) so it is never picked up by a
suite run.

## 6.5 What MMAP2 did NOT change, and why

- **`src/os/libc/simpleos_libc.c` is untouched.** All three blockers it names
  are still true (kind/backing hard-coded, no arg5 slot,
  `vmm_shared_register_backing` unwired in `syscall_spm.spl`). Narrowing the
  `EOPNOTSUPP` now would re-introduce P5's dishonesty. Writable `MAP_SHARED`
  and `fd >= 0` both still fail closed.
- **`src/os/kernel/ipc/**` is out of this lane's ownership**, so the syscall and
  VFS-pwrite wiring in § 4 remains for the owning lane. Unchanged.
- **SQLite WAL is still blocked** and the sqlite contract was not edited. The
  unblock condition is unchanged: § 4 items 1-3.
- **Multi-core TLB shootdown** on the write-back/unmap edge is still not
  implemented. Single-CPU-correct only.

## 6.6 Validation gate — STILL REQUIRED, unchanged in substance

The residency fix is spec-proven at the model level but the frame path it
guards still touches real page tables and the HHDM and has no hardware
evidence. The matrix row stays **model/partial**, never "implemented". Exact
gate a future session must run, in order:

```
bin/simple test test/01_unit/os/kernel/memory/vmm_shared_mmap_spec.spl
SIMPLE_EXECUTION_MODE=interpreter bin/simple test test/01_unit/os/kernel/memory/vmm_shared_mmap_spec.spl
# then, only after the § 4 syscall/VFS wiring lands, under REAL FIRMWARE
# (OVMF pflash — never QEMU -kernel, never isa-debug-exit):
#   1. two user tasks map the same file MAP_SHARED|PROT_WRITE;
#   2. task A stores, task B loads the stored value;
#   3. a THIRD task maps the same page and never touches it, then A and B
#      unmap, then the third task faults — it must NOT observe freed-frame
#      contents (this is the § 6.2 regression, and it is the one case a
#      single-task smoke test will miss);
#   4. msync, then a host-side read of the file matches.
```

Per `.claude/rules/board-runnable.md`, a QEMU-only pass is not the end state:
the same artifact must also boot and run this on the physical dev board.
