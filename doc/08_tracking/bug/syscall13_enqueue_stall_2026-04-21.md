# Syscall 13 "Enqueue Stall" Root Cause (2026-04-21)

## Summary

The symptom tracked in
`doc/08_tracking/todo/simpleos_syscall13_direct_handoff_2026-04-20.md`
— "scheduler enqueue pending" between `create_user_task: caps registered`
and the first `_enqueue_ready` body — is **not** a scheduler enqueue bug.

It is a pathological per-byte allocation loop in
`src/os/kernel/loader/segment_mapper.spl` that runs between
`[syscall13] build_user_process_image ok` and the first scheduler marker.
QEMU eventually times out (or exhausts the heap) before `create_user_task`
can be entered, which made the stall *look* like it happened at the scheduler
boundary.

## Evidence

Serial log: `build/os/simpleos_desktop_disk_current_serial.log` (1.2 MB,
30 154 lines), from an earlier diagnostic run where the
`src/os/kernel/ipc/syscall.spl:1246` `return -12` gate was removed.

- Line 84: `[syscall13] build_user_process_image ok`
- Line 85 onward: ~30 000 lines of

  ```
  [heap] alloc off_after=0x...
  [heap] alloc sz=0x40 off_before=0x...
  [heap] alloc off_after=0x...
  [heap] alloc sz=0x30 off_before=0x...
  ```

  strictly alternating `sz=0x40` / `sz=0x30` (64-byte / 48-byte pair).

- The heap offset climbs from `0xc000010` to `0xc0d3290` — roughly **13 MB**
  of allocator churn — before the log truncates at QEMU timeout.
- No `[scheduler] create_user_task: …` marker is reached. No PANIC, FAULT,
  EXCEPTION, `cr2=`, `cr3=`, or `heap exhausted` marker is emitted.

## Root Cause

`src/os/kernel/loader/segment_mapper.spl` copies user-program bytes from the
kernel-side buffer into the user-page HHDM mapping **one byte at a time**,
in two places:

1. `_copy_segment_page` (`segment_mapper.spl:82-99`) — the PT_LOAD
   byte-copy loop used from `map_segment` (`:131-170`).
2. `_copy_stack_page` (`:101-121`) — the initial-stack-frame byte-copy loop
   used from `map_stack` (`:172-207`).

Both loops do:

```simple
while cur < copy_end:
    val seg_off = cur - seg_va
    val page_off = cur - page_va
    val b = if seg_off < file_size: _byte_at(src, seg_off) else: 0 as u8
    _write_u8(page_phys + page_off, b)
    cur = cur + 1
```

Where `_byte_at(src, off)` resolves to
`rt_bytes_u8_at(src, off.to_i64()).to_u8()`.

Observed `0x40` / `0x30` allocation pair per iteration matches the shape of
one boxed `i64` + one small wrapper struct. For a ~24 KB Browser Demo image
that lands on 6 page copies, the loop issues roughly `6 × 4096 = 24 576`
iterations and ~120 000 small allocations, each going through the Simple
allocator before the stack loop even starts. The stack copy is
`frame_length × 1-byte` more of the same, plus whatever overhead comes from
`vmm_write_byte_through_hhdm` going through the phys→virt conversion per
byte.

The generic-syscall code path at `src/os/kernel/ipc/syscall.spl:1174` that
calls `sched.create_user_task(...)` directly without the gate has the same
structural bug — it has just never been live because the desktop lane goes
through `dispatch_spawn_binary_direct` (`interrupt.spl:253`) whose gate
(`syscall.spl:1246`) returns `-12` before `create_user_task` is even
reached.

## Falsified Hypotheses

The original plan listed four candidate shapes; the log falsifies all of
them and replaces them with "bulk-copy primitive missing":

- **Shape A (mirror copy / scheduler by-value):** falsified. `Scheduler` is
  declared `class Scheduler:` at `scheduler.spl:341`, so it's a reference
  type; `sched.create_user_task(...)` mutations persist across the call
  boundary.
- **Shape B (CPU index out of range in `_enqueue_ready`):** falsified.
  Execution never reaches `_enqueue_ready` — it never reaches any
  `[scheduler] create_user_task: …` marker either.
- **Shape C (allocator reentry inside `_enqueue_ready`):** right direction,
  wrong site. The allocator IS the cause, but the hot loop is in
  `segment_mapper.spl`, not in `ReadyQueue.enqueue` /
  `CpuRunQueue.enqueue`.
- **Shape D (logging suppression):** falsified. Serial output IS flowing —
  30 k lines of it, the lines are just all allocator traces.

## Fix Shape (for Phase 2/3)

Replace the per-byte loops with a bulk byte-copy primitive. Two concrete
steps:

1. **Add `vmm_copy_to_user(phys: u64, src: [u8], src_off: u64, len: u64)`
   in `src/os/kernel/memory/vmm.spl`**. Implement using `rt_memcpy` which
   is already declared `extern fn rt_memcpy(dest: i64, src: i64, len: i64)`
   and used by `src/os/drivers/virtio/virtio_blk.spl:65`. Translate `phys`
   to an HHDM-mapped virtual address via the same `_phys_to_virt` that
   `vmm_write_byte_through_hhdm` uses (`vmm.spl:915-918`). For the source
   byte pointer, use `rt_bytes_from_raw`'s inverse — extract the `SplArray*`
   data pointer, or add a small `extern fn rt_bytes_u8_data_ptr(arr: [u8])
   -> i64` if none exists. Zero-fill the BSS tail with `rt_memset` (already
   defined alongside `rt_memcpy`).

2. **Rewrite `_copy_segment_page` and `_copy_stack_page` in
   `src/os/kernel/loader/segment_mapper.spl`** to call that helper once per
   page instead of once per byte. After the change, `map_segment` /
   `map_stack` emit exactly one `vmm_copy_to_user` per page, not 4096.

With that in place, `_map_user_process_image` returns cleanly,
`create_user_task` is actually entered, and the scheduler path that was
(mistakenly) assumed to stall can be exercised for the first time.

## Follow-up Diagnostics If The Real Scheduler Stall Appears

If, after the bulk-copy fix, the next QEMU run shows
`[scheduler] create_user_task: caps registered` followed by a fresh silent
stall (not present in today's log because we never reached that code), the
original Phase-1 instrumentation plan — markers inside `_enqueue_ready`
and `_sync_trap_runtime_state` — still applies as step two. But do not
add those markers until the bulk-copy fix is in; the allocator storm will
drown any new markers regardless.

## Forbidden Log Markers After the Fix

Once the bulk copy lands, the desktop disk lane must not emit any of:

- the `[heap] alloc sz=0x40 off_before=...` / `sz=0x30 off_before=...`
  alternating pair more than ~10 times between
  `build_user_process_image ok` and `[scheduler] _enqueue_ready`.
- `heap exhausted`
- QEMU timeout during app launch

If they reappear, the fix missed another per-byte loop; check
`_copy_stack_page`, `_write_u8`, and the `rt_bytes_u8_at` call sites in
`src/os/kernel/loader/elf64.spl`, `elf_loader.spl`, `process_image.spl`,
and `smf.spl` — they all share the same `_byte_at` pattern and may all
need the bulk-copy treatment for hot paths.

## References

- `src/os/kernel/loader/segment_mapper.spl` (hot loops at :82 and :101)
- `src/os/kernel/memory/vmm.spl:915` (`vmm_write_byte_through_hhdm`)
- `src/os/drivers/virtio/virtio_blk.spl:65,298,576` (existing `rt_memcpy`
  usage as a template)
- `build/os/simpleos_desktop_disk_current_serial.log` (raw evidence)
- `build/os/simpleos_desktop_direct_serial.log` (current post-gate log —
  confirms the gate is the only thing preventing the allocator storm
  today)

## Verification Status (2026-04-21)

The bulk-copy fix landed in `src/os/kernel/memory/vmm.spl` and
`src/os/kernel/loader/segment_mapper.spl`. The x86_64 desktop E2E kernel
builds cleanly with the change (`bin/simple native-build` produces a
working ELF32).

**Live QEMU verification is blocked by a separate pre-existing
regression.** A fresh `jj @`-clean build of `desktop_e2e_entry.spl` with
**all Phase-2 changes reverted** still emits ~8 kernel-mode `[fault] ***
EXCEPTION FRAME ***` entries immediately after `[desktop-e2e] mouse
ready` — between the PS/2 mouse bring-up and `CompositorEngine2D.new`.
The committed log `build/os/simpleos_desktop_direct_serial.log` (from
2026-04-20 22:10, before the AP trampoline commit `5a6482d3` and the
`bootstrap memory/apic topology` commit `aee87bd9`) shows a clean boot to
`TEST PASSED`, so the regression was introduced between that log and the
current working-copy state.

Impact on this bug:

- The Phase-2 fix is still correct — it addresses a real per-byte
  allocation storm in `segment_mapper.spl` that would absolutely fire
  the moment the `syscall 13` direct-handoff gate is lifted.
- But the fix cannot be QEMU-verified end-to-end until the
  post-`mouse ready` kernel fault on the x86_64 desktop disk lane is
  resolved. That is an independent bug and needs its own diagnostic pass
  (likely around `CompositorEngine2D.new`, `engine2d_display`, or the
  framebuffer/ACPI glue altered by recent topology/APIC work).
- Therefore: land the Phase-2 fix on its own, and file the desktop-lane
  fault as a follow-up (separate bug doc) rather than block Phase 2
  behind it.

Retaining the `-12` gate in `src/os/kernel/ipc/syscall.spl:1246` keeps
the resident-manifest fallback live, so unblocking Phase 2 does not
regress the current `TEST PASSED` evidence — the bulk copy only runs
when the gate is lifted, which is deferred to Phase 3 (x86_64 ring-3
return path) together with the desktop-lane fault triage.
