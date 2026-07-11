# BUG: freestanding module-compiled code misbehaves where identical entry-closure code works (ring-3 handoff aborts 134)

**Status:** open — sole blocker for in-guest clang via the general streaming loader
**Severity:** high (silent behavioral divergence by compilation unit; blocks Track 3d)
**Component:** native-build freestanding codegen — module compilation path vs entry-closure path
**Found:** 2026-07-11 (clang file-launch lane, isolated by exhaustive A/B)

## Symptom

The map/stack/heap/enter-user pipeline for a streamed 124,602,568-byte static
clang ELF aborts exit=134 (after libc startup: mmap+getpid succeed, abort
before the first stderr lseek) when the sequence executes in the loader
MODULE (`src/os/kernel/loader/x86_64_fs_exec_ring3.spl`), but the SAME code
exits 0 — and even compiles hello.c — when it runs in the entry-closure file
(`fs_elf_exec_smoke_entry.spl`, re-verified green on current source).

## Isolation (everything below verified IDENTICAL between the two paths)

- Kernel binary, image bytes (.data spot-checked against host copy)
- SysV frame (including the smoke's own C cc1 argv builder, argc=13)
- TaskContext readback (rflags=0x3002 / cs=43 / ss=35)
- Pre-AS setup: nvme_bar_high, pmm bounds, 64 KB header
- A VERBATIM copy of the smoke's mapper, called from the module — still aborts

Same defect family as the documented freestanding module-val/boxing landmines
(module-level state through ANY/boxing channels behaves differently by
compilation unit).

## Repro / next unblock

Binary-search the split point: move pipeline stages one at a time from the
entry-closure into the module until the abort appears (or temporarily host the
handoff in entry-closure-compiled code). Ground truth via `rt_dump_phys16`
(baremetal_stubs.c) — `rt_mmio_read_u8` readbacks falsely return 0 (see
`x64_freestanding_mmio_read_u8_address_dependent_zero.md`).

Logs: `build/os/elfexec/clang_stream_run.log` (abort), `smoke_cur_run.log`
(green baseline). Worktree fixes that got clang this far are listed in
`doc/03_plan/os/in_guest_clang_streaming_loader_roadmap.md`.
