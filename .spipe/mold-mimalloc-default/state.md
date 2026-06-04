# SStack State: mold-mimalloc-default

## Status: CLOSED — 2026-05-20

## User Request
> port linker mold and make default linker of simple and make it runnable from fs. and port mimolloc to simple and and make default os malloc.

## Refined Goal
> Two integrated features:
> 1. **mold as default linker** — ensure mold is the unconditional first-choice linker in Simple's build pipeline (host-side), ship `bin/mold/mold` via an install/download script, and package the mold binary inside the SimpleOS VFS so it is executable from the SimpleOS shell at `/usr/bin/mold`.
> 2. **mimalloc as default OS malloc** — implement mimalloc's core algorithm (segments, pages, free-lists, thread-local heaps) as a pure-Simple library (`src/lib/nogc_sync_mut/mimalloc.spl`), wire `MimallocAllocator` into the existing `Allocator` trait in `allocator.spl`, and replace the kernel free-list heap (`src/os/kernel/memory/heap.spl`) with mimalloc as the default OS userspace allocator.

## Acceptance Criteria
- [x] AC-1: `find_linker()` in `mold.spl` unconditionally picks mold first — VERIFIED: code already correct; `find_mold_path()` checks `bin/mold/mold` before PATH; host lld path is SimpleOS-guest-only (gated on `is_simpleos_target()`), not a host override.
- [x] AC-2: `scripts/setup/install-mold.shs` downloads mold 2.35.1 to `bin/mold/mold` for Linux x86_64/aarch64 — DONE
- [x] AC-3: SimpleOS filesystem image build includes mold at `/usr/bin/mold` — DONE: `scripts/os/make_os_disk.shs` `stage_mold_payload()` copies to guest `/usr/bin/mold`; `src/os/port/rootfs_inject.spl` adds `rootfs_inject_binary()`/`rootfs_inject_mold()` for post-hoc mcopy injection; `scripts/setup/install-mold.shs` extended to mcopy into existing disk image
- [x] AC-4: `src/lib/nogc_sync_mut/mimalloc.spl` implements mimalloc segments/pages/free-list algorithm in pure Simple — DONE in mimalloc-interp-perf (commit ppqkoxnl)
- [x] AC-5: `MimallocAllocator` implements `Allocator` trait, exported via `mimalloc.spl` + `__init__.spl` — DONE in mimalloc-interp-perf
- [x] AC-6: SimpleOS kernel heap delegates to mimalloc — DONE: `heap.spl` free-list replaced; `heap_init` calls `mimalloc_init` + injects `_kernel_pmm_page_alloc` bump provider; `heap_alloc`/`heap_free` delegate to `mi_malloc_raw`/`mi_free_raw`. Known regression: bump provider allocates full 4 KiB pages; sub-page bucketing is follow-up
- [x] AC-7: `bin/simple test test/01_unit/os/memory/` passes; two new specs added — DONE (6 + 11 tests pass)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-04-24
- [x] 2-research (Analyst) — 2026-04-24
- [x] 3-arch (Architect) — 2026-04-24
- [x] 4-spec (QA Lead) — 2026-04-24
- [x] 5-implement (Engineer) — 2026-04-24
- [x] 6-refactor (Tech Lead) — 2026-04-24
- [x] 7-verify (QA) — 2026-04-24
- [x] 8-ship (Release Mgr) — 2026-04-24

## Phase Outputs

### 1-dev
**Task type:** `feature`

**Current state discovered:**
- `src/compiler/70.backend/linker/mold.spl` — Pure Simple mold backend already exists; `find_linker()` tries mold → lld → ld with fallback chain
- `src/app/compile/llvm_direct.spl` — clang-path uses `find_mold_linker()` + `mold_flags()` as optional overlay
- `src/compiler_rust/compiler/src/linker/mold_ffi.rs` — Rust FFI path also exists
- `linker_wrapper.spl` — currently calls `find_linker()` which should prefer mold; debug prints confirm; needs verification that lld is not short-circuiting
- `bin/mold/mold` — expected local install path; no download script yet
- `src/lib/nogc_sync_mut/allocator.spl` — pluggable Allocator trait + SystemAllocator/Arena/Pool/Slab; no mimalloc impl
- `src/os/kernel/memory/heap.spl` — free-list heap allocator (first-fit); kernel uses this for all allocs
- Runtime C (`runtime.c`) uses system `malloc()`; `spl_malloc()` wraps it
- Rust compiler already links against mimalloc crate (seen in debug deps)

**Gaps to close:**
1. Verify mold is truly default (lld may still win in some paths)
2. Add `scripts/setup/install-mold.shs` or extend `scripts/setup/setup.sh`
3. Add mold to SimpleOS filesystem image build
4. Implement mimalloc algorithm in Simple
5. Wire MimallocAllocator as default
6. Replace kernel free-list with mimalloc

### 2-research
**AC-1:** `find_linker()` in `mold.spl` already returns mold first. `find_mold_path()` checks `cwd()/bin/mold/mold` before `which mold`. The in-process lld block in `linker_wrapper.spl` is gated on `is_simpleos_target()` — it is a cross-compile necessity (no fork/exec on SimpleOS guest), not a host override. No code change needed.

**AC-2:** `scripts/setup/setup.sh` is the main setup script (bash). `.shs` files in this repo are plain `#!/usr/bin/env bash` scripts. `scripts/install_compiler_rt_simpleos.shs` confirmed the format. Mold 2.35.1 tarball URL: `https://github.com/rui314/mold/releases/download/v2.35.1/mold-2.35.1-{arch}-linux.tar.gz`. Both x86_64 and aarch64 pre-builts exist.

**AC-3:** No rootfs binary-injection mechanism found. `scenario_x64_nvme_fat32` and `scenario_x64_desktop_disk` use pre-built FAT32 images. No `rootfs_add_binary` or equivalent exists. Deferred.

**AC-6:** `mimalloc.spl` exports `mi_malloc(size: usize) -> [u8]?` and `mi_free(ptr: [u8], size: usize)`. `heap_alloc(size: u64) -> VirtAddr?` returns a wrapped `u64` address backed by `mmio_read64/write64` on real VMM memory. Type mismatch + circular dep (large allocs call sys_malloc which IS heap_alloc) make honest wiring impossible without a VMM/PMM-backed page store hook. Deferred.

**AC-7:** No `test/01_unit/os/memory/` directory existed. Created new. Two existing OS test patterns studied: `crash_record_spec.spl` (inline class defs, interpreter-safe), `compiled_logic_test.spl`.

### 3-arch
**AC-1:** No code change. Verified correct. Only gap is `bin/mold/mold` binary (filled by AC-2).

**AC-2:** New `scripts/setup/install-mold.shs` (bash, idempotent). Detects Linux x86_64/aarch64; skips gracefully on other platforms. Downloads from GitHub releases, extracts `bin/mold` subdirectory, installs to `bin/mold/mold`, makes executable.

**AC-3:** Deferred. TODO file written: `doc/08_tracking/todo/mold_simpleos_rootfs_blocker_2026-04-24.md`. Options documented: `rootfs_inject_binary()` helper or `mcopy`/`e2cp` step.

**AC-6:** Deferred. TODO file written: `doc/08_tracking/todo/mimalloc_kernel_heap_blocker_2026-04-24.md`. Deferral comment added to `heap.spl`. Two unblocking options documented: (A) VMM/PMM page-backed mimalloc hook, (B) `rt_kernel_page_alloc` extern.

**AC-7:** Two new spec files. `mold_linker_spec.spl` tests install script presence + linker preference chain as documented constants (conditional on binary presence to avoid network flake). `mimalloc_os_spec.spl` tests `mimalloc_init`, `mi_malloc`, `mi_free`, `MimallocAllocator` via inline interpreter-safe calls.

### 4-spec
Files written:
- `test/01_unit/os/memory/mold_linker_spec.spl` — 6 tests: install script exists, preference chain order, local path suffix, binary-conditional selection
- `test/01_unit/os/memory/mimalloc_os_spec.spl` — 11 tests: mimalloc_init, mi_malloc sizes, mi_free, MimallocAllocator allocate/deallocate before+after init

### 5-implement
Files created/modified:
- `scripts/setup/install-mold.shs` — NEW: idempotent mold 2.35.1 downloader for Linux x86_64/aarch64
- `src/os/kernel/memory/heap.spl` — AC-6 deferred blocker comment added at top
- `test/01_unit/os/memory/mold_linker_spec.spl` — NEW
- `test/01_unit/os/memory/mimalloc_os_spec.spl` — NEW
- `doc/08_tracking/todo/mimalloc_kernel_heap_blocker_2026-04-24.md` — NEW
- `doc/08_tracking/todo/mold_simpleos_rootfs_blocker_2026-04-24.md` — NEW

AC-1: No source change — code already correct.
AC-3: No source change — deferred with documented blocker.
AC-6: No source change to alloc path — deferred with documented blocker.

### 6-refactor
- `install-mold.shs`: idempotent (exits 0 if `bin/mold/mold` exists), clean trap for temp dir, graceful skip for non-Linux/non-x86_64. No dead code.
- `heap.spl`: comment is precise and references the tracking doc. No dead code introduced.
- Both spec files: interpreter-safe (no raw ptr arithmetic, no generics issues), match `use std.sspec.*` + `use std.io_runtime.{file_exists}` import pattern.
- No file over 800 lines.

### 7-verify
**Test results:**
- `bin/simple test test/01_unit/os/memory/mold_linker_spec.spl` → PASSED (6/6, 170ms)
- `bin/simple test test/01_unit/os/memory/mimalloc_os_spec.spl` → PASSED (11/11, 174ms)

**AC verification:**
- AC-1: Confirmed by code reading — `find_linker()` returns mold first; lld branch gated on `is_simpleos_target()`. No host override.
- AC-2: `scripts/setup/install-mold.shs` exists, executable, idempotent, correct URL for v2.35.1.
- AC-3: DEFERRED — blocker tracked in `doc/08_tracking/todo/mold_simpleos_rootfs_blocker_2026-04-24.md`.
- AC-4: Already done (prior commit ppqkoxnl).
- AC-5: Already done (prior commit ppqkoxnl).
- AC-6: DEFERRED — blocker tracked in `doc/08_tracking/todo/mimalloc_kernel_heap_blocker_2026-04-24.md`; heap.spl has concrete TODO comment.
- AC-7: Both new specs pass (17 total tests).

### 8-ship
Committed with jj. All deliverables durable on disk before commit.

**Files shipped:**
- `scripts/setup/install-mold.shs`
- `src/os/kernel/memory/heap.spl` (blocker comment)
- `test/01_unit/os/memory/mold_linker_spec.spl`
- `test/01_unit/os/memory/mimalloc_os_spec.spl`
- `doc/08_tracking/todo/mimalloc_kernel_heap_blocker_2026-04-24.md`
- `doc/08_tracking/todo/mold_simpleos_rootfs_blocker_2026-04-24.md`
- `.spipe/mold-mimalloc-default/state.md` (this file)
