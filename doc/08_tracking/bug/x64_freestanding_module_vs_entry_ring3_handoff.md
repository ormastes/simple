# BUG: [PREMISE DISPROVEN → relocated] clang ring-3 abort 134 is a seed codegen regression (Jul 11 ~12:27 seed), not module-vs-entry

**Status:** open — root cause relocated 2026-07-12; next step = seed bisect
**Severity:** high (blocks in-guest clang; any freestanding build with the post-12:27 seed aborts)
**Component:** Rust seed native-build codegen (regression window: seed rebuilt 2026-07-11 12:27)
**Found:** 2026-07-11; premise disproven by single-variable bisection 2026-07-12

## Original (false) premise

The streamed clang_static pipeline was believed to abort 134 when run from the
loader MODULE but exit 0 from the entry-closure file. Exhaustive single-variable
elimination disproved this.

## What the bisection actually established (2026-07-12)

Eliminated one variable per run (full table: BISECT_NOTES.md in the lane
worktree, run logs step0/buildA..J in the session scratchpad):

- RuntimeString header fix (u64 len): still 134
- Frame bytes: entry-built vs module-built frames dumped in the SAME run are
  byte-identical and correct: still 134
- Green's exact 13-arg cc1 argv: 134 · 4 GB RAM: 134 · kernel_end 0x18000000:
  134 · linker.ld variants: 134
- DECISIVE: the "proven green" all-inline entry-closure smoke, rebuilt from
  current source, ALSO aborts 134 — identical to the module path.
- The pre-existing green BINARY (built Jul 11 08:53) still exits 0 today
  against the same image/QEMU.
- Zero repo commits between the green build (08:53) and the first red build
  (13:26); the only changed input is the Rust seed, rebuilt 12:27 (that day's
  seed inline-len STR1-vs-byte-tag change is the prime suspect).

## Abort characterization

clang reaches CPL3, performs mmap+getpid, then aborts during libc init
(second getpid is raise()'s kill(getpid, SIGABRT); exit 0x86) — insensitive
to frame/argv/layout/memory size.

## Next step (single-variable proof, then fix)

Rebuild the seed at the pre-12:27 Rust commit; rebuild the same kernel source;
if it exits 0, bisect the seed change. Note: foreign-worktree seeds from
08:28/10:31 produce kernel-faulting builds — a clean seed rebuild at the
pinned commit is required for the proof.

## Related (surfaced during bisection)

- `x64_freestanding_layout_sensitive_dup_displaced_stores.md` — real dumped
  bytes showed duplicated slot0/1 stores + all later stores displaced +16 in
  one build, vanishing when unrelated code was added to the entry file.
- `simpleos_pmm_bound_breaks_128mb_base_kernels.md` — committed
  kernel_end=0x14000000 makes the green baseline unbuildable from origin/main.
