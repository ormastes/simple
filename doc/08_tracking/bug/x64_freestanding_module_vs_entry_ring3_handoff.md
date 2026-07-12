# BUG: [RESOLVED 2026-07-12] clang runs in-guest on SimpleOS — abort-134 was a zero-sized user heap from a `.to_u64()` codegen bug

**Status:** RESOLVED (2026-07-12). clang_static now runs in ring-3 on SimpleOS to
`clang version 20.0.0git ...` + clean exit(0). Both prior premises (module-vs-entry,
seed regression) were disproven; the true cause was a zero-sized user heap.
**Severity:** was high (blocked in-guest clang)
**Component:** SimpleOS ring-3 user-heap setup (loader) + a `.to_u64()` codegen bug

## Resolution

The abort-134 was clang's libc calling `abort()` because its FIRST `mmap` in ring-3
returned ENOMEM. The user heap had zero capacity: in
`src/os/kernel/loader/x86_64_fs_exec_ring3.spl` the map_heap block computed page size
via `PAGE.to_u64()` (where `PAGE` is a function-local `val PAGE: i64 = 4096`), and that
conversion evaluates to **0** under freestanding native-build. So (a) the size passed to
`rt_user_heap_init` was `16384 * 0 = 0` (heap end == base), and (b) the page-mapping loop
mapped all 16384 pages to `HEAP_VA + hp*0` = the same VA (only 4 KB really backed).

Fix: use a fresh `val HEAP_PAGE_SZ: u64 = 4096` in both the mapping loop and the size,
instead of `PAGE.to_u64()`. Serial then shows the heap 64 MiB backed, clang's mmap
succeeds, clang stats its resource dir and prints `clang version 20.0.0git
(https://github.com/ormastes/llvm-project.git 92fa402...)` then `[syscall] exit status=0`.

The underlying `.to_u64()`-returns-0 codegen bug is filed separately
(`freestanding_i64_to_u64_returns_zero.md`) and worked around at this call site.

Regression-verified after the loader change: `ssh_clang_hello_ring3.shs` DEMO PASSES
(hello + rc=42), `ssh_multi_cmd.shs` MULTI-COMMAND SSH WORKS (both commands resume).

The syscall dispatcher was NOT at fault — it correctly returned ENOMEM for an exhausted
heap. No missing syscall; the earlier "static-libc/CRT/syscall frontier" conclusion was
wrong.

---

## Investigation history (premises disproven en route)

**Found:** 2026-07-11; two successive premises disproven 2026-07-12 (opus main loop)

## Two disproven premises

1. **"module-vs-entry compilation defect."** DISPROVEN: the all-inline entry-closure smoke,
   rebuilt from current source, aborts 134 identically to the loader-module path; frame bytes
   dumped from both paths in the same run are byte-identical and correct.
2. **"seed codegen regression (Jul 11 12:27 seed)."** DISPROVEN: a release seed rebuilt CLEAN
   from origin (commit f61639f0c12, built 2026-07-12 03:18) still produces clang exit 134,
   while the SAME clean seed builds the hello FS-exec demo GREEN (ssh_clang_hello_ring3.shs:
   "hello from clang on simpleos" / "[user] exit rc=42" / DEMO PASSES). So the seed is
   exonerated for clang.

## The invalid comparison that produced the "seed regression" theory

The bisection's "green binary exits 0, red aborts 134, only the seed changed" compared TWO
DIFFERENT PAYLOADS: the green anchor runs the **hello FSEXEC.ELF smoke** (small static ELF →
rc=42), the red run streams **clang_static** (124,602,568 bytes). clang and hello were never
the same binary, so "only the seed changed between them" was never true. There is no evidence
clang ever ran green — it is unimplemented frontier, not a regression.

## Abort characterization (stable across every configuration)

clang streams fully (125 MB, PT_LOADs mapped, 64 MiB user heap mapped), enters CPL3 with a
correct SysV frame (argc readback=2), performs mmap + getpid, then aborts during libc init —
the second getpid is raise()'s kill(getpid, SIGABRT); exit status = 134 (128 + SIGABRT 6).
Insensitive to: frame bytes, argv (green's exact 13-arg cc1 set), RAM size (4 GB), pmm bound
(0x18000000), linker script. The hello smoke on the identical kernel/AS path exits cleanly, so
the ring-3 machinery is sound — the failure is specific to clang's static-libc init sequence.

## Next step (characterize, don't bisect)

Run clang with FULL syscall serial logging (SIMPLE_OS_LOG_MODE on, not off) and dump every
syscall number + args clang's libc issues before the SIGABRT. The abort is almost certainly
clang's libc asserting on an unsupported/incorrect syscall return (candidates: brk/mmap flags,
arch_prctl/TLS setup, ioctl(TCGETS) on stderr, rt_sigprocmask, set_tid_address, futex). Fix =
implement/repair the offending syscall(s) in the bare user-exec dispatcher
(baremetal_stubs.c). This is CRT/syscall-completeness work, not a compiler or seed fix.

## Related (surfaced during investigation, still valid)

- `x64_freestanding_layout_sensitive_dup_displaced_stores.md` — real dumped bytes showed
  duplicated slot0/1 stores + all later stores displaced +16 in one build, vanishing when
  unrelated code was added to the entry file (separate latent codegen fragility).
- `simpleos_pmm_bound_breaks_128mb_base_kernels.md` — RESOLVED (bound raised to 0x18000000).

## Note on the stale seed (fixed as a side effect)

The gates' release seed (src/compiler_rust/target/release/simple) was stale at 2026-07-11
12:27, built from a since-diverged lineage. It was rebuilt clean from origin f61639f0c12 on
2026-07-12; this fixed the unrelated process_queue.spl "function too large" phantom (see
memory) but did NOT change the clang abort. Always verify seed provenance before trusting a
kernel-gate result.
