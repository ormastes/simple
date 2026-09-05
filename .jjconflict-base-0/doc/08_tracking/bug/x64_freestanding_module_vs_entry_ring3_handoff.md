# BUG: [BOTH premises DISPROVEN] clang aborts 134 during static-libc init in ring-3 — genuine unimplemented frontier, not a regression

**Status:** open — NOT a seed regression, NOT module-vs-entry; the abort is clang's own
static libc calling abort()/SIGABRT during process init in ring-3.
**Severity:** high (sole remaining blocker for in-guest clang; the hello FS-exec path is green)
**Component:** SimpleOS ring-3 process runtime — freestanding static-libc / CRT / syscall completeness
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
