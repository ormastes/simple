# Seed test-run slowdown: child-process leak + per-spec preamble cost (perf ledger)

Date: 2026-09-19
Lane: suite-2026-09-18 (Windows, seed binary `bin/simple.exe`, built 2026-09-17)

## Question

README.md (`### Testing`) claims "4,067 tests in 17.4 seconds / average per test
4.3ms" (snapshot 2026-02-14). Does that still hold? And the suite felt "far
more slower than before" during this lane's verification runs.

## Verdict

1. **The README number is not comparable to today's runs.** It counts individual
   `it()` cases (4,067 of them), was measured with the pure-Simple self-hosted
   binary on an idle machine, and the suite has since grown by an order of
   magnitude. All current lane verification runs use the Rust **seed**
   interpreter (`bin/simple.exe`) because the pure-Simple binary is blocked by
   the ledgered HIR-tail memory wall (see
   `jit_co_compiled_definition_ambiguity_debt_2026-09-15.md` and the
   `check_worker_seed_interpreter_gap_2026-09-19.md` chain).

2. **The acute slowdown ("far more slower than before") was a child-process
   leak, now fixed.** Measured and remediated 2026-09-19:
   - 462 `simple.exe` processes alive on a 24-core host; 285 were hung
     grandchildren (`"./bin/simple" gen-lean verify`, `simple run
     build/test-artifacts/...`) spawned by specs that invoke the CLI as a child.
   - Root cause: the shard runner wrapped each spec in `timeout 240`, which on
     Windows kills only the direct child. Grandchildren blocked in the seed's
     child-process gap (see `posix_spawn_and_seed_process_debt_2026-09-19.md`)
     never exited and accumulated, saturating CPU/RAM and making every
     subsequent spec 5-15x slower. The leak compounded over hours of sharding.
   - Fix: `scripts/check/run-shard-suite.shs` v2 runs each spec as a background
     job and reaps the whole process tree with `taskkill //PID <pid> //T //F`
     after each spec (also on timeout). A one-time PowerShell sweep
     (`scripts/check/sweep-windows-test-leaks.ps1 -Kill`) removed 489 stuck
     processes; the host dropped from 462 to ~11 `simple.exe` processes.

3. **No per-spec regression found on an unsaturated machine.** Measurements
   (7 shards still running, mild contention):
   - `"$PURE" --version`: 129 ms (native seed startup).
   - `test/01_unit/lib/std/common/text_find_start_offset_spec.spl`: 11.8 s,
     twice in a row (11,799 ms / 11,821 ms) — within and below the documented
     15-25 s seed pre-main cost; no cross-run speedup.
   - `test/01_unit/compiler/30.types/simd_capabilities_extern_backing_spec.spl`:
     ~100 s — compiler-harness specs import the compiler test preamble, an
     order of magnitude more module surface than lib specs.
   - Passing a directory (no tests selected at all): 91 s — pure preamble cost.
   - Zero `[jit-fallback]` lines in these runs: the preamble JIT-compiles; the
     time is JIT compilation + interpretation of a large module closure,
     re-paid on every spec invocation.

## Structural perf finding (follow-up, not a regression)

There is **no effective persistent module cache in `simple test` mode**: the
seed binary contains a module cache (`module_cache.rs`, "Module cache hit",
`.simple_cache/`), but `.simple_cache/` stays empty across runs and repeated
identical spec invocations take identical time. Every one of the thousands of
spec invocations re-JITs the same std/lib/compiler preamble from scratch
(~12 s lib closure, ~90-100 s compiler-harness closure under the seed).

Options for the pure-Simple toolchain (do NOT patch the seed):
- Persist and reuse the module cache across `test` invocations (key on
  source-hash closure + compiler version), or
- Keep a warm test-runner daemon that JITs the preamble once and forks specs
  through it.

Either would collapse suite wall-time even under the seed, and becomes moot
for the preamble once the pure-Simple binary unblocks (it runs these same
specs in the sub-second-per-spec range the README records).

## Evidence artifacts

- `/tmp/shard2_*.log` — restart-of-shards runs with tree-kill runner.
- Before/after process counts: 462 -> 11 `simple.exe` (24-core host).
