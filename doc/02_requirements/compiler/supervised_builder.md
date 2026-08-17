# Feature request: a supervising builder that survives worker death

- **Filed:** 2026-08-17
- **Status:** REQUESTED
- **Domain:** compiler / driver
- **Severity:** P1 — this is currently the dominant cost of every bootstrap defect

## The ask

Simple needs a real **builder** that owns compilation as supervised work in
**separate processes**, so that a unit of work which *dies* — SIGSEGV, SIGABRT,
OOM kill, external SIGTERM, or an infinite loop hit by a timeout — costs that one
unit and not the entire build. It must serve both entry points:

- **bootstrap** (stage 2/3/4, `bootstrap_main.spl` / `main.spl`), and
- **normal / ad-hoc** builds (`simple native-build`, `simple run`, `simple test`).

One builder, two front ends — not a bootstrap-only special case.

## Why: measured cost, today

Three failures observed in a single day, each of which this design removes:

1. **Fail-fast across files.** `driver_source_pipeline_parsing.spl` returned `Err`
   on the first bad file and abandoned the other 618;
   `driver_aot_native_output.spl` has **24** immediate `return
   CompileResult.CodegenError(...)` sites. Every defect therefore cost one full
   ~20-minute run to find. (Collect-all for *recoverable* errors has since landed
   in the parse path — but see 2.)
2. **A death is not an `Err`.** A segfault or OOM kill does not unwind, and this
   language has no try/catch by design (`Result<T,E>` + `?`). No amount of
   error-accumulation inside one process survives the process dying. Collect-all
   and crash-survival are **different features**; only the first exists.
3. **One external signal discarded a 26-minute build.** Stage 3 ended with
   `exit 143` (SIGTERM) at 26 minutes with 43 files left to parse. Sender still
   unidentified — the script's own `run_timeout` wrappers were ruled out, and
   `kill-simple-monitor.service` does not match its own thresholds on the measured
   numbers. **Nothing in the build recorded which unit was in flight when it
   died**, because progress reported only every 64 files. Details:
   `doc/08_tracking/bug/stage3_parse_stalls_at_tail_43_files_2026-08-17.md`.

Corollary already proven: a 547-second stall on one file was indistinguishable
from normal work for 9 minutes. Supervision makes cost per unit observable for
free, which on this host matters doubly because attach-based profiling is blocked
(`ptrace_scope=1`, `perf_event_paranoid=4`).

## Requirements

### R1 — Unit isolation
Each unit of work (one module: parse, lower, codegen) runs in a child process.
A child's death must not terminate the parent or any sibling.

### R2 — Classified outcomes, never merged
The supervisor reads each child's wait status directly (never through a pipe —
`$?` through a pipeline yields the pipeline's last status, which has already
produced false greens in this repo) and classifies:

| outcome | detection |
|---|---|
| `OK` | exit 0 and the declared artifact exists on disk |
| `ERROR` | clean exit, non-zero, diagnostics captured |
| `CRASHED` | killed by signal — 139 SIGSEGV, 134 SIGABRT, 137 SIGKILL/OOM |
| `TERMINATED` | 143 SIGTERM — **external**, i.e. UNVERIFIED, not failed |
| `TIMEOUT` | exceeded the per-unit budget |
| `NOT_RUN` | never started (build ended first) |

`TERMINATED` and `TIMEOUT` must NOT be reported as failures: per
`.claude/rules/testing.md`, `rc=143`/`144` with no result line means
**unverified**. Conflating them is how a contended host manufactures phantom
compiler bugs.

### R3 — The build reaches the end of the source list
Every remaining unit is attempted after any single unit's death. The final report
names every unit in every category, with counts. A unit that was never attempted
is `NOT_RUN` and is stated as such — silent absence is forbidden.

### R4 — Fail closed at the boundary, not early
Reporting continues to the end; the **link** then fails closed if any unit is not
`OK`. Explicitly forbidden: fabricating a stub or empty object for a crashed
module to make the link succeed. This repo already carries a defect of exactly
that shape — `linker/native_binary/stubs.rs:209-221` fabricates zero-returning
stubs, which masked missing symbols.

### R5 — Attribution of deaths
The supervisor logs, per unit: unit id, source path, signal or exit code, wall
time, peak RSS. This is what was missing when stage 3 was SIGTERMed. It also
answers "which file is slow" without a profiler.

### R6 — Resume
A build re-run must skip units already `OK` (existing object cache) and retry
only non-`OK` units. Note the current cache defeats this: the pure-Simple
driver's `cache_scope_root` hashes the **entire loaded source closure**, so
editing one file drops reuse to 0 for all modules (measured: 3/3 reused
unchanged, 0/3 after a one-line edit). Per-unit resume needs the interface-digest
work that already exists but is uncalled — `interface_digest_of` in
`action_key.spl:197-204` has **zero callers**.

### R7 — Bounded concurrency, honest about the host
Worker count must respect existing limits (codegen already runs `--threads 16`;
`scripts/resource/test-slot.shs` caps test concurrency at 12). No unbounded
fan-out. A supervisor that starves the box is a regression, not a feature — 58
processes queued against 6 slots produced 2 verdicts out of 33 runs today.

### R8 — One implementation, two front ends
Bootstrap and ad-hoc share the supervisor. A bootstrap-only path would drift, and
the bootstrap is precisely where the failures are most expensive.

## Where it goes

`ParallelBuilder` (`src/compiler/80.driver/driver_build/parallel.spl:241`,
`ParallelBuildConfig` with `num_threads` / `parallel_threshold` / `deterministic`
/ `verbose`) is the natural extension point — it is already the fan-out for
uncached modules in `driver_aot_native_output.spl`. What it lacks is process
isolation and outcome classification: today a worker's death is the parent's
death.

Note the seed's `native_project` pipeline already has genuine per-module hardened
cache keys and prints `[native-incremental] N reused / M rebuilt`, but it is only
reachable via `SIMPLE_NATIVE_BUILD_RUST=1` or a cross-target build — so it is not
a drop-in, and routing normal builds through it would violate the
pure-Simple-default policy.

## Acceptance

A fixture of **six** modules — one parse error, one that segfaults the compiler,
one that OOMs, one that infinite-loops into a timeout, and two clean — must, in
**ONE** run:

1. emit objects for both clean modules,
2. report all four poisoned modules in their correct categories, by path,
3. exit non-zero,
4. never claim six compiled, and never fabricate an artifact.

Plus a **negative control**: with the change reverted, that fixture must behave
worse. A control that fails to fail means the test is broken, not the code.

## Related

- `doc/08_tracking/bug/stage3_parse_stalls_at_tail_43_files_2026-08-17.md`
- `doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md` — superlinear
  per-file cost; R5 makes it locatable without a profiler.
- `doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md`
  — the test-side twin of R2: a run that never ran must not read as a pass.
- `b4872f73454` — build progress now reaches stdout (stage logs were 0 bytes for
  entire runs).
- `4d1aca2d799` — parse now reports per file, so a stalled unit names itself.
- `doc/01_research/compiler/incremental_build/lib_only_build_feasibility_2026-08-09.md`
  — why there is no target/dependency model today (relevant to R6).
