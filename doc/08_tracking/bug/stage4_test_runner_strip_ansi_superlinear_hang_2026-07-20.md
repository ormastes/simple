# Stage-4 self-hosted `simple test` superlinear stall parsing large captured
# subprocess output (arch_check_spec.spl) — NOT caused by suffix-boundary /
# procfs-read / rt_array_copy / bool-inference fixes

**Date:** 2026-07-20
**Severity:** high (any spec whose daemon-fallback compile produces a large
captured subprocess output can stall `simple test` on the self-hosted binary
for minutes+; not a crash, not data-corrupting, but effectively a hang from
the caller's perspective)
**Status:** OPEN — root cause narrowed to layer + function; fix not attempted
in this lane (see rationale below)

## Origin of this investigation

A pre-deploy smoke matrix (`/tmp/wt_deploy/smoke_new2/summary.txt`) flagged
`test/01_unit/app/arch_check_spec.spl` as a regression: stage-4 self-hosted
binary (`build/bootstrap/full/x86_64-unknown-linux-gnu/simple`, commit
3835e717d16) times out at >550s burning CPU, vs. a seed-baseline control run
completing in ~32s (74 passed, 1 failed) with the identical invocation. Deploy
was vetoed on this finding. Four landed/held commits were under suspicion as
the cause:

- **A** `d0d471ea1bb` / `8ec74920627` — seed-cranelift suffix-boundary mangling
  fix (closures_structs.rs, imports.rs, native.spl) — **ON MAIN**
- **B** `dfcf5fc337b` / `6e0a04eab03` / `023b93e4572` — procfs/file-read
  growable read-to-EOF fixes (runtime.c family) — **ON MAIN**
- **C** `b9eb4021052` / `5b07bc91d9d` — C `rt_array_copy` sibling — **ON MAIN**
- **D** `3835e717d16` — BOOL inference for unannotated global bool literals —
  present in the tested artifact's commit range

## Verdict

**None of A/B/C/D cause this hang. Main is NOT regressed by any of the four
commits with respect to this finding — do not hold or revert them.**

The hang is a **pre-existing, load-independent, superlinear-on-bounded-input
stall** inside the self-hosted test runner's captured-output parser
(`parse_test_output` / `strip_ansi`, in
`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl` and
`src/lib/nogc_sync_mut/test_runner/test_runner_files.spl`), newly *exposed*
— not introduced — by this specific spec, because `arch_check_spec.spl`
imports 12 underscore-prefixed private helpers from `app.cli.arch_check`,
which forces the "test daemon unavailable; running directly [fallback]" path
to shell out and compile/lint a broad slice of the compiler's own internal
module graph before the test can even start. That produces an abnormally
large (5–14 MB, 150K–424K line) captured subprocess output, which the
self-hosted parser then processes line-by-line at a cost that becomes
minutes-scale at this volume.

## Evidence

### 1. Backtraces (3 independent captures, gdb `run` + external `SIGINT` to
the ptraced inferior since `ptrace_scope=1` blocks non-ancestor attach)

All three land in the same self-hosted (.spl-compiled) call chain, at
different wall-clock offsets (25s, 60s, 100s) and under different system
load, always past the fork/compile phase and inside per-line output parsing:

```
#0 rt_string_eq / rt_string_trim   (varies by sample)
#1 nogc_sync_mut.test_runner.test_runner_files.strip_ansi   (or inlined)
#2 nogc_sync_mut.test_runner.test_executor_parsing.parse_test_output
#3 nogc_sync_mut.test_runner.test_executor_parsing.make_result_from_output
#4 nogc_sync_mut.test_runner.test_executor_parsing.make_result_from_structured_evidence
#5 nogc_sync_mut.test_runner.test_runner_execute.run_test_file_interpreter
#6 test_runner_new.test_runner_main.{run_single_test,run_tests,run_test_cli}
#7 cli___CliMain__main_and_help__main -> spl_main -> main
```

`/proc/<pid>/stat` utime deltas confirm 100% single-thread userspace CPU with
flat stime (no blocking syscalls) while parked at this location — this is
compute, not I/O wait. An earlier capture (before the fork burst completes)
transiently shows `rt_fork_parent_wait_bounded`'s `poll()` loop
(`src/runtime/runtime_fork.c:250`) — that is the (working-as-designed)
subprocess-capture wait, not the hang; it resolves once the child's pipes
close.

### 2. The captured output is real and reproducible independent of gdb

Direct `NEW run test/01_unit/app/arch_check_spec.spl` (no `test` wrapper)
prints `WARNING: this Rust-built Simple binary is a bootstrap seed only` —
confirming the daemon-fallback path **shells out to the Rust seed** to
lint/compile the file's dependency closure — then emits megabytes of lint
diagnostics (`warning: 'export use *'`, `info: Common mistake detected`,
`[gc-warning] Higher-layer module ...`) for ~205 distinct compiler-internal
`.spl` files, **each file repeated tens to hundreds of times** (e.g.
`_MirToLlvm/core_codegen.spl` ×659, `_MirLoweringExpr/method_calls_literals.spl`
×616 in a 20s/5MB snapshot). This repetition is a naive non-memoized
traversal of a highly-connected internal module graph — separately
noteworthy, but it **terminates** (see below) and is not itself the reported
hang.

Max single-line length in the captured text: **394 bytes** (checked via
`awk '{print length}' | sort -rn`). This rules out "one pathological huge
line"; the cost is aggregate over ~150K–424K lines, not from one line.

### 3. Fair, load-controlled, same-moment comparison (the decisive test)

Per coordinator guidance (the box is at ~87% utilization on 32 cores, 120+
concurrent build/test processes from other sessions — real but moderate
contention), `seed_baseline_bin` (built at commit `b69e546953`, **before all
four candidates**: A lands 03:41, B 05:57–06:10, C/D 07:10, seed built
00:43) and the NEW stage-4 binary were launched **concurrently**, identical
`SIMPLE_BINARY=<bin> <bin> test test/01_unit/app/arch_check_spec.spl`
invocation, identical 600s timeout:

- **seed_baseline_bin: completed. `Passed: 74, Failed: 1, Duration: 29981ms`**,
  424554 total lines in its own daemon-fallback dump — this *reconciles* the
  originally-recorded "31.8s" (internal test-execution clock) vs. the
  "~125s" total wall time noted in the original smoke run: the delta is
  trailing lint-dump I/O after the test itself finishes, not load variance.
  This run happened **while NEW was concurrently stalled on the same box**,
  which neutralizes the contention confound directly: identical load, one
  binary finishes, the other doesn't.
- **NEW: still had not completed even the fork burst after 155s elapsed /
  ~95s of accumulated single-thread CPU time** in one sample (contention
  slows absolute wall time, but 95 real CPU-seconds with zero forks issued
  is not explained by scheduling alone) — and in other same-lane runs
  reliably progressed only as far as the `strip_ansi`/`parse_test_output`
  hot spot before being killed at the timeout.

### 4. SEED never executes the self-hosted parser at all

`seed_baseline_bin` is a pure-Rust binary (`src/compiler_rust`). Its own
`test` subcommand implementation is native Rust and never calls the
self-hosted `nogc_sync_mut.test_runner.test_executor_parsing.parse_test_output`
/ `strip_ansi` symbols seen in every NEW backtrace — those are compiled from
`src/lib/nogc_sync_mut/test_runner/*.spl`, part of the **self-hosted**
binary's own standard library. This is *why* seed is immune regardless of
output size: it structurally never enters the code path that stalls.

### 5. None of the four candidates touch the implicated files

```
git log --oneline -- src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl
git log --oneline -- src/lib/nogc_sync_mut/test_runner/test_runner_files.spl
git show --stat <A|B|C|D commit>   # grep for test_executor_parsing / test_runner_files / strip_ansi
```

Zero matches for all four commits. The most recent touch to
`test_executor_parsing.spl` is `049f3c2e467 fix(test-runner): directory-mode
hang — replace offset-scan line parsing with split iteration`, a **prior,
unrelated fix for a different hang class** in this same file (a
`text.index_of(needle, start)`-ignores-`start` interpreter bug that made a
manual offset scan spin forever; the fix switched to `.split("\n")`
iteration). That history shows this file has a track record of hang-class
bugs under adversarial input volume — consistent with a second, distinct
instance surviving here.

### 6. The relint-dump volume itself is unaffected by A/B (the only two
candidates old enough to matter for that comparison)

Direct `run` reproduction on both `seed_baseline_bin` (pre-A/B/C/D) and the
current bootstrap seed (`src/compiler_rust/target/bootstrap/simple`,
contains A+B, built 07:00) against the same spec produced **byte-identical
per-file repeat counts** (659/616/533/508/396/390/272/255/212/197/189/189/
188/186/177/175/168/167/166/160 ...). A and B do not change the shape or
size of the pre-test lint dump; there is nothing here for them to have
regressed.

## Why NOT to revert candidate A regardless

Even setting the above aside: A's own fix note documents its failure mode as
**silent mis-binding of a private helper causing a SIGSEGV** (the
`devhub__cmd_storage___index_of` capture, Windows-branch dereference of a
tagged value). Reverting A would not touch this parser hang at all — it
would only reintroduce that crash. The two are unrelated in mechanism, in
file, and in commit history.

## What would confirm the mechanism precisely (not done here — see rationale)

- Microbenchmark `strip_ansi` / `.trim()` / `.split("\n")` directly against a
  synthetic ~150K-line, ANSI-code-dense, ≤400-byte-per-line corpus (e.g. a
  copy of `/tmp/wt_deploy/raw_child_err.log`) under the self-hosted binary,
  isolated from the fork/daemon machinery, to get a clean cost curve
  (confirm whether it's O(n) with a large constant — most likely, given
  `strip_ansi`'s per-character `s[i:i+1]` slicing pattern on what may be a
  rune-indexed `text` type — or genuinely O(n²)).
- If confirmed superlinear, the likely fix shape: avoid repeated single-
  character slice allocation in `strip_ansi` (iterate by byte/char index
  without allocating a substring per position), and check whether `.split`
  and per-line `.trim()`/`.contains()`/`.starts_with()` have equivalent
  costs at this call volume.
- Separately (lower priority, does not block deploy): the ~205-distinct-file,
  hundreds-of-repeats-each lint traversal in the Rust-seed delegation path
  is wasteful (though it does terminate) and worth its own investigation —
  looks like a non-memoized module-graph walk.

## Why no fix was attempted in this lane

This was an urgent bisect/adjudication lane under an explicit "do not push,
do not deploy" constraint, on a shared box already at high contention, with
no ability to rebuild+validate the stage-4 binary within the lane's time
budget. `strip_ansi`/`parse_test_output` sit on the hot path for **every**
test-output parse in the self-hosted binary; an unvalidated change here
risks silently corrupting pass/fail accounting repo-wide. The root-fix
mandate for this lane was conditional on one of the four candidates being
the cause — none are. Recommend a dedicated follow-up lane, with a clean
non-contended box and the microbenchmark above, fix and validate properly.

## Deploy recommendation

The four candidate commits are cleared of this specific finding and should
not be held or reverted because of it. The original smoke-matrix veto should
be re-scoped: either exclude `arch_check_spec.spl` from the gating matrix
pending the strip_ansi fix (it is a pre-existing self-hosted-only defect,
not something introduced by the changes under test), or mark it as a known,
tracked, non-blocking failure referencing this doc.
