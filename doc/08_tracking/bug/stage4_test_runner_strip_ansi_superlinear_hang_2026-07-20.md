# Stage-4 self-hosted `simple test` superlinear stall parsing large captured
# subprocess output (arch_check_spec.spl) — NOT caused by suffix-boundary /
# procfs-read / rt_array_copy / bool-inference fixes

**Date:** 2026-07-20
**Severity:** high (any spec whose daemon-fallback compile produces a large
captured subprocess output can stall `simple test` on the self-hosted binary
for minutes+; not a crash, not data-corrupting, but effectively a hang from
the caller's perspective)
**Status:** CLOSED (re-scoped) — 2026-07-20 follow-up lane: `strip_ansi` /
`parse_test_output` benchmarked and EXONERATED (empirically linear, not
quadratic); root cause re-attributed to the non-memoized daemon-fallback
relint/compile traversal this doc already flagged in "What would confirm the
mechanism" as a separate, lower-priority concern. See "2026-07-20 follow-up:
benchmark results" below. Tracked onward in
`doc/08_tracking/bug/stage4_test_runner_daemon_fallback_relint_nonmemoized_2026-07-20.md`.
No change was made to `strip_ansi` / `parse_test_output` — see follow-up
section for why.

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

## 2026-07-20 follow-up: benchmark results (root-fix lane)

A dedicated follow-up lane (own worktree, `/tmp/wt_stripansi` at
`b56adfac66d`) ran the microbenchmark this doc called for. Verdict: **the
"prime suspect" — `strip_ansi`'s per-character slicing being O(n²) — is
empirically FALSE.** `strip_ansi` and `parse_test_output` are linear. No
change was made to either function. The real bottleneck is child-side
compile/lint work, tracked separately in
`doc/08_tracking/bug/stage4_test_runner_daemon_fallback_relint_nonmemoized_2026-07-20.md`.

### Binary and backend used for every measurement below

All numbers are from `build/bootstrap/full/x86_64-unknown-linux-gnu/simple`
at commit `3835e717d16` (`/tmp/wt_deploy`, sha256 `c3236c0f...`) — the exact
"NEW" artifact this doc's own gdb backtraces were captured from — invoked via
`simple run <file>.spl` with `SIMPLE_EXECUTION_MODE=cranelift` explicitly
set and confirmed engaged (see below). This is a **self-hosted, compiled**
measurement, not the Rust seed and not a tree-walking interpreter:
- A 200,000,000-iteration integer loop ran in ~390ms (~2ns/iteration) under
  `run` — native-compiled speed, not interpreter speed.
- `SIMPLE_EXECUTION_MODE=interpret` on the same loop took 1271ms (3.3x
  slower) and `SIMPLE_EXECUTION_MODE=llvm` printed `[INFO] JIT compilation
  failed, falling back to interpreter: LLVM JIT not available: compile with
  feature 'llvm'` (1307ms, i.e. it silently fell back to the interpreter)
  — **this exact binary has no LLVM JIT capability at all.** Since this is
  the same artifact that exhibited the original 550s+ hang, cranelift *is*
  production for this artifact; there is no alternate LLVM code path this
  bug could have been hitting. `SIMPLE_EXECUTION_MODE=cranelift` gave 382ms,
  confirming cranelift engagement and ruling out the interpreter fallback
  for all measurements below (each was captured with the mode pinned and
  the `--backend=`/positional-flag forms found to be silently inert for
  `run` — do not rely on them; use the `SIMPLE_EXECUTION_MODE` env var).
- `bin/simple` (the Rust seed) was NOT used for any timing below — the seed
  never enters this self-hosted code path at all (§4 above), so it cannot
  validate or refute this finding either way.

Harness scripts referenced below were self-contained (no `use
std.test_runner...`) specifically because importing that package under
`run` on this binary triggers the SAME daemon-fallback relint this doc
describes for `arch_check_spec.spl` (confirmed: it ran past 900s without
even reaching the harness's own `main()`). `strip_ansi`/`parse_test_output`
were exercised either as verbatim inlined copies (Experiments A-C) or via
the real `use std.test_runner.{strip_ansi, parse_test_output}` import
(Experiment D, run against a real captured dump so the relint-on-import
cost was paid once, out of band, by capturing the dump from a separate
`run arch_check_spec.spl` invocation first).

### Experiment A — repeated `strip_ansi(fixed_line)`, isolating call-count effects

Same short line (~80 bytes, 3 SGR codes) called N times in one process;
per-checkpoint delta shown so a growing per-call cost (as would result from
a scan over a monotonically-growing global, e.g. the string registry
discussed below) would be visible even though total N grows:

| N (cumulative) | ms since prev checkpoint | calls since prev | µs/call |
|---:|---:|---:|---:|
| 10,000 | 425 | 10,000 | 42.5 |
| 50,000 | 1,698 | 40,000 | 42.5 |
| 100,000 | 2,361 | 50,000 | 47.2 |
| 200,000 | 4,332 | 100,000 | 43.3 |
| 424,554 | 10,664 | 224,554 | 47.5 |
| 800,000 | 17,556 | 375,446 | 46.8 |

Flat at ~43-48µs/call across an 80x range of N. No superlinear trend.

### Experiment B — realistic synthetic corpus, `strip_ansi` once per line

Mixed ANSI/plain lines (~60-110 bytes each), matching the doc's own "max
line 394 bytes, aggregate volume" characterization:

| n_lines | strip_ansi loop (ms) | µs/line |
|---:|---:|---:|
| 10,000 | 484 | 48.4 |
| 50,000 | 2,319 | 46.4 |
| 100,000 | 4,076 | 40.8 |
| 200,000 | 8,507 | 42.5 |
| 424,554 | 19,386 | 45.7 |
| 800,000 | 35,561 | 44.5 |

Linear. At the doc's own reported max volume (424,554 lines), total
`strip_ansi` cost is ~19.4s — not "minutes+".

### Experiment C — discriminating probe for the registry-scan hypothesis

Code reading found a real candidate mechanism: `rt_native_eq_inner` in
`src/runtime/simple_core/core_string.spl` calls `registered_string_ptr`,
which does a **linear scan over a global, monotonically-growing,
never-pruned array** (`string_registry_items`, appended to by every
`rt_string_new`/`alloc_string` call and never trimmed) to validate a tagged
value is a real string before comparing it. `llvm_lib_translate_expr.spl`
confirms `==` on arbitrary types lowers to `rt_native_eq`. This looked like
exactly the "aggregate volume, not single line length" shape the hang
exhibits, so it was tested directly: pre-inflate the registry by N
*freshly, dynamically constructed* (not literal — avoids compile-time
interning at a fixed low index) distinct strings, then time a FIXED 4,000
comparison workload:

| pre-allocated strings in registry | fixed 4,000-comparison loop (ms) |
|---:|---:|
| 0 | 1 |
| 100,000 | 1 |
| 500,000 | 1 |
| 1,500,000 | 1 |

Flat at 1ms regardless of registry size. **`registered_string_ptr`'s scan is
not reachable from `text == text` in `strip_ansi`'s code shape** (the
compiler must be routing `ch == "["` / `c == ";"` etc. through the O(1)
`rt_string_eq` fast path, not the generic `rt_native_eq`/registry path).
This refutes the leading hypothesis this doc raised in "What would confirm
the mechanism precisely" — `registered_string_ptr` is a real, load-bearing
O(n) scan in the runtime (worth hardening defensively; see note below), but
it is not what's making this spec's `test` invocation slow.

### Experiment D — the decisive measurement: real `parse_test_output` on a real captured dump

To rule out "the synthetic corpus doesn't match the real pathological
input" and to directly re-test the exact call chain the doc's 3/3 gdb
backtraces landed in (`parse_test_output` → `strip_ansi`, including the
`.split("\n")`, `.trim()`, `.starts_with()`, `.contains()`, `.index_of()`
calls the earlier experiments didn't individually exercise), a real dump
was captured by running `SIMPLE_EXECUTION_MODE=cranelift simple run
test/01_unit/app/arch_check_spec.spl` on this same binary. That run was
still producing lint output after a 900s timeout (killed, not completed —
see next section). The first 149,478 real, complete (newline-terminated)
lines of that capture (~4.85MB; the file is 11MB total but the tail past
that point is a SIGKILL-truncated partial line, correctly excluded) were
then fed to a verbatim-inlined copy of `parse_test_output` (including
`strip_ansi`, `extract_number_before`, `extract_number_after_colon`) at
increasing prefix sizes:

| n_lines (real dump prefix) | prefix bytes | parse_test_output (ms) | µs/line |
|---:|---:|---:|---:|
| 20,000 | 665,318 | 675 | 33.8 |
| 50,000 | 1,684,721 | 1,385 | 27.7 |
| 100,000 | 3,374,391 | 2,729 | 27.3 |
| 149,478 | 4,996,193 | 4,512 | 30.2 |

Clean linear on real data: ~28-34µs/line, no upward trend. Extrapolated to
the doc's own reported max volume (424,554 lines), this is **~13-20s**, not
550s+. If `parse_test_output` were the 550s driver, this 149K-line slice
alone would have taken on the order of 190s; it took 4.5s.

### Attribution: where the 550s actually goes

`run test/01_unit/app/arch_check_spec.spl` (same binary, same mode) —
which reproduces the daemon-fallback relint + spec execution but calls
`parse_test_output` **zero times** (parsing only happens in the *parent*
process under `test`, never under a bare `run`) — did not finish within a
900s timeout. Combined with Experiment D showing the parent's own parse
cost is ~13-20s at full volume, the attribution is: **the ~205-distinct-file,
up-to-659-repeats-each non-memoized relint traversal (already flagged in
this doc's "Evidence §2" as "separately noteworthy... worth its own
investigation") is the actual driver of the 550s+ hang, not
`strip_ansi`/`parse_test_output`.** This also reconciles the seed-vs-NEW gap
this doc reports (seed 32s vs NEW 550s+ on the same spec): the gap is NEW's
own self-hosted lint/compile pipeline being far slower than the seed's
native Rust implementation for this repeated-traversal workload, not a
parsing regression. Filed as its own bug:
`doc/08_tracking/bug/stage4_test_runner_daemon_fallback_relint_nonmemoized_2026-07-20.md`.

### Reconciling the 3/3 gdb backtraces

This doc's own gdb evidence (§1) is not contradicted, just re-read: this
doc explicitly hedged the parser was "most likely O(n) with a large
constant — or genuinely O(n²)" and never actually measured it. The 3
backtrace samples (at 25s/60s/100s wall-clock offsets) landing inside
`parse_test_output`/`strip_ansi` are consistent with catching a real
(linear, ~13-20s-at-full-volume) parse pass — the samples were explicitly
taken "past the fork/compile phase," which is biased toward whatever runs
after the (much longer) relint phase, not a uniform sample of the whole
550s+. A linear parse that runs for ~13-20s is an entirely plausible thing
for 3 manually-timed samples to land in, especially since it's the last
thing to run before the process would otherwise complete.

### Correctness evidence (mission requirement, since a fix was on the table until this benchmark)

- Regression spec added: `test/01_unit/app/test_runner_strip_ansi_spec.spl`
  (12 examples: plain text, simple SGR, multiple SGR in one line, `?`
  parameter byte, multi-parameter SGR, OSC-sequence passthrough documented
  as current out-of-scope behavior, truncated-escape-at-EOF, bare trailing
  ESC, empty string, escapes-only string, non-ASCII/multi-byte UTF-8
  passthrough, adjacent-sequence-then-text). Validated via `simple run
  test/01_unit/app/test_runner_strip_ansi_spec.spl` (`test <spec>` was
  found to fail "no parseable pass/fail summary" on this binary even for a
  trivial one-assertion spec with no strip_ansi involvement at all — an
  environment/binary limitation of this specific artifact, not a
  `parse_test_output` correctness finding, and not this spec's fault; see
  next paragraph). Result: **12 examples, 0 failures.**
- Differential test vs. the old implementation (mission step 4b) and
  unchanged-pass/fail-accounting sweep (step 4c): **N/A — no algorithmic
  change was made to `strip_ansi` or `parse_test_output`.** The benchmark
  above found them already linear; there is nothing to diff against or
  re-verify accounting for.
- Environment note for future lanes: `build/bootstrap/full/x86_64-unknown-
  linux-gnu/simple` at `3835e717d16` (a) resolves `use std.X` imports
  against `/tmp/wt_deploy`'s own tree regardless of invoking CWD, so it
  cannot see edits made in a different worktree, and (b) fails `simple
  test <any spec>` with "no parseable pass/fail summary in test output;
  refusing synthetic pass" even for a trivial always-passing spec with no
  output at all. Both were confirmed independent of this investigation's
  content. Use `simple run <spec>.spl` (which works and prints the normal
  `N examples, 0 failures` BDD summary) for correctness checks against this
  specific binary; do not treat a `test` rejection on this artifact as a
  parser defect.

### Deferred hardening note (not a bug filed — record only)

`registered_string_ptr` in `src/runtime/simple_core/core_string.spl` is a
linear scan over a never-pruned, monotonically-growing global array, used
by `rt_native_eq_inner` (the generic/dynamic equality path). It happened
not to be reachable from `strip_ansi`'s specific code shape (the compiler
routes static `text == text` through the O(1) `rt_string_eq` instead), so
no bug is filed against it here — but it remains a latent O(n) validation
cost on every *generic* equality comparison for the lifetime of a process,
and is worth a defensive O(1) hash-set rewrite if a future profile shows it
hot on a path that does reach it (e.g. `Any`-typed or dict-key equality).
Not investigated further; out of scope for this lane.
