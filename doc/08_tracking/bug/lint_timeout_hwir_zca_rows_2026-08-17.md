## Re-verified 2026-08-17 - STILL OPEN, WORSE than filed

Re-ran `nice -n 19 timeout 900 sh scripts/check/lint-cached.shs
src/compiler/50.mir/hwir/zca_rows.spl`. It exceeded **900s** (not just the 600s
in the original filing) and produced **no verdict line**; the log froze at 382
lines after the module-load `[gc-warning]` block and never advanced. Killed
manually.

Measured file shape (for the cost model): **1901 lines, 30 function decls**.
At the documented ~11.7s startup + ~3.3-4.0s/decl that predicts ~130s, so the
observed >900s is **~7x above** the linear prediction - consistent with the
superlinear per-decl cost being the root cause, and it means the published cost
model under-predicts badly on this file. Profiling the linter on this file
remains the right next step.

# Lint timeout (>600s) on src/compiler/50.mir/hwir/zca_rows.spl

- Date: 2026-08-17
- Status: DUPLICATE of lint_single_file_superlinear_timeout_on_line_count_2026-08-06.md
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  yet located (profiling blocked on this host); optimisation still OPEN.**
- Command: `sh scripts/check/lint-cached.shs src/compiler/50.mir/hwir/zca_rows.spl`
  (via seed `bin/simple lint`), killed by `timeout 600` (rc=124), no verdict line.

## Verdict: cost, not a hang

The linter **terminates and prints an explicit verdict**. Reproduced directly on
a 182-line, 2-function prefix of the file:

```
Lint passed: all files clean      (rc=0, 210s)
```

So the original "hangs" framing is wrong, and that matters: a hang is a deadlock
to break, whereas this is a cost curve to either flatten or bound honestly.
Nothing here should be "fixed" by making the linter skip work.

## Measurements

All taken on the shared dev box under real load — load average and concurrent
`simple` process count are recorded because they materially change the numbers
(a contended box roughly doubles them). No idle-box round was available; these
are an upper envelope, not clean-room figures.

| fixture | decls | lines | wall | per decl | load | procs |
|---|---|---|---|---|---|---|
| 1 trivial fn | 1 | 2 | 12s | — (startup) | 34 | 28 |
| 15 tiny fns | 15 | 61 | 111s | ~6.6s | 47 | 21 |
| 90 tiny fns | 90 | 361 | 436s | ~4.7s | 48 | 25 |
| 4 fns x 45 stmts | 4 | 192 | 107s | ~24s | 39 | 30 |
| 45 fns x 4 stmts | 45 | 315 | 239s | ~5s | 34 | 24 |
| `zca_rows` first 2 fns | 2 | 182 | 210s | ~99s | 36 | 29 |
| `zca_rows` first 8 fns | 8 | 443 | **>2400s** (killed) | >300s | 37 | 29 |

### What the numbers say

1. **Declaration count is LINEAR.** 15 -> 90 tiny declarations leaves per-decl
   cost flat or slightly falling (6.6s -> 4.7s). Splitting a file into more
   functions buys nothing.
2. **Content complexity dominates, and is superlinear in the file.** Two real
   hwir row-builder functions cost ~99s each — 20x a trivial declaration. Going
   from 182 to 443 lines *of the same file* multiplied wall time by more than
   11x for 2.4x the lines. Extrapolating the full 1901-line, 30-function file
   puts it far beyond any practical budget.
3. **Startup is ~12s**, and is *not* the ~310s fixed `Session setup` cost
   another lane measured in `bin/simple test`. Lint does not share that path;
   the two should not be conflated or double-fixed.

### Correction to an earlier number in this investigation

An initial measurement recorded the 2-function prefix at **588s**. That figure
was contaminated — a `cargo build --release` of mine was running concurrently.
The clean re-measurement is **210s**. The 588s number should not be cited, and
the "~30x off the documented model" framing derived from it overstates the gap;
the honest gap is that the documented model tracks *declaration count* while the
real driver is *declaration content*.

## Documentation fixed

`.claude/rules/commands.md` published `~11.7s startup + ~3.3-4.0s per function
decl, superlinear`. The startup figure is accurate (~12s measured). The per-decl
figure is right for *simple* declarations but was being read as a general rule,
which under-predicts real compiler files by more than an order of magnitude and
misled scheduling. That entry now carries the table above and states explicitly
which variable dominates.

## Still open: where the superlinearity lives

**Not located.** Attach-based profiling is unavailable on this host:
`/proc/sys/kernel/yama/ptrace_scope` = 1 and
`/proc/sys/kernel/perf_event_paranoid` = 4, so both `perf record -p` (produced a
0-byte `perf.data`) and `gdb -p` attach are refused without root. Profiling
needs either relaxed host policy, or lint driven as a child under a launcher
rather than attached to.

Candidate shapes, none confirmed — do not treat as findings:
- a per-declaration pass that rescans the whole file or the whole token stream;
- expression-tree work that is quadratic in nesting depth (the hwir rows are
  deeply nested constructor calls, which is exactly the distinguishing feature
  of the expensive fixtures);
- repeated re-resolution of imported symbols per expression rather than once.

A constant-factor tweak on a quadratic is not a fix; the pass structure is what
needs to change once the hot loop is identified.

## Guard

`sh scripts/check/check-lint-cost-budget.shs` pins lint cost on a small
committed fixture so a regression cannot silently return. Fail-closed, same
verdict convention as the other `scripts/check` guards (`PASS`/`FAIL`/`ERROR`
as the last stdout line, ERROR when 0 fixtures were timed), with a fatal
`--selftest` of 4 stub fixtures. It deliberately treats **a silent exit 0 with
no verdict line as FAIL** — that is the failure mode most likely to be
introduced by "optimising" the linter.

Proven to bite in both directions:

```
PASS — 1 fixture(s) checked, lint completed in 51s of a 240s budget (load=52.97, concurrent simple=28)
FAIL — 1 fixture(s) checked, lint exceeded its 5s budget on test/fixtures/lint_cost/nested_expression_row.spl (load=55.53, concurrent simple=29)
```

It does not benchmark `zca_rows.spl` itself: that file costs more than any sane
CI budget, and a gate that always fails gets disabled.

## Specs

- `test/01_unit/compiler/lint/lint_terminates_with_verdict_spec.spl` — lint
  finishes and states an outcome rather than exiting silently (the "not a hang"
  half, made executable).
- `test/01_unit/compiler/lint/lint_still_bites_prevention_spec.spl` — a fixture
  that violates `RAW-RT-001` must still be reported, and the clean fixture must
  not be. This is the arm that fails if lint is made faster by making it look at
  less.
- Fixtures: `test/fixtures/lint_cost/{nested_expression_row,raw_rt_violation}.spl`.

Timing is deliberately NOT asserted inside the specs — wall time depends on
machine load, so a timing assertion there would be flaky rather than
informative. Cost lives in the guard above, which records load alongside its
verdict.

## Follow-up

1. Locate the superlinear term (needs a profiling-capable host).
2. Fix the pass structure, then re-measure the table above and tighten the
   guard's budget.
3. Until then `zca_rows.spl` is effectively un-lintable and is knowingly outside
   the lint sweep — an honest documented bound, not a silent skip.
## Re-verified 2026-08-17 - STILL OPEN, WORSE than filed

Re-ran `nice -n 19 timeout 900 sh scripts/check/lint-cached.shs
src/compiler/50.mir/hwir/zca_rows.spl`. It exceeded **900s** (not just the 600s
in the original filing) and produced **no verdict line**; the log froze at 382
lines after the module-load `[gc-warning]` block and never advanced. Killed
manually.

Measured file shape (for the cost model): **1901 lines, 30 function decls**.
At the documented ~11.7s startup + ~3.3-4.0s/decl that predicts ~130s, so the
observed >900s is **~7x above** the linear prediction - consistent with the
superlinear per-decl cost being the root cause, and it means the published cost
model under-predicts badly on this file. Profiling the linter on this file
remains the right next step.

## 2026-08-17 bounded source fix

No profiler capture exists beyond the wall-clock/log-freeze evidence above,
so the earlier superlinear-per-declaration attribution remains a hypothesis.
Static audit did identify one avoidable deep pass: `check_required_comment`
recursively walks and recopies warning arrays through nested expressions even
when the source contains none of the REQC trigger families. `zca_rows.spl` is
a 132148-byte builder-heavy AST and contains no such trigger.

The lint CLI now uses `required_comment_source_may_match`, a conservative
linear admission check, before that recursive walk. It covers `pass_*`,
`todo(...)`, wildcard cases, and every name in the live dangerous-keyword
registry, including names registered later. The focused regression reads the
exact Zca file and proves rejection while adjacent wildcard and dangerous-name
sources remain admitted.

Status: **SOURCE FIXED / RUNTIME TIMING PENDING**. This isolated worktree has
no deployed pure-Simple CLI with a `lint`/`test` command; the available shared
staged bootstrap executable exposes compile flags only. Per repository policy
no Rust-seed fallback was used, and the 900-second command was not repeated.
A deployed pure-Simple binary must run the focused spec and a bounded lint
timing before this record can close.

## 2026-08-17 macOS ARM deployment-authority audit — still pending

The focused admission spec was invoked once through the executable currently
deployed at `/Users/ormastes/simple/bin/release/aarch64-apple-darwin/simple`
(SHA-256 `f2c216a660da83da1a253d2e8191a3059a66b1d9dc11bbcbaf237fe7e5b8d2bc`):

```
Results: 2 total, 2 passed, 0 failed
Time: 288ms (setup: 10129ms)
```

The one exact `zca_rows.spl` lint timing was then started under a 600-second
process alarm. During startup that same executable identified its authority:

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
```

The run was stopped after 96.99 seconds rather than spending the remaining
budget on inadmissible seed evidence. It had emitted substantially more than
the old 382-line frozen transcript, but it had no lint verdict at interruption;
neither that progress nor the focused 2/2 result can close a criterion that
explicitly requires deployed pure-Simple authority. The isolated worktree also
has no `bin/simple`, and no deployment/provenance receipt beside the executable
establishes a pure-Simple lineage.

Status remains **SOURCE FIXED / PURE-SIMPLE RUNTIME TIMING PENDING**. The exact
remaining host-fixable gap is deployment of a receipt-bound pure-Simple CLI;
after that, run the focused spec once and one bounded exact-file lint timing.
Do not relabel the current release-path seed or cite its path as authority.

# Lint timeout (>600s) on src/compiler/50.mir/hwir/zca_rows.spl

- Date: 2026-08-17
- Command: `sh scripts/check/lint-cached.shs src/compiler/50.mir/hwir/zca_rows.spl`
  (via seed `bin/simple lint`), killed by `timeout 600` (rc=124), no verdict line.
- Context: sequential lint sweep of files changed vs origin/main; sibling files
  (`driver_public_compile_process.spl`, `store.spl`) linted in normal time in the
  same session.
- Known cost model (`.claude/rules/commands.md`): ~11.7s startup + ~3.3-4.0s per
  function decl, superlinear. `zca_rows.spl` appears to exceed the 600s budget on
  its own, so per-decl superlinearity makes this file un-lintable in practice.
- Expected: single-file lint completes within the 600s budget or the linter
  reports partial progress.
- Follow-up: profile lint on this file; the superlinear per-decl cost is the
  suspected root cause.
