# Lint cost on src/compiler/50.mir/hwir/zca_rows.spl — dominant term is an interpreted frontend, not a superlinear parser

> **2026-08-18 — CAUSE FOUND, and it is not the one this row hunts for.**
> `simple lint` never JITs: `src/app/cli/lint_entry.spl` imports
> `std.cli.cli_util (get_cli_args)`, which trips the entry-file text-grep in
> `should_prefer_interpreter_for_source`
> (`src/compiler_rust/driver/src/exec_core.rs:1412`) and pins the WHOLE program
> — the entire pure-Simple compiler frontend included — to the seed's
> tree-walking interpreter. Force the JIT on and it still drops the whole module
> for a second, independent reason: two structs named `Span`
> (`00.common/diagnostics/span.spl` vs `10.frontend/core/lexer_types.spl`)
> collide in HIR lowering's global by-bare-name struct resolution.
> The documented cost of that state is 100-1000x.
> Measured in-process, the lexer is **linear** in token count (exponent 1.09
> over a 2.8x range) at ~21 ms/token — a constant factor, not a quadratic pass.
> The "superlinear parser" framing below is therefore **not supported** and
> should not drive optimisation work. Full evidence, all three arms, and the
> fix options:
> `doc/08_tracking/bug/lint_dejits_whole_program_span_struct_collision_2026-08-18.md`.

- Date: 2026-08-17
- Status: **OPEN (bounded, guarded)** — DUPLICATE of
  lint_single_file_superlinear_timeout_on_line_count_2026-08-06.md.
  The superlinear term is **not yet located** (profiling blocked on this host);
  optimisation still OPEN. The "not a hang / cost not deadlock" verdict, the
  guard, and the specs are all present and green.
- **Re-verified 2026-08-17 (later pass), by execution, not inspection:**
  - `out=$(timeout 500 sh scripts/check/check-lint-cost-budget.shs); rc=$?`
    -> `rc=0`, `selftest: 4 fixture(s) passed`,
    `PASS — 1 fixture(s) checked, lint completed in 62s of a 240s budget
    (load=51.03, concurrent simple=36)`. The guard is live and non-vacuous.
  - `wc -l src/compiler/50.mir/hwir/zca_rows.spl` -> **1901** (unchanged; the
    file has not been split or shrunk, so the bound still applies).
  - Both specs and both fixtures present:
    `ls scripts/check/check-lint-cost-budget.shs
    test/01_unit/compiler/lint/lint_{terminates_with_verdict,still_bites_prevention}_spec.spl
    test/fixtures/lint_cost/` -> all 5 paths exist.
  - Profiling still blocked: `cat /proc/sys/kernel/yama/ptrace_scope
    /proc/sys/kernel/perf_event_paranoid` -> `1` / `4`. Unchanged, so
    follow-up 1 below cannot be started on this host.
  - `zca_rows.spl` itself was **deliberately not lint-timed** in this pass and
    no files were batched, per the standing cost bound.
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

## Bisection findings (2026-08-18, fixture ablation — profiler still blocked)

Binary: bin/release/x86_64-unknown-linux-gnu/simple (rebuilt seed, 2026-08-18 01:08, 59,620,392 B).
All times single runs on the shared box, ~12s startup included. Fixtures in session scratchpad lint_bisect/.

| fixture | time |
|---|---|
| zca fn1 only (13 ctor entries) | 43s |
| zca fn2 only (46 comb_op entries) | 218s |
| zca fn2 + identical renamed copy | 313s (1.46x — repeated content is CHEAP) |
| fn2, comb_ops halved (23 entries) | 144s |
| fn2, comb_ops emptied | 86s |
| synthetic: 40 static calls, 1-method class | 36s |
| synthetic: 40 free-fn calls | 43s (static dispatch NOT the driver) |
| synthetic + zca imports | 39s (import context NOT the driver) |
| synthetic: 40 calls, 40-method class | 96s |
| synthetic: 10 calls, 40-method class | 68s |

Conclusions:
- Cost is roughly LINEAR per array entry (~2.5-3.2s/entry in zca, ~0.6s in a 1-method-class synthetic),
  so the "superlinear in file" observation tracks entry counts, not a global quadratic.
- The dominant term is per-METHOD-DECLARATION on the callee class (~1.2s per static method even with
  few calls: 40-method class costs ~50s body before calls scale), plus a methods x call-sites
  interaction (~0.9s/call at 40 methods vs ~0.3s at 1 method).
- Duplicated identical functions are sub-linear (1.46x), so per-content caching exists; distinct
  declarations do not share it.
- Suspect shape: per-declaration semantic elaboration re-processes the whole impl (per-method cost),
  and each call site rescans the callee class method list. Fix direction: memoize per-class method
  tables across declarations/call sites in the lint path.
- zca_rows.spl (30 such functions, hundreds of Hw* ctor entries against many-method hwir classes)
  is exactly the worst case of this model; no single construct removal fixes it — the per-decl and
  per-call constants must drop.

## 2026-08-18 — parse-phase attribution: the cost is the SEED INTERPRETER's per-call env rebuild, not a pure-Simple hotspot

Instrumented the declaration parse path (level-gated on `SIMPLE_PARSE_PROFILE=1`, default off,
same idiom as `lint_prof_now`/`lint_prof_mark`; probes live in
`src/compiler/10.frontend/core/parser_decls_use.spl` (`parse_prof_now`/`parse_prof_mark`,
per-method sub-phases) and `src/compiler/10.frontend/core/parser.spl` (`parser_advance`
per-token split)). PARSEPROF aggregate on `fx_m5_c10.spl` (5 static methods, 25 lines, 1103 bytes):

| PARSEPROF label | total | n | avg |
|---|---|---|---|
| method:signature | 5.4s | 5 | ~1.1s |
| method:body | 12.0s | 5 | ~2.4s |
| method:declreg (decl_fn + side tables) | 0.1s | 5 | 25ms |
| tok:lex_next | 4.6s | 351 | 13.2ms |
| tok:kind_set (one slot write) | 1.4s | 351 | 4.0ms |
| tok:cur_text (2-deep slot read) | 1.5s | 351 | 4.3ms |
| tok:text_set | 1.3s | 351 | 3.8ms |
| tok:line_col (2 accessors) | 4.5s | 351 | 12.9ms |

Every sub-phase is uniformly slow: a trivial one-array-slot write costs ~4ms; parse cost is
~48ms/token, entirely accounted for by per-CALL overhead, not by any algorithm in the parser.

Isolation experiments (decisive):
- Plain interpreted 10k calls to a local slot-setting fn: **0.08µs/call** (`bin/simple run`, JIT'd)
  and ~0.9µs/call interpreted.
- Same call INSIDE a process that imported `compiler.core.parser`: local fn 8.7µs/call, but
  **cross-module `par_kind_get()` = 1.38 ms/call** (1k calls = 1.38s), a ~160x cross-module penalty.
- `parse_module_silent_checked` on the 1103-byte fixture outside lint: 16.7s — reproduces the whole
  cost with zero lint code involved.

Root cause (named, in the Rust seed): `captured_env_with_live_globals_inner`
(`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:59`) rebuilds the callee's
environment on EVERY interpreted call — cloning the owner module's full globals map
(`MODULE_GLOBALS_BY_OWNER ... .clone()`), resolving and cloning every imported global binding, and
re-`bind_global`ing each name. `compiler.core.parser`'s module has hundreds of globals/imports, so
each cross-module call into it costs ~1.4ms. The parser makes a few such hops per token
(`parser_advance` -> `lex_next` -> accessors), giving the measured ~1.2s per 2-line declaration.

Verdict per this bug's fix-direction note above: the earlier "memoize per-class method tables"
suspicion is WRONG for the parse phase — there is **no single pure-Simple hotspot**; the parser's
own algorithms are fine (decl registration is 25ms/decl). The fix belongs in the seed interpreter
(cache the built env per (owner, globals-generation) instead of rebuilding per call), or in not
running lint interpreted at all. Behavior-identical pure-Simple mitigation would require merging
the parser's modules to eliminate cross-module hops — rejected as a rewrite, not a fix.

Verified after instrumenting (probes off by default, no behavior change):
- `fx_m5_c10` lint 39s / `fx_m20_c10` 49s (same-or-better vs 44s/~55s baseline, shared box).
- `lexer_brace_escape_spec.spl`: Results: 4 total, 4 passed, 0 failed.
- `parser_contextual_keyword_named_arg_spec.spl`: Results: 8 total, 8 passed, 0 failed.
- `parser_move_contextual_keyword_spec.spl`: Results: 4 total, 4 passed, 0 failed.
- `bin/simple lint src/lib/common/base_encoding.spl`: "Lint passed: all files clean".
