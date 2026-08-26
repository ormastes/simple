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
> The documented cost of that state is 100-1000x — but **measured, unblocking it
> buys 1.23x**, not 100x (182-line fixture, 222.95s -> 181.37s user CPU). That
> negative result matters as much as the finding: the de-JIT is real and worth
> fixing, and it is still not the whole story.
> Measured in-process, the lexer is **linear** in token count (exponent 1.09
> over a 2.8x range) at ~21 ms/token — a constant factor, not a quadratic pass.
> Whole-`lint` does still show ~1.33 across 49 -> 182 lines, so a *secondary*
> superlinear term survives above the tokenizer; it is not the dominant one and
> it is still unlocated. The "superlinear parser" framing below overstates it.
> Full evidence, all arms, and the fix options:
> `doc/08_tracking/bug/lint_dejits_whole_program_span_struct_collision_2026-08-18.md`.

- Date: 2026-08-17
- Status: **OPEN (bounded, guarded)** — DUPLICATE of
  lint_single_file_superlinear_timeout_on_line_count_2026-08-06.md.
  **2026-08-18: the dominant term IS located** — see the banner above — and it
  is a de-JIT constant factor, not a superlinear term. Optimisation still OPEN
  (the fix is a struct rename plus a driver-heuristic change, neither landed). The "not a hang / cost not deadlock" verdict, the
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
2. **Content complexity dominates.** Two real hwir row-builder functions cost
   ~99s each — 20x a trivial declaration. **Corrected 2026-08-18:** the
   "superlinear in the file" claim attached to this point rested on the
   182 -> 443 line comparison, and the 443-line arm is a **KILLED** run
   (`>2400s`, no verdict). A kill is a lower bound, so no ratio and no exponent
   may be computed from it, and "more than 11x for 2.4x the lines" is not a
   measurement. Measured properly, in-process, the lexer is **linear** in token
   count (exponent 1.09 across a 2.8x range). The reason `zca_rows.spl` exceeds
   any practical budget is its size times a very large *constant* per token
   (~21 ms), not a growth exponent.
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

## Where the superlinearity lives — SUPERSEDED 2026-08-18

**Located, and it is not superlinearity.** See the banner at the top of this
file. The dominant term is a 100-1000x constant factor from running the
compiler frontend interpreted, caused by two stacked de-JIT triggers. The
candidate shapes listed below (per-declaration rescans, depth-quadratic
expression work, per-expression symbol re-resolution) were **not** confirmed and
none of them is the cause; they are kept only as a record of what was ruled out.
The 8-function `>2400s` row in the table above remains a KILLED run — a lower
bound, never a measurement — and must not be used to fit an exponent.

The rest of this section is the historical account of why profiling was blocked.
The blocker was real but the workaround was simpler than assumed: yama
`ptrace_scope=1` forbids *attaching* to a non-descendant, but the actual
localisation needed no profiler at all — a default-off `LINTPROF` timer plus an
in-process cost curve was enough.

Attach-based profiling is unavailable on this host:
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

## Text tier (check_all_rules) — root-caused and fixed 2026-08-18

The text-tier rule loop (separate from the parse cost above) was attributed with new
per-rule `LINTPROF` probes (same env-gated idiom, default off) added to BOTH
`check_all_rules` implementations:
- `src/compiler/90.tools/fix/rules/registry.spl` (`rule:` labels) — instrumented, but
  **the run resolves the STDLIB copy**, not this one;
- `src/lib/nogc_sync_mut/tooling/easy_fix/rules.spl` (`std_rule:` labels) — this is the
  one that executes (proven: only `std_rule:` lines appear in the profile).

Profile on `fx_m5_c10.spl` (25 lines, load ~20-25):

| mark | before (us) | after (us) |
|---|---|---|
| `std_rule:check_unnamed_duplicate_typed_args` | 671,034 | 40,896 |
| — of which `dup_args:fix_loop` (call-site scan) | 646,775 | 32,982 |
| `check_all_rules` (remainder) | 748,676 | 80,623 |
| `TEXT_TIER_TOTAL` | 986,137 | 172,862 |

(The originally reported ~12.4s check_all_rules was the same code under load 33-55;
the ratio, not the absolute, is the signal: ~8x on check_all_rules, ~5x on the tier.)

Root cause: `_collect_line_call_replacements` stepped **one character at a time**
through every line for every duplicate-typed signature, calling interpreted
`_matches_identifier_at` per character (O(sigs x chars) interpreted calls).
`_short_find_text_from` had the same per-char interpreted loop.

Fix (behavior-identical, `src/lib/nogc_sync_mut/tooling/easy_fix/rules.spl`):
- fast-reject lines with `line.contains(sig.name)`;
- on a failed identifier-boundary match, jump to the next occurrence with native
  `.find()` instead of `i + 1` stepping (an occurrence that fails at `i` cannot
  match at `i` again, and `.find()` from `i+1` yields exactly the next candidate);
- `_short_find_text_from` rewritten onto native `.find()` (used by several rules).
  Note: `slice(...).find(...)` must go through an intermediate typed `val` —
  chained `.find` on the erased receiver fails (`method 'find' not found ... in
  nested call context`), the known chained-methods-on-erased-receivers limit.

Verified:
- Lint stdout **byte-identical** before/after on 3 files (fixture + 
  `src/lib/common/compute/placement_contracts/storage.spl` +
  `src/lib/common/crypto/typed/__init__.spl`; 268/256/256 output lines, findings present).
- `lint_profile_spec.spl`: Results: 17 total, 17 passed, 0 failed.
- `collection_easy_fix_spec.spl`: Results: 4 total, 4 passed, 0 failed.
- `lint_cli_duplicate_typed_args_contract_check.spl` FAILs identically at HEAD with the
  pre-change files restored (zero-examples / DTYP001 parity FAIL) — pre-existing, not
  introduced by this change; left as-is.

## 2026-08-18 — Parser-side call-count mitigation (pure-Simple lane, landed)

Files: `src/compiler/10.frontend/core/lexer.spl`, `src/compiler/10.frontend/core/parser.spl`.

What changed in `parser_advance()` (behavior identical, verified by specs + lint):
- **Batched lexer snapshot**: new `lex_next_snapshot()` in lexer.spl returns
  `[kind, line, col, text]` in ONE cross-module call; parser_advance previously
  made four (`lex_next` + `lex_token_text` + `lex_token_line` + `lex_token_col`).
  The kind-mask (180/181/182/190 -> "") is `parser_current_token_text` inlined.
- **Inlined slot setters**: `par_kind_set/par_text_set/par_line_set/par_col_set`
  replaced with direct `par_*_slot[0] = ...` writes; the
  `SIMPLE_BOOTSTRAP_PAR_*` env-save mirror is preserved behind a single
  `par_env_save_enabled()` check (was checked 4x, once per setter).
- PARSEPROF branch updated to time the same batched path
  (`tok:lex_snapshot` replaces `tok:lex_next`+`tok:cur_text`).

Key measurement that refines the 2026-08-18 cross-module model: PARSEPROF shows
**same-module calls are also milliseconds each** under the seed interpreter —
`par_line_set`+`par_col_set` (two same-module calls) cost ~8.8ms/token before
inlining (`tok:line_col` 5.24s over 351 tokens -> 3.10s after removing the
lexer hops; near-zero once the setters were inlined). So the fix axis is total
CALL COUNT on the per-token path, not only cross-module hops. Net: ~7 calls
removed per token (3 lexer hops + 4 setter calls incl. their 4
`par_env_save_enabled` sub-calls collapsed to 1).

Interleaved A/B on the shared box (base files restored vs new, CPU user time),
`bin/simple lint` on scratchpad fixtures:
- `fx_m5_c10.spl`: base 44.8/36.5/23.2s vs new 25.3/26.9/21.6s — new faster in
  all 3 pairs, medians 36.5s -> 25.3s (~30% CPU).
- `fx_m20_c10.spl`: pairs (79.2 vs 81.2), (111.1 vs 83.9), (83.2 vs 61.1) —
  new faster 2 of 3 under heavy load spikes.

Verified: lexer_brace_escape_spec 8/8, parser_contextual_keyword_named_arg_spec
8/8, parser_move_contextual_keyword_spec 4/4, parser_describe_fn_literal_spec
2/2; `bin/simple lint src/lib/common/base_encoding.spl` still "all files clean".

Still open: the superlinear content-complexity term (this change shaves the
linear per-token constant only), and the per-CALL millisecond cost itself,
which is a seed-interpreter issue owned by the Rust lane.

## FIXED AND DEPLOYED (2026-08-18 06:12)

- Seed env-cache landed (`7dc9d1f962f`): captured module env cached per owner
  module with load/write invalidation, `SIMPLE_INTERP_ENV_CACHE=0` kill switch.
- Combined with the parser hop reduction and text-tier fix: fx_m20_c10 lint
  ~49s -> **14s** on the deployed binary (cache-off 26s). Cache on/off spec
  parity proven (8/8, 12/12, 12/12 identical both modes).
- Remaining: the seed per-call constant is reduced, not zero; the strategic fix
  stays the self-hosted deploy. zca_rows full-file lint should be re-measured
  next session against the ~99s/decl history.
