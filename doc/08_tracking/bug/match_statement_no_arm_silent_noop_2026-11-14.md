# A `match` whose scrutinee matches no arm silently did nothing (2026-11-14)

Status: **fixed on the Rust seed (interpreter + JIT/native lowering)**; open on
the pure-Simple core interpreter and the self-hosted MIR lowering (see
"Residuals").

## Owner decision (2026-11-14)

> match with no arm should fail

A `match` whose scrutinee matches no arm fails with a runtime error that names
the value and the location. It never silently does nothing. This holds for the
statement form and the expression form alike. An arm whose guard is false does
not count as matched. Unchanged: `case _:` / `else` arms, `if val`, `val`
destructuring and `for` patterns.

## Symptom (before)

```text
match n:            # n == 7
    case 1: print "one"
    case 2: print "two"
print "after"       # reached; the match was an invisible no-op
```

The seed interpreter returned `Control::Next` from `exec_match_core` and set
`last_value = Nil` in the two block-closure paths; the seed HIR lowering ended a
statement-position arm chain with nothing (`lower_match_arms_stmt`) or `Nil`
(`lower_match_with(.., exhaust_panic=false)`). A mis-typed pattern — the classic
being `Ok`/`Err` arms over an `Option` — therefore skipped its body with no
diagnostic. A match **expression** already failed closed (interpreter:
`invalid pattern` error; JIT: `rt_panic`, since 2026-11-03).

## Behaviour now

| Lane | No arm matched | Message |
|---|---|---|
| Seed interpreter | `error: semantic: <file>:<line>:<col>: invalid pattern: match statement\|expression exhausted without matching any pattern for <type> value <value>; arms [...]`, exit 1 | type, value, source location, every arm |
| Seed JIT / native (HIR lowering) | `rt_panic` + abort (exit 134) | `invalid pattern: match statement\|expression exhausted without matching any pattern (no arm matched); match at line N` for a `match` statement, `...; first arm at line N` for a match in expression syntax (including one used as an expression statement). No value: the lowered code has no formatter for an arbitrary scrutinee at that point. |
| Pure-Simple core interpreter | unchanged: warning by default, abort under `SIMPLE_SAFETY_PROFILE=critical`, enum scrutinees only | residual 1 |
| Self-hosted MIR lowering | unchanged: warn-only for a non-total enum match, trap for a total one | residual 2 |

The implicit tail `match` of a function with a declared non-void return was
already made fail-closed on the JIT by `c739aa3c104`; it now shares the same
tail (`lower_match_arms_stmt` takes the panic type) and keeps reporting the
expression form on the JIT, because that match's value is the return value. The
interpreter executes the same tail through the statement path and says
"statement" there; the wording differs, the failure does not.

The appended panic diverges, so it must not count as a value: a statement
match that used to end in a missing `else` now ends in `rt_panic` typed NIL,
and two analyses that ask "does this branch leave a value" would have changed
their answer — the MIR `if`-merge slot type (a float-valued match nested in a
tail `if` would have merged through an I64 slot and returned 0.0) and
`body_produces_value` for unannotated functions. Both now skip it via
`HirExpr::is_match_exhausted_panic`. Found by the independent review, pinned by
the `float_nested_tail=2.5` JIT case (red before the fix, green after).

One shared constructor per lane: `match_no_arm_error` (interpreter,
`interpreter_control.rs`) and `match_exhausted_message` / `match_exhausted_panic`
(HIR, `hir/lower/expr/control.rs`).

## Evidence

Spec: `test/01_unit/compiler/control_flow/match_no_arm_fails_spec.spl` with
run-path probes under `match_no_arm_probes/` (statement) and
`match_no_arm_expr_probes/` (expression). Each probe prints `before`, runs the
match, prints `after`; a failing match must show `before`, must not show
`after`, must exit non-zero and must carry the message. Both seed engines are
exercised for int, text, enum, Option and tuple scrutinees, all-guards-false
(both forms), a match inside a loop and inside a block closure, and the
unchanged cases (`case _:` silent, matched arm, exhaustive enum, binder
catch-all, `None` arm, float-valued nested tail match, expression arms,
`break`/`continue` arms in a loop).

- Base seed (before): 5 passed, 15 failed — every statement-form case and every
  JIT case (the JIT expression cases fail only on the new message token).
- Branch seed: 20 passed, 0 failed.

Rust unit tests: `hir::lower::tests::control_flow_tests`
(`test_statement_match_without_wildcard_fails_closed`,
`test_tail_match_with_wildcard_has_no_panic_and_void_tail_is_statement_form`).

## Census of existing fall-through sites

Method: a throwaway seed (`simple_census`, never committed) that keeps the old
silent behaviour on the **interpreter** lane but appends
`<file>:<line> <type> <value>` to a log every time a statement match takes no
arm. `simple test` runs specs on the interpreter, so this lists every dynamic
fall-through site a spec reaches, in the spec and in all product code it calls.
The census seed's JIT lane already aborts, and every non-OK row was re-run on
the base seed and the branch seed and compared.

| Set | Specs run | Verdicts on the census seed | Files with a fall-through site | Distinct sites |
|---|---|---|---|---|
| A: every spec named `*match*`/`*pattern*`/`*enum*`/`*option*` under `test/01_unit` + `test/03_system`, plus all of `compiler/{control_flow,interpreter,95.interp,semantics}`, `compiler_core`, `lib/test_runner`, `03_system/language` | 1036 | 868 OK, 164 ERROR, 4 no verdict | 3 (+ the new spec's own probes) | 4 |
| C: every 95th of the remaining specs (legacy `test/unit`, `test/integration` mirrors excluded) | 223 | 175 OK, 46 ERROR, 1 BLOCKED, 1 no verdict | 0 | 0 |

Sites found (all in spec fixtures; **none in `src/`**):

| Site | Scrutinee | Triage |
|---|---|---|
| `test/01_unit/compiler/interpreter/match_arm_early_return_spec.spl:28`, `:35` | `Dir::East`, `Dir::South` | fixture relied on the no-op; explicit `case _: pass` added, assertions unchanged |
| `test/01_unit/compiler/50.mir/match_guard/match_guard_parity_spec.spl:206` | `i64 3` | spec case pinned "falls through like the seed (no abort)"; rewritten to the inputs an arm accepts (old rule removed, see residual 2) |
| `test/01_unit/compiler/semantics/safety_checker_unsafe_boundary_spec.spl:38` | `SafetyError::StaticReferenceOutsideUnsafe` / `MutableReferenceToImmutableStatic` (14 hits) | counting helper omitted two variants; explicit arms added. The spec was already red before this change (10 passed / 8 failed on base and on branch) |

Base-vs-branch re-run of every non-OK or site row (170 in A on the pre-merge
seed pair, 48 in C on the merged pair): verdict and pass/fail counts are
identical on both seeds apart from the three files
above (now green or unchanged after the edits) and
`interpreter/global_array_push_linear_spec.spl`, a wall-clock ratio test that
flipped once under host load and passes on both seeds when re-run. The ERROR
rows are therefore pre-existing failures, not fallout.

### Self-hosted compiler

`simple run src/app/cli/bootstrap_main.spl compile hello.spl --format=smf`
(the pure-Simple compiler executed by the seed, `SIMPLE_BOOTSTRAP=1`) exits 0
with no exhaustion message on the base seed and on the branch seed, in
interpreter mode and in JIT mode, and logs zero fall-through sites on the
census seed. The same driver's `native-build` did not finish inside 850 s on
any seed, base included, so it gives no evidence either way.

Coverage is **dynamic**: a site is found only if a run reaches it with a value
that matches no arm. The static upper bound is the 286-477 candidate
non-exhaustive enum sites of
`doc/08_tracking/bug/match_enum_fallthrough_silent_2026-08-01.md`, most of which
cannot be resolved statically (duplicate enum names).

## Residuals

1. **Pure-Simple core interpreter** (`src/compiler/10.frontend/core/interpreter/`
   `eval.spl:928`, `eval_stmts.spl:744`, `eval_tables.spl:1225`). A no-arm match
   on an enum value warns by default and aborts only under the `critical`
   profile (`match_fallthrough_set_abort`); a non-enum scrutinee is not
   diagnosed. Making abort the default is not mechanical: the flag is one rung
   of the assurance-profile ladder (`eval_apply_assurance_profile_phased`,
   Deny -> Warn under warning phase) and
   `test/01_unit/compiler_core/interpreter/match_fallthrough_diagnostic_spec.spl`
   pins "unset profile does not resolve to Deny". Not changed here.
   `doc/07_guide/language/strictness_tiers.md` now states that its table is the
   core-interpreter lane only.
2. **Self-hosted MIR lowering**
   (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`). A
   non-total enum match with no default stays warn-only by a documented
   deferral (bare-name enum collisions make the static coverage unsound); only a
   textually total match traps. Not changed here.
3. **Stage 2+ bootstrap under this seed is unverified.** The seed compiles the
   self-hosted compiler through the changed HIR lowering, so a statement match
   in compiler source that falls through at run time now aborts instead of
   continuing. The only evidence gathered is the `compile --format=smf` run under
   "Self-hosted compiler" above; a `--stop-after-stage2` run was not made.
4. **JIT message carries no scrutinee value**, only the form and the line.
5. JIT-lane product coverage is thin: specs run on the interpreter, so a site
   where the JIT's pattern lowering fails to match a value the interpreter does
   match (previously a silently skipped body) is not in the census. It now
   aborts loudly instead of being skipped.
6. **Pre-existing, observed while pinning the review fix, not changed here:** on
   the seed JIT an *unannotated* function whose body ends in a no-wildcard
   match with value arms returns 0 instead of the arm value
   (`fn pickv(n):` / `match n:` / `case 1: 10` / `case 2: 20`; `pickv(2)` is 20
   on the interpreter, 0 on the JIT, on the base seed and on this branch
   alike). `body_produces_value` classifies the body as procedural because the
   arm chain has no value-producing `else`. This change deliberately keeps that
   classification (the appended panic is not a value); making a diverging tail
   neutral would return 20 but changes the ABI of such functions from void to
   `Any`, which needs its own review.
7. **Census sample size.** Set C is roughly 1% of the ~21,000 specs outside set
   A. Zero sites in 223 specs does not bound the remainder; a spec outside both
   sets that reaches a fall-through site now fails with the message above
   instead of passing silently.

## Cost

Hot loop, 4-arm int `match` statement, six alternating runs, host load ~25
(base `efaae95b0b2aa81a`, branch `5ce8396bcd3fe228`, sha256 prefixes):

| Lane | Base min / runs (s) | Branch min / runs (s) | Max RSS base / branch |
|---|---|---|---|
| Interpreter, 2M iterations | 1.99 / 1.99 2.11 2.07 2.20 2.22 2.03 | 2.02 / 2.31 2.09 2.27 2.13 2.25 2.02 | 34.6 MB / 22.7 MB |
| JIT, 400M iterations | 0.84 / 1.30 1.13 0.84 0.86 1.17 1.40 | 0.87 / 0.87 0.93 1.19 1.19 0.91 1.10 | 36.7 MB / 35.6 MB |

Minimums differ by 2-3%, inside the run-to-run spread on a loaded host; the
matching path executes no new code on the interpreter, and one never-taken
branch target on the JIT.
