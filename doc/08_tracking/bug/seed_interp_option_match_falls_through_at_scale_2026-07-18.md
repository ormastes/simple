# Seed interpreter: `.?` boolean-context consumers re-decide presence from payload truthiness ("0 is falsy" landmine)

**Date:** 2026-07-18
**Lane:** N2 (root-caused from lane M4's report)
**Status:** Root-caused and fixed at the source (`src/compiler_rust`). **Fix
NOT YET VERIFIED by rebuild** — the CPU load gate (see "Verification status"
below) blocked `cargo build`/`cargo test` this session. The `.spl` regression
test is committed and currently RED against the pre-fix seed binary, as
expected; it must go GREEN after the next seed rebuild.
**Severity:** P1 (silent wrong result) — any `if opt.?:` / `elif opt.?:` /
`while opt.?:` / a `match` arm's `if guard.?:` on an `Option<T>`/`Result<T, E>`
(or a bare nilable value) whose present payload is itself falsy under
`Value::truthy()` (`Some(0)`, `Some(false)`, `Some("")`, `Ok(0)`, a bare `0`,
…) silently takes the wrong branch.

## Original report (lane M4)

M4 reported: `match opt: case Some(local_id): ... case nil: ...` on an
`i64?` executes NEITHER arm when the value is `Some(0)` — falling through
both, silently returning nil — and traced the crash site to
`src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl`'s SSA path
(`ssa_operand_push_local`), but said it only manifests "at full-driver
scale."

## What this lane found

The literal symptom as described (a plain `match ... case Some(x): ...
case nil: ...` falling through both arms) does **not** reproduce in
isolation: `match` dispatches on the interpreter's `Value::Enum` discriminant
via `pattern_matches`, which is correct — `Some(0)` matches `case Some(x)`
and binds `x = 0` fine, in every execution mode tried (plain `bin/simple
run`, the native/cranelift `InterpCall` hybrid bridge via
`SIMPLE_NATIVE_BUILD_RUST=1 native-build --backend cranelift`, and the
`bin/simple test` SSpec runner).

But `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl` and
`var_reassign_analysis.spl` are full of comments like:

```
# NOTE: explicit match, not `if lo.?:` -- local id 0 landmine, see
# ssa_max_local_from_operand.
```

pointing at `.?` (the existence-check operator), not `match`, as the actual
landmine — and warning that a positive `if written.?:` truthiness check
"silently reintroduces the SAME class of bug for MirLocal id 0
specifically: the bootstrap seed interpreter's `.?` on a boxed `i64?`
collapses `Some(0)` to falsy." That is the real bug M4's trace was pointing
at; "match falls through" was an imprecise restatement of it.

This lane reproduced that precisely, with a **minimal, isolated** `.spl`
repro (no `var_reassign_ssa.spl`/full-driver involvement needed):

```
fn describe_option_dot_check(opt: i64?) -> text:
    if opt.?:
        "some:" + opt.unwrap().to_text()
    else:
        "none"
```

Called with `Some(0)`, run through the `bin/simple test` SSpec runner (which
executes the trailing `if` in *value/implicit-return position*, i.e. via
`exec_if_core`), this returns `"none"` instead of `"some:0"` — the exact bug
class, cheaply reproducible. New regression spec:
`test/03_system/interpreter/option_match_some_zero_regression_spec.spl`.

## Root cause (corrected — see "First attempt was wrong" below)

`Expr::ExistsCheck` (the `.?` operator, `interpreter/expr.rs`) is **not**
the bug. It correctly evaluates presence and returns "the unwrapped value
if present, `Value::Nil` if absent" — this design is intentional and
load-bearing: `.? ??` (nil-coalescing) and `if val v = expr.?:` (pattern
binding) both need the real unwrapped *value* back, not a bare boolean
(confirmed by `test/03_system/feature/usage/exists_check_value_return_spec.spl`,
18 examples, all passing pre-fix, several of which specifically exercise
`.?`'s value-returning contract). For `Some(0)`: `ExistsCheck` unwraps to
`Value::Int(0)`, computes `is_present` on that unwrapped value (`Nil` →
false, empty `Array`/`Dict`/`Str`/Set → false, **anything else → true**,
including any `Int`/`Bool`/`Float` regardless of value) — `is_present` is
correctly `true` for `Some(0)`, and `ExistsCheck` correctly returns
`Value::Int(0)` (not `Value::Nil`).

**The actual bug is at the consumption boundary.** Every `if`/`elif`/`while`
condition and `match`-arm guard clause in the interpreter evaluates its
condition expression and then calls generic `Value::truthy()` on the
result to decide whether to take the branch. `Value::truthy()`
(`value_impl.rs`) is, by design, `Value::Int(i) => *i != 0` — correct for
ordinary boolean-context values (`if some_i64_var:`). But when the
condition expression is `expr.?` (`Expr::ExistsCheck`), its returned value
already *is* the presence decision (unwrapped value = present, `Nil` =
absent) — running that value back through generic `.truthy()` **re-decides
presence a second time**, this time from the *payload's* truthiness, and
disagrees with `.?`'s own (correct) decision for any present-but-falsy
payload: `Some(0)` → unwrapped `Int(0)` → `Int(0).truthy() == false` →
`if opt.?:` silently takes the `else` branch even though `opt` was
genuinely `Some(0)`.

## First attempt was wrong (documented for the next reader)

The first fix attempted here changed `Expr::ExistsCheck` itself to
determine presence from the Option/Result *discriminant* only and return
`Value::Bool(is_present)` instead of the unwrapped value, reasoning (from
`hir/lower/expr/control.rs`'s `lower_exists_check`, which always lowers
`.?` to a discriminant-only `rt_is_some` **bool**-typed call) that `.?` was
never meant to be value-chainable on the interpreter either.

That was disproven by actually running
`test/03_system/feature/usage/exists_check_value_return_spec.spl` (18
examples, 0 failures, pre-fix): several passing tests explicitly rely on
`.?` returning the real value — `val result = opt.? ?? 0` needs `opt.?` to
evaluate to the payload (`42`), not `true`, for `??` to pass it through
correctly; `if val s = opt.?: result = s` needs `s` to bind to the payload
(`"hi"`), not a bool; `if val name = input.?:` on an **empty** bare string
needs `.?` to have already applied its own emptiness check (returning
`Nil`) so `optional_let_binding` correctly skips — collapsing `.?` to a
bare bool broke all of these. The HIR lowering's "always bool" behavior is
the native/compiled path's own choice (which routes `if val` through a
completely separate `if_let_pattern_condition`/pattern-match mechanism, not
through `.?`'s return value at all — see `stmt_lowering.rs`'s S70 comment,
which explicitly strips one `ExistsCheck` layer before generating the
`rt_is_some` condition, precisely because HIR *also* treats `.?`'s bool as
unsuitable for value-binding purposes). The tree-walk interpreter's
"return the value" design was correct all along; only its consumption was
buggy.

## Fix

`interpreter/expr.rs`'s `Expr::ExistsCheck` is **unchanged from its
original behavior** (reverted back after the above false start; only the
comment was updated to point at the real fix location).

Added `is_condition_present(condition_expr: &Expr, val: &Value) -> bool` in
`interpreter_control.rs`:

```rust
pub(crate) fn is_condition_present(condition_expr: &Expr, val: &Value) -> bool {
    if matches!(condition_expr, Expr::ExistsCheck(_)) {
        !matches!(val, Value::Nil)
    } else {
        val.truthy()
    }
}
```

and replaced `cond_val.truthy()`/`elif_val.truthy()`/`guard.truthy()` with
`is_condition_present(condition_expr, &cond_val)` at every boolean-context
condition call site found in the interpreter's `if`/`elif`/`while`
statement and expression forms, and `match`-arm guard clauses:

- `interpreter_control.rs`: `exec_if` (main condition, elif condition,
  loop-invariant-hoisting while fallback, plain while condition), `exec_if_core`
  (main condition, elif condition), `exec_match_core`'s arm-guard evaluation.
- `interpreter_call/block_execution.rs`: both sibling closure-block `if`
  executors (main condition, elif condition, arm-guard, plain `while`
  condition) — these duplicate `interpreter_control.rs`'s logic for
  lambda/block-closure/BDD execution and needed the identical fix (mirrors
  the pre-existing pattern of bug #188a needing separate fixes in each
  sibling executor).
- `interpreter/expr/control.rs`: the **expression-form** `if`/`match`
  (`x = if opt.?: a else: b`, and its arm-guard clause) — the value-position
  sibling of the statement forms above, with the identical bug.
- `interpreter/node_exec.rs`: the `? condition -> result` guard-clause
  statement.

`if val`/`elif val`/`while val` (pattern-binding) call sites were
**reverted to their original, untouched form** (a mid-session attempt to
"fix" them by stripping `ExistsCheck` was itself unnecessary and wrong once
`ExistsCheck`'s value-returning behavior was correctly left alone — see
git history on this file for the false start and its revert).

### Known follow-up (not fixed here — explicitly out of scope)

A repo-wide grep for `.truthy()` in the interpreter turns up ~30 more call
sites with the same *shape* (boolean `and`/`or`/`not` operators in
`interpreter/expr/ops.rs`; array/collection predicate methods `filter`/
`all`/`any`/`take_while` in `interpreter_method/collections.rs` and
`interpreter_helpers/collections.rs`; the BDD test framework in
`interpreter_call/bdd.rs`; misc. dispatch in `interpreter_helpers/
method_dispatch.rs`). Any of these that can receive an `expr.?` as their
boolean input would have the identical "0 is falsy" landmine. None of them
were touched in this change: the reported bug and its reproducing test are
specifically about `if`/`elif`/`while`/match-guard conditions, and blindly
editing ~10 more files without the ability to `cargo test` (see below) was
judged too high-risk for this session. Flagged here as a concrete, scoped
follow-up rather than silently left unaddressed.

## Regression tests added

- **`.spl` (SSpec, tree-walk interpreter via `bin/simple test`):**
  `test/03_system/interpreter/option_match_some_zero_regression_spec.spl`
  (new file, kept separate from `interpreter_regression_spec.spl` because
  that file has an unrelated, pre-existing failing example — "Bug 1d -
  expression form selects by presence and binds the payload" — that aborts
  the whole-file test run before later `describe` blocks execute). Covers
  `match`-based dispatch (already correct, kept as a guard) and `.?`-based
  `if`/`else` dispatch (the actual bug) for `Some(0)`, `Some(5)`, and `nil`.
- **Rust unit tests, `interpreter_control.rs`'s `exec_if_core_tests`
  module** (the exact call site that reproduced the bug — `if`/implicit-return
  position):
  - `exec_if_core_takes_then_branch_for_some_zero_via_exists_check` /
    `exec_if_core_takes_else_branch_for_none_via_exists_check`: the actual
    bug (plain `if x.?:` on `Some(0)`/`None`).
  - `exec_if_core_if_val_with_exists_check_binds_unwrapped_value` /
    `exec_if_core_if_val_with_exists_check_skips_empty_string`: guard the
    *unrelated* `if val` binding path against a repeat of the false-start
    mistake (these pass unmodified against the reverted `ExistsCheck`).
- **Native/cranelift `InterpCall` bridge (a separate, already-largely-fixed
  layer — see "Related" below):**
  `src/compiler_rust/compiler/src/runtime_bridge.rs`:
  `value_to_runtime_option_some_zero_payload_is_not_none` and
  `option_some_zero_payload_runtime_to_value_roundtrip` — closes a coverage
  gap where every existing S82 Option/Result test used a non-zero payload.

## Verification status (honest accounting)

- **`.spl` regression spec, run against the pre-fix seed binary:**
  reproduces the bug exactly as described. `bin/simple test
  test/03_system/interpreter/option_match_some_zero_regression_spec.spl` →
  `6 examples passed, 1 failed`: `.? truthiness check recognizes Some(0) as
  having a value` fails with `expected none to equal some:0`. This is the
  "add a reproducing test" mandate satisfied — RED, as expected, since the
  fix lives in Rust source that the currently-deployed seed binary does not
  yet contain.
- **Baseline regression check:** `test/03_system/feature/usage/
  exists_check_value_return_spec.spl` (18 examples covering `.?`'s
  value-return/nil-coalescing/if-val contract) passes 18/18 against the
  *pre-fix* binary — this is the check that caught the first (wrong)
  attempt and drove the correction to the current design.
- **Rust source fix:** written and manually reviewed (brace/paren-balance
  checked file-by-file after every edit, import paths and match-ergonomics
  style cross-checked against adjacent pre-existing code) but **NOT
  compiled or `cargo test`-verified this session.** `uptime` load average
  was 40–49 throughout this session (repo policy: only build if load < 15
  and > 30G free disk) — a `cargo build`/`cargo test` was never attempted,
  per that gate. This is a documented verification gap, not a silent skip.
- **Native/cranelift hybrid path:** a hand-built repro forcing
  `FallbackReason::TryOperator` (`InterpCall`) through
  `SIMPLE_NATIVE_BUILD_RUST=1 native-build --backend cranelift` on a
  `Some(0)`/`Some(5)`/`nil` `match` already passed correctly before any
  change here — S82 (landed earlier the same day, see
  `doc/08_tracking/bug/s68_cranelift_interpcall_boxed_result_generic_return_gap_2026-07-18.md`)
  already fixed discriminant-based Option/Result marshaling on that bridge.
  The two new `runtime_bridge.rs` tests exercise an already-fixed path and
  are expected to pass once compiled, but were likewise not
  `cargo test`-run this session (same load gate).

## Resume command (next session / once load is low)

```
cd /home/ormastes/dev/wt_n2
uptime   # confirm load < 15, and df -h . confirms > 30G free
cargo test -p simple-compiler --lib interpreter_control -- --test-threads=1
cargo test -p simple-compiler --lib runtime_bridge -- --test-threads=1
# rebuild + redeploy the seed binary per the repo's normal bootstrap flow, then:
bin/simple test test/03_system/interpreter/option_match_some_zero_regression_spec.spl
# expect: 7 examples, 0 failures (currently: 6 passed, 1 failed pre-fix)
bin/simple test test/03_system/feature/usage/exists_check_value_return_spec.spl
# expect: still 18 examples, 0 failures (this is the anti-regression check
# for the false start above -- if this regresses, `.?`'s value-return
# contract broke again)
rm -rf src/compiler_rust/target   # disk discipline cleanup when done
```

## Related / out of scope

- A separate, unrelated bug was found and is explicitly **not** fixed here:
  under plain `bin/simple run` (not the SSpec test runner), a `val opt: i64?
  = Some(5)` local variable's `.unwrap()` returned `40` (`5 << 3`) instead of
  `5` — a tag-boxing/JIT representation bug, distinct from the `.?`
  truthiness bug above (confirmed distinct: `match`-based unwrap of the same
  value via pattern binding was correct; only the `.unwrap()` method call on
  a locally-bound, explicitly `i64?`-annotated `val` showed the corruption,
  and it was NOT reproducible with `SIMPLE_BOOTSTRAP=1` set). Flagging for a
  separate bug report/lane; not chased further here to stay in scope.
- `doc/08_tracking/bug/s68_cranelift_interpcall_boxed_result_generic_return_gap_2026-07-18.md`
  — the native/cranelift `InterpCall` bridge bug (S78/S82), a different
  layer, already fixed same-day.
