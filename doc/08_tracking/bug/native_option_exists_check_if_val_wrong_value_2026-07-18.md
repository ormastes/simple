# native-build: `if val v = x.?:` binds `v` to the exists-check bool, not the unwrapped value (S70, fixed)

**Severity:** high (silent-wrong value, no diagnostic)
**Found:** 2026-07-18, bugfix campaign lane N6 (task id S70)
**Status:** fixed in the Rust seed's HIR lowering; guarded by 2 Rust unit
tests plus the pre-existing `native-smoke-matrix.shs` `option_nil_check` case
**Backend:** native-build (Rust seed HIR lowering — shared by every codegen
backend, LLVM and Cranelift alike; there is no separate per-backend adapter
for this logic)

## Symptom

`scripts/check/native-smoke-matrix.shs` case 14 (`option_nil_check`, "Option/
nil check (x.?)") native-builds successfully but the resulting binary returns
the **wrong value**: `rc got=84 want=7`. This is distinct from the
`native_try_op_on_option_silent_wrong_2026-07-14.md` bug (P4 lane): that bug
is about the `?` try-operator on `Option`/`Result` values; this bug is about
the `.?` exists-check operator used as an if-val binding subject. Both are
pre-existing, independent gaps in `main`.

Case source (`write_case_option` in the matrix script):

```
fn main() -> i64:
    val x: i64? = 7
    if val v = x.?:
        return v
    return 0
```

Expected `rc=7`. Confirmed with the stale deployed seed
(`/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple`,
`env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 native-build --entry ... -o
... --backend llvm --clean`): the built binary exits `84`. Running the same
source interpreted (`bin/simple run`, same stale seed) exits `7` (correct) —
confirming this is a native-lowering-only defect, not a language-semantics
ambiguity.

## Root cause

`x.?` parses as `Expr::ExistsCheck(x)` — a standalone presence-check operator
that normally yields a `bool` (`if x.?:` alone means "if x has a value").
`EXPR_EXISTS_CHECK`'s documented semantics (`src/compiler/10.frontend/core/_AstExpr/nodes.spl:63`)
are actually "returns `T?` — value if present, nil if absent", and the
tree-walking interpreter implements exactly that
(`src/compiler/10.frontend/core/interpreter/eval.spl:310-318`,
`eval_option_binding_value`): `.?` evaluates to the *unwrapped value* when
present, not to a boolean.

The parser's `if val v = EXPR:` desugaring
(`src/compiler/10.frontend/core/parser_stmts.spl:819-831`, `G19`) produces a
synthetic `val v = EXPR` binding (marked via `stmt_if_val_decl`/
`stmt_is_if_val_decl`) followed by a `v != nil` guard. When `EXPR` is `x.?`,
the *interpreter* path (`eval_stmt_val_decl`,
`src/compiler/10.frontend/core/interpreter/eval_stmts.spl:183-201`) already
gets the right value because `eval_expr` on `EXPR_EXISTS_CHECK` returns the
unwrapped value, and the interpreter path additionally applies
`eval_option_binding_value` on top (idempotent here) — so `v` binds to `7`.

The Rust seed's native HIR lowering (`Node::If`'s `let_pattern` branch,
`src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`, and the mirrored
`elif` branch in `lower_elif_chain`) lowered the `if val`/`elif val` subject
expression **verbatim**, i.e. `lower_expr(Expr::ExistsCheck(x))`. That lowers
`.?` as the standalone boolean presence-check (matching its *other*, bare-use
meaning), so the pattern-match subject became `bool`-typed (`true`), not
`x`'s own `i64?` value. `v`'s local slot ended up declared/consumed with a
type that disagreed with its actual (`i64?`) runtime shape, and `return v`
read back `84`. This is not a deliberate boxed-bool encoding: a control probe
(`fn main() -> i64: return true`, compiled+run the same way) exits `1`, not
`84`, ruling that specific hypothesis out. `84` is downstream garbage from
the subject/binding type mismatch, not a value with independent meaning; the
fix targets the type-mismatch root cause (the subject must be `x`'s own
type, not the `ExistsCheck` bool), so the exact provenance of `84` was not
pursued further once the type mismatch was identified and closed.

## Fix

`src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`: in the `Node::If`
`let_pattern` branch and the mirrored `elif` branch in `lower_elif_chain`,
unwrap one `ExistsCheck` layer off the condition/subject expression before
lowering it, matching the already-correct bare `if val v = x:` idiom:

```rust
let condition_expr = match &if_stmt.condition {
    Expr::ExistsCheck(inner) => inner.as_ref(),
    other => other,
};
let subject_hir = self.lower_expr(condition_expr, ctx)?;
```

This makes `if val v = x.?:` and `if val v = x:` lower identically (the
subject is always `x`'s own Option-typed value); the existing
`if_let_pattern_condition` machinery (`rt_is_some`/`!= nil` style guard) still
performs the actual presence test, so a bare `if x.?:` (no binding) is
unaffected — only the if-val/elif-val *binding* subject changes.

A second, unrelated bug bundled in the same fix pass
(`match_value_position_return` matrix case) is out of scope for this doc; see
commit `b1ee7fbaad1` for details.

## Verification

- Reproduced with the stale deployed seed: `option_nil_check` case ->
  `rc got=84 want=7` (build succeeds, wrong runtime value).
- Control probe ruling out "boxed bool" as the value's provenance: `fn main()
  -> i64: return true` (no `.?`/if-val involved), same stale seed, same
  `native-build --entry ... --backend llvm --clean` invocation, exits `1`.
- Interpreted control (same stale seed, `bin/simple run`): `rc=7` (correct),
  confirming the defect is native-lowering-only.
- 2 targeted Rust unit tests added
  (`src/compiler_rust/compiler/src/hir/lower/tests/control_flow_tests.rs`):
  - `test_if_val_exists_check_binds_unwrapped_option_value` — asserts the
    lowered if-val subject's type is not `TypeId::BOOL` and that `v`'s
    binding copies the unwrapped subject local, not the `ExistsCheck` result.
  - `test_value_position_match_arm_return_actually_returns` — covers the
    bundled `match_value_position_return` fix (see commit message).
  Per the landing commit message: both new tests pass with the fix, and a
  full `hir::lower::tests` A/B run (fix vs. reverted) showed the pre-existing
  7 unrelated failures unchanged and no new failures — the fix is isolated.
- End-to-end `NATIVE_SMOKE_CASES=option_nil_check
  sh scripts/check/native-smoke-matrix.shs` against a *freshly rebuilt* seed
  (i.e. one compiled from this fixed source, not the stale deployed seed) is
  the remaining strict-gate proof; a full `cargo build --release` of
  `src/compiler_rust` was not run in this pass because sibling parallel lanes
  had pushed 1-minute load average to 40-90 at verification time (repo
  discipline: build only when load&lt;15). The fix's correctness is
  established via the unit tests above, which exercise the exact HIR/MIR
  shapes the native codegen backends consume; re-run the matrix against the
  next rebuilt seed deploy to close the loop with a literal exit-code proof.

## Files changed (already landed, commit `b1ee7fbaad1`)

- `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs` — unwrap one
  `ExistsCheck` layer before lowering the if-val/elif-val subject (main `if`
  branch + `lower_elif_chain`).
- `src/compiler_rust/compiler/src/hir/lower/expr/control.rs` — the bundled
  `match_value_position_return` fix (return-terminator preservation for
  value-position match arms).
- `src/compiler_rust/compiler/src/hir/lower/tests/control_flow_tests.rs` —
  the 2 regression tests above.

## Reproducer

`scratch_n6/repro.spl` (lane-local scratch, not committed) mirrors the matrix
case verbatim for quick iteration:

```
fn main() -> i64:
    val x: i64? = 7
    if val v = x.?:
        return v
    return 0
```
