# Bug: `unwrap or_return: <default>` never parses/stores the default value; propagates like `?` instead

- **Date:** 2026-07-20
- **Status:** RESOLVED (verified 2026-11-25 — see note below; fix direction (a)
  was implemented)
- **Area:** `src/compiler_rust/parser/src/expressions/postfix.rs` (`TokenKind::OrReturn` arm),
  `src/compiler_rust/compiler/src/interpreter/expr.rs` (`Expr::UnwrapOrReturn`), deployed seed
  at `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

`test/feature/usage/safe_unwrap_operators_spec.spl`, context "unwrap or_return: with
early return", 3 of 4 examples fail:

```
✗ returns default when None
  expected Option::None to equal 0
✗ works with Result
  expected 82 to equal 84
✗ returns default for Result Err
  expected Result::Err(parse error) to equal -1
```

The feature's own docstring (and the mirrored `doc/02_requirements/language/operators/safe_unwrap_operators.md`)
describes `result unwrap or_return: default_on_err` as "returns from the function
with a **default value** on error" — i.e. `opt unwrap or_return: 0` should behave
like `opt unwrap or: 0` except performing an early `return` instead of continuing
the current expression.

## Root cause (confirmed by source read)

Comparing the three sibling arms in `postfix.rs`'s `TokenKind::Unwrap` match
(`OrColon`, `Else`, `OrReturn`):

```rust
TokenKind::OrColon => {
    self.advance();
    let default = self.parse_expression()?;
    expr = Expr::UnwrapOr { expr: Box::new(expr), default: Box::new(default) };
}
TokenKind::Else => {
    self.advance();
    self.expect(&TokenKind::Colon)?;
    let fallback_fn = self.parse_expression()?;
    expr = Expr::UnwrapElse { expr: Box::new(expr), fallback_fn: Box::new(fallback_fn) };
}
TokenKind::OrReturn => {
    self.advance();
    expr = Expr::UnwrapOrReturn(Box::new(expr));   // <-- no default parsed at all
}
```

`OrColon` and `Else` both parse and store a trailing expression as the
fallback/default. `OrReturn` does not — `Expr::UnwrapOrReturn` only wraps the
receiver, with no field for a default value. The interpreter
(`interpreter/expr.rs`, `Expr::UnwrapOrReturn(inner)` arm) matches this: on
None/Err it does `Err(CompileError::TryError(Box::new(val)))`, i.e. it
propagates the **receiver itself** as an early return — identical to the `?`
operator, not "return a caller-supplied default."

Because the parser never consumes the trailing `0`/`-1` after `or_return:` as
part of the `UnwrapOrReturn` node, but also raises no parse error, the tokens
are evidently absorbed elsewhere in a way that corrupts adjacent evaluation —
observed secondary symptom: even the *happy-path* Result case ("works with
Result", `Ok(42)`, expected `84` = `42 * 2`) returns `82` instead, an
unexplained-by-us discrepancy consistent with the trailing default expression
tokens not being safely discardable garbage.

## Minimal repro

```simple
fn get_default_or_early() -> i64:
    val opt: Option<i64> = None
    val value = opt unwrap or_return:
    value + 1

fn main():
    print(get_default_or_early().to_text())
```

`bin/release/x86_64-unknown-linux-gnu/simple run <repro>.spl`:
```
error: semantic: method `to_text` not found on type `enum` (receiver value: Option::None)
```

`get_default_or_early()` returns `Option::None` directly (propagated, matching
`?` semantics) rather than any default — confirmed independent of the trailing
default-value syntax question, since this repro omits the default entirely and
the function's declared return type (`i64`) does not match what's actually
returned (`Option::None`), which the interpreter does not type-check on this
path.

## Fix direction (not applied — parser + interpreter change, needs rebuild)

Either (a) implement the documented default-value semantics: `postfix.rs`'s
`OrReturn` arm should parse a trailing expression like its `OrColon`/`Else`
siblings and store it on a new `Expr::UnwrapOrReturn { expr, default }` variant;
the interpreter should evaluate and return `default` (not propagate the
receiver) when the function's control flow needs an early return path that
doesn't unwind further, or (b) if `or_return:` is intentionally designed to be
parameterless (matching `?`), fix the docs (feature docstring +
`doc/02_requirements/language/operators/safe_unwrap_operators.md`) and update
the spec's own assertions, and make the parser reject a trailing value after
`or_return:` instead of silently absorbing it.

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/safe_unwrap_operators_spec.spl --no-session-daemon
```
Not checked against the pure-Simple self-hosted compiler (`src/compiler/`) or a
compiled/native path — only the Rust seed's tree-walking interpreter (the path
`bin/simple test` exercises on this host) was probed.

## Verification 2026-11-25 — fixed at release/1.0.0 HEAD

Fix direction (a) was implemented: `Expr::UnwrapOrReturn` is now a struct
variant carrying the default (`{ expr, default }`,
`src/compiler_rust/parser/src/ast/nodes/core.rs:801`), the parser's `OrReturn`
arm parses and stores the trailing default expression like its
`OrColon`/`Else` siblings (`src/compiler_rust/parser/src/expressions/postfix.rs:636,696`),
and the interpreter evaluates and early-returns the DEFAULT on None/Err
instead of propagating the receiver
(`src/compiler_rust/compiler/src/interpreter/expr.rs:557-568`).

All four "unwrap or_return: with early return" examples — including the three
that failed when this was filed ("returns default when None", "works with
Result" (84, not 82), "returns default for Result Err") — now pass:

```
SIMPLE_LIB=src bin/simple.exe run test/feature/usage/safe_unwrap_operators_spec.spl --mode=interpreter
=> 23 examples, 3 failures; all 4 or_return cases green
```

Run on a Windows worktree at release/1.0.0 HEAD (`f3fb8f24dc9`) with the
tracked seed `bin/simple.exe` (38,403,072 bytes, v1.0.0-rc.1); the `test`
subcommand is unusable at HEAD (pinned seed rejects
`@representation_boundary`), so the `run` harness was used.

**Adjacent observation (NOT this bug, not fixed here):** the same spec run
shows 3 failures in the separate "unwrap else: with lazy evaluation" context
("calls closure only when Option is None", "evaluates closure for Result
Err", "closure can perform side effects" — all `expected false to equal true`
/ `expected 0 to equal 100`). The pattern is uniform: side effects performed
inside an `unwrap else:` fallback closure are not visible to the enclosing
scope under the seed interpreter — a closure-capture/Else-lane issue
independent of `or_return:`. Filed as
`doc/08_tracking/bug/unwrap_else_closure_side_effects_invisible_2026-11-25.md`.
