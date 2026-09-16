# Bug: `unwrap or_return: <default>` never parses/stores the default value; propagates like `?` instead

- **Date:** 2026-07-20
- **Status:** open (found triaging `test/feature/usage/safe_unwrap_operators_spec.spl`)
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
