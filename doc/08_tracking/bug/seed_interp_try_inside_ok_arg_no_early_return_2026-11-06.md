# Seed interpreter: `?` inside `Ok(...)` in a method does not return the Err

- **Found:** 2026-11-06 during the W3 node-pool pilot (data plan W3).
- **Repro**, in a class `impl` running on the seed interpreter:
  ```simple
  fn row(node: i64) -> Result<Row, text>:
      if not self.rows.contains_key(node):
          return Err("no row")
      Ok(self.rows[node])

  fn op(node: i64) -> Result<i64, text>:
      Ok(self.row(node)?.op)        # row(...) is Err here
  ```
  `op(999999).is_err()` is `false`: the `?` inside the `Ok(...)` argument did not return the `Err`.
- **Expected:** `?` propagates the `Err` out of `op`, wherever it appears in the expression.
- **Workaround in tree:** `src/compiler/10.frontend/node_pool_pilot.spl` uses an explicit `match`.
- **Status:** the pure-Simple interpreter and the JIT are not measured yet.

## Resolution 2026-11-08 — premise re-scoped (grammar, not a dropped return)

Status: fix-implemented-verification-pending.

`Ok(self.row(node)?.op)` never contains a `?` operator: the lexer reads `?.`
as ONE safe-navigation token (seed `parser/src/lexer/mod.rs` `QuestionDot`,
pure-Simple `src/compiler/10.frontend/core/lexer_types.spl`), so the
expression is `Ok(self.row(node) ?. op)`. Safe navigation on an `Err`
receiver yields `nil`, giving `Ok(nil)` — the documented `?.` semantics
(`doc/07_guide/quick_reference/syntax_quick_reference.md` "Safe Navigation").
Measured on a seed built from `origin/release/1.0.0` (interpreter and JIT
agree): `Ok((self.row(n)?).op)` and `Ok(self.row(n)?)` both propagate the Err.
Use `(expr?).field` for try-then-field; the `match` workaround in
`node_pool_pilot.spl` can become `(self.row(node)?).op`.

Regression/prevention tests:
`src/compiler_rust/compiler/tests/try_operator_in_ok_arg_interpreter.rs`
(4 cases: free-fn and method `Ok(f()?)` propagate, `(f()?).field` reads the
payload, `f()?.field` stays safe navigation) — 4 passed.
