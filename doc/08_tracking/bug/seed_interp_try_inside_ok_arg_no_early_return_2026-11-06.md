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
