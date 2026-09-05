# Pipe-lambda typed parameters rejected by parser (fixed in seed source, pending rebuild)

- **Status (2026-08-17): RESOLVED — the pending rebuild has happened and the repro passes.**

  Binary identity:
  ```
  readlink -f bin/simple
  /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
  stat -c '%s %y' -> 59537240 2026-08-17 12:58:51.339525019 +0000
  ```
  Repro (`scratchpad/r1.spl`):
  ```simple
  fn main():
      val f = |x: i64| x + 1
      print("{f(5)}\n")
  ```
  ```
  $ bin/simple run r1.spl
  [INFO] JIT compilation failed, falling back to interpreter: ... lambda/closure ABI ...
  6
  ```
  Parses and evaluates correctly — the `Unexpected token: expected Pipe, found
  Colon` error is gone. (The JIT-closure-ABI deferral message is a separate,
  pre-existing known limitation, not this defect.)

Date: 2026-08-07

## Symptom

`val f = |x: i64| x + 1; print("{f(5)}\n")` fails to parse:

```
error: compile failed: parse: in "...": Unexpected token: expected Pipe, found Colon
```

Untyped pipe-lambdas (`|x| x + 1`) parse fine. Multi-param typed form
(`|x: i64, y: i64| x + y`) fails the same way.

## Repro confirmation

Both `bin/simple run` (JIT, falls back to interpreter on failure) and
`SIMPLE_EXECUTION_MODE=interpret bin/simple run` produce the identical parse
error -- not engine-specific, since parsing is a shared frontend stage before
either engine runs.

`bin/simple` is currently the unrebuilt Rust seed (see
`.claude/rules/bootstrap.md` "KNOWN BLOCKER" -- stage 3 self-host is blocked),
so the seed parser (`src/compiler_rust/parser`) is the only live frontend;
`src/compiler` (pure-Simple) has no independent lambda-parameter parsing code
of its own to check.

## Root cause

- `src/compiler_rust/parser/src/expressions/postfix.rs`,
  `parse_pipe_lambda_params` (pipe lambda `|x|`, `|x, y|` form): pushed every
  `LambdaParam { name, ty: None }` unconditionally for the first parameter,
  never checking for a following `: Type`.
- `src/compiler_rust/parser/src/expressions/helpers.rs`,
  `parse_remaining_lambda_params` (parameters after the first comma, shared by
  both pipe-lambda and backslash-lambda forms): same unconditional
  `ty: None`.
- The `LambdaParam` AST node (`src/compiler_rust/parser/src/ast/nodes/core.rs:889-892`)
  already has `ty: Option<Type>` -- only the parser never populated it for
  this syntax. `fn` parameter-list parsing already supports `name: Type`; the
  lambda param parser simply never mirrored it.

## Fix

Added an optional `: <Type>` parse after each pipe-lambda parameter name in
both functions above, mirroring `fn` parameter parsing. `parse_remaining_lambda_params`
is shared by both the pipe-lambda (`|x, y|`) and backslash-lambda (`\x, y:
body`) forms, so it now takes an explicit `allow_types: bool` parameter:
`true` from `parse_pipe_lambda_params`, `false` from `parse_lambda_params`
(the backslash form). The backslash form was deliberately left disabled: it
already uses a bare trailing `:` to end the parameter list and start the
body, so `\x, y: x + y` would otherwise try to parse the body `x + y` as a
type for `y`. A first version of this fix threaded no such flag and would
have broken exactly that case; caught in review before landing and fixed by
adding the flag plus a regression test (`backslash_lambda_multi_param_untyped_still_parses`).

The type is parsed with `parse_single_type()`, not `parse_type()`:
`parse_type()` continues consuming a following `|` to build a union type
(`src/compiler_rust/parser/src/parser_types.rs:36-43`), which would swallow
the pipe-lambda's own closing `|` (e.g. `|x: i64| x + 1` would misparse `i64`
as the start of a union type continuing into `x`). `parse_single_type()` does
not have this problem.

Scope deliberately limited to the `|...|` pipe-lambda syntax.

This is a small, contained, parser-only grammar addition -- `LambdaParam.ty:
Option<Type>` already existed on the AST node and already has a real
downstream reader: `src/compiler_rust/compiler/src/hir/lower/expr/control.rs`
(lowering a `Lambda` expr) does `let ty = if let Some(ref t) = p.ty {
self.resolve_type(t)... } else { TypeId::I64 }` per parameter -- i.e. it
already resolves a declared param type when present and only defaults to I64
when absent. Before this fix nothing ever produced `Some(Type)` for a
`LambdaParam`, so this path always took the I64-default branch; after the
fix, a typed pipe-lambda param now takes the `resolve_type` branch, same as
`fn` params. This is the JIT/HIR (`bin/simple run`) lane; the interpreter
lane that `bin/simple test` hard-defaults to
(`src/compiler_rust/compiler/src/interpreter/expr/control.rs:32`) destructures
`LambdaParam { name, .. }` and ignores `ty` entirely, so
`test/01_unit/language/typed_pipe_lambda_param_spec.spl` passing after
rebuild depends only on the parser accepting the syntax and binding `name`
correctly, independent of `resolve_type`. No codegen/ABI change was needed
for either lane -- the reader already existed,
only the parser producer was missing -- so it was patched directly in the
seed (`src/compiler_rust/parser/**`) per the repo's "fix .spl not Rust"
exception for small, safe, contained parser additions.

## Files changed

- `src/compiler_rust/parser/src/expressions/postfix.rs` (`parse_pipe_lambda_params`, `parse_lambda_params` call site)
- `src/compiler_rust/parser/src/expressions/helpers.rs` (`parse_remaining_lambda_params`, now takes `allow_types: bool`)
- `src/compiler_rust/parser/src/pipe_lambda_typed_param_test.rs` (new, 4 in-crate parser tests)
- `src/compiler_rust/parser/src/lib.rs` (registers the new test module)
- `test/01_unit/language/typed_pipe_lambda_param_spec.spl` (new `.spl` regression spec)

## Verification status

- `cargo test -p simple-parser --lib` (in `src/compiler_rust`): **276 passed,
  0 failed** -- full existing parser test suite is unaffected.
- `cargo test -p simple-parser pipe_lambda_typed_param` (in-crate, exercises
  the actual parser behavior, not just type-checking): **4 passed, 0
  failed** -- single typed param, multi typed params, untyped params
  (no-regression), and the backslash-lambda multi-param
  no-per-param-type-leak guard.
- **Not yet live in the deployed binary**: `bin/simple` (the deployed seed)
  does not contain this change. No bootstrap/seed rebuild was run for this
  fix (out of scope for the task that produced it, and
  `.claude/rules/bootstrap.md` warns against hand-rolled `cargo build
  --release` redeploys of `bin/release/**`).
  `test/01_unit/language/typed_pipe_lambda_param_spec.spl` is currently RED
  under `bin/simple test` (`Results: 1 total, 0 passed, 1 failed`, same
  `Unexpected token: expected Pipe, found Colon` parse error) because the
  deployed binary predates the fix. **Unblock condition:** next seed rebuild
  or full bootstrap that picks up `src/compiler_rust/parser/**` -- re-run the
  spec after that and confirm `Results: 3 total, 3 passed, 0 failed`.
- Summary: **parser-level verified (in-crate tests green); deployment
  pending-rebuild** (the `.spl` regression spec stays RED, correctly, until
  then).
