id: if_val_some_constructor_pattern_parser_regression_2026-07-02
status: FIXED (source; deployed binary pending bootstrap — stage2 blocked by unrelated rt_cranelift_new_aot_module extern error)
fixed: 2026-07-02
fix: src/compiler/10.frontend/core/parser_stmts.spl parse_if_stmt — binding
  position now parsed with parse_or (below assignment precedence); a
  constructor pattern (EXPR_CALL) desugars to the equivalent match stmt
  (pattern arm + `_` else arm) via arm_new_with_binding_and_rationale /
  stmt_match_stmt, identical to hand-written match. Plain ident keeps the
  nil-check desugar. Root cause: never implemented in the pure-Simple
  parser (G19 only accepted parser_expect(IDENT)); the Rust seed parser
  (compiler_rust/parser/src/stmt_parsing/control_flow.rs,
  parse_optional_let_pattern) always supported it, so call sites accumulated.
  UPDATE 2026-07-02: the EXPRESSION-position gap (`val r = if val Some(x) = o:
  a else: b`, plain-ident form too -- sites: src/lib/common/js/engine/jit.spl:112,
  src/compiler/80.driver/main.spl:127) is FIXED -- parse_if_expr in
  src/compiler/10.frontend/core/parser_stmts.spl now mirrors parse_if_stmt's
  G19 desugar, expression-flavored: plain-ident binding desugars to a block
  value (bind + if-expr on `!= nil`), and a constructor pattern desugars to
  an expr-level match (expr_match_expr, evaluated by eval_match_expr, which
  was already wired into the interpreter but never reached by any parser
  path before) instead of a match statement, so both branches stay values.
  Verified via a core_frontend_parse_reset driver run through both
  `bin/simple run` and `bin/simple check` (both dynamically load and execute
  the current on-disk pure-Simple parser source, confirmed by A/B: reverting
  the source reproduces the exact `expected =, got (` / `unexpected token in
  expression: :` errors, restoring it fixes them) on repros matching the two
  wild sites above, plus an elif-val chain in expression position. Regression:
  5 existing parser specs still pass (1 pre-existing unrelated failure in
  pipe_operator_spec, confirmed present on reverted source too).
severity: high
discovered: 2026-07-02
discovered_by: bin/simple check on src/lib/nogc_async_mut_noalloc/path/baremetal_path.spl
related: src/lib/nogc_async_mut_noalloc/path/baremetal_path.spl
related: src/lib/nogc_async_mut_noalloc/replay/bm_checkpoint.spl
related: src/compiler/00.common/effects.spl
related: src/compiler/70.backend/backend/codegen_errors.spl
---

# `if val Some(x) = expr:` constructor-pattern binding fails to parse (self-hosted `bin/simple check`)

## Summary

The pattern-binding form `if val Some(<name>) = <expr>:` — used throughout
the codebase to conditionally unwrap an `Option<T>` — currently fails to
parse with the self-hosted `bin/simple` binary, everywhere it is used,
not just in the two sites originally reported.

```
[parser_error] line 52:16: expected =, got ( '('
```

The column points at the `(` right after `Some`, i.e. the parser accepts
`if val <ident>` (plain identifier binding) but does not accept
`if val <Ctor>(<ident>)` (constructor-pattern binding) in this build.

## Repro

```
fn bm_path_dirname(path: text) -> text:
    ...
    val last_sep = clean.rfind("/")
    if val Some(sep_idx) = last_sep:
        ...
    else:
        "."
```

```
$ timeout 180 bin/simple check src/lib/nogc_async_mut_noalloc/path/baremetal_path.spl
[parser_error] line 52:16: expected =, got ( '('
[parser_error] line 68:16: expected =, got ( '('
```

## Not Isolated To This File

Confirmed the same failure on every file using this syntax that was spot
checked, including files far from the reported ones:

- `src/lib/nogc_async_mut_noalloc/replay/bm_checkpoint.spl:49` —
  `[parser_error] line 49:24: expected =, got ( '('`
- `src/compiler/00.common/effects.spl:115,119` —
  `[parser_error] line 115:20: ...` / `line 119:20: ...`
- `src/compiler/70.backend/backend/codegen_errors.spl:135,142,146` —
  `[parser_error] line 135:20: ...` / `142:20` / `146:20`

A repo-wide `grep -rn "if val Some(" src/` turns up dozens of call sites
across the compiler and stdlib; every one spot-checked with
`bin/simple check` on the current self-hosted binary reproduces the same
`expected =, got (` error. This means the short/canonical `if val Some(x) = expr:`
sugar is currently broken build-wide, not specific to the noalloc tier or
to `baremetal_path.spl`.

## Working Alternative (used as the workaround)

The equivalent `match` form parses cleanly and is already used elsewhere
in the same noalloc tier, e.g.
`src/lib/nogc_async_mut_noalloc/qemu/debug_boot_runner.spl:181-186`:

```
match last_sep:
    Some(sep_idx):
        ...
    nil:
        "."
```

`bin/simple check` on `debug_boot_runner.spl` and on the rewritten
`baremetal_path.spl` (see below) both report zero parser errors.

## Applied Workaround

`src/lib/nogc_async_mut_noalloc/path/baremetal_path.spl` — converted the
two `if val Some(...) = ...: / else:` sites (`bm_path_dirname` line ~52,
`bm_path_extension` line ~68) to the equivalent `match ...: Some(...): / nil:`
form. Verified `bin/simple check` on the file now passes with zero errors.

## Suggested Fix

Investigate the self-hosted parser's `if val <pattern> = <expr>:` grammar
rule (parser front-end, statement/if-let handling) for why a constructor
pattern (`Some(x)`, presumably also `Ok(x)`, `Err(x)`, other single-field
tuple variants) is not accepted as `<pattern>` after `if val`, while a bare
identifier is. Given the number of existing call sites relying on this
sugar, this should be treated as a parser regression rather than a
docs/style issue — either restore constructor-pattern support in `if val`,
or do a repo-wide migration to `match` if the sugar is being intentionally
removed.

## Citations

- `src/lib/nogc_async_mut_noalloc/path/baremetal_path.spl:52,68` (original failure, now fixed)
- `src/lib/nogc_async_mut_noalloc/replay/bm_checkpoint.spl:49` (same failure, unfixed — out of scope for this task)
- `src/compiler/00.common/effects.spl:115,119` (same failure, unfixed — out of scope for this task)
- `src/compiler/70.backend/backend/codegen_errors.spl:135,142,146` (same failure, unfixed — out of scope for this task)
- `src/lib/nogc_async_mut_noalloc/qemu/debug_boot_runner.spl:181-215` (working `match Some(...): / nil:` form used as the model for the workaround)
