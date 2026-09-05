# Comparison chain `a < 0 or b > (c)` misparsed as generic arguments (self-hosted parser)

- **Date:** 2026-08-21
- **Status:** FIXED (`bf440c278b8`, "fix(parser): backtrack comparison chains from generic lookahead")
- **Scope:** self-hosted front end only. The Rust seed parser accepts the same source.
- **Severity:** blocked a stage1 `native-build` — the compiler could not parse its own source.

## Symptom

In a stage1 native-build (self-hosted front end),
`src/compiler/10.frontend/core/flat_pool_codec.spl:94`

```
if n < 0 or n > (self.lines.len() - self.pos):
```

failed with

```
[parser_error] line 94:25: const generic arguments are not supported: a numeric
literal such as Tensor<i64, 2> is not a type, and Simple has no const generic
parameters. ...
[parser_error_ctx] ... kind 140 text '('
```

The error names const generics, which the source does not use: the `<` is a
comparison operator.

## Root cause

`src/compiler/10.frontend/core/parser_expr.spl`, `try_skip_ident_generic_args()`
(the speculative "is this `ident <` the head of a generic-argument list?"
lookahead, ~line 770).

Its token walk accepted `TOK_INT_LIT`, `TOK_IDENT` and `TOK_COMMA` in any order
and any number, with no separator discipline. So for `n < 0 or n > (`:

1. `<` consumed, `depth = 1`.
2. `0` consumed as a const-generic argument candidate — `saw_const_arg = true`.
3. `or` … the walk kept going through the ident `n` (the `or` keyword itself
   broke out of the accept set only *after* the numeric had already poisoned
   the state in the real failing shape).
4. The final `>` closed `depth` to 0 and was followed by `(`, which is the
   CONFIRMATION condition — `ok = true`, so the speculation committed instead
   of backtracking.
5. Because `saw_const_arg` was set, the committed path raised the const-generic
   error (`parser_expr.spl:868`).

The confirmation heuristic (`>` followed by `.` or `(`) is right; what was
missing is that a numeric literal is only a plausible generic argument in a
list, and a list separates its elements.

## Rule implemented

Once a numeric literal has been consumed as a generic-argument candidate, only
a comma or a closing angle may follow. Any other token proves the `<` was a
comparison operator, so the walk breaks, `ok` stays false, and the whole
speculation is rolled back via `lex_snapshot_rollback` — the chain then parses
as ordinary boolean logic. This is a **fall back to comparison, not an error**.

`TOK_COMMA` clears the flag (a real list continues), and a nested `<` opening a
deeper level clears it too. Genuine const-generic attempts in TYPE position
still reach the confirmation branch and keep their precise error.

## Pre / post evidence

Spec: `test/01_unit/compiler/frontend/lt_gt_generic_disambiguation_spec.spl`
(byte-identical mirror at `test/unit/compiler/frontend/`), 9 examples.

| tree | result |
|---|---|
| `bf440c278b8~1` (pre-fix) | `7 passed, 2 failed` — both failures emit the const-generic error at the `<` |
| `2efa6de3a0f` (post-fix) | `9 passed, 0 failed` |

The two pre-fix failures are exactly the numeric-literal shapes:
`a < 0 or b > (c)` and the real `if n < 0 or n > (len - pos):`. The
non-numeric shapes (`a < b and c > d`, `x < y or z > f(q)`,
`while i < n and j > (k):`) already parsed correctly pre-fix — the `or`/`and`
keyword tokens are not in the accepted type-argument set, so those broke out of
the walk on their own. The defect class is specifically **numeric literal in a
comparison chain**.

Generic-instantiation examples that must and do keep parsing on both trees:
`Dict<text, i64>()`, `foo<i64>(x)`, `List<Pair<i64, text>>` in type position,
`Tensor<f64>` in type position.

## Neighbors (all green post-fix)

`multi_param_generic_return_type_spec` 2/2, `unknown_generic_return_type_spec`
1/1, `impl_head_type_params_spec` 5/5, `enum_payload_capture_spec` 7/7,
`type_alias_capture_spec` 4/4, `test/05_perf/frontend_interpolation_scaling_spec`
2/2.

## Other occurrences of the shape in the owned tree

Census over `src/compiler` and `src/lib` for `< … <numeric> … (or|and) … > (`
(the exact shape the confirmation heuristic could latch onto) — 4 hits, none
edited by this change, all parse on the fixed tree:

- `src/compiler/10.frontend/core/flat_pool_codec.spl:96` — the original
  casualty, currently carrying the `(n < 0) or (n > …)` workaround
  parenthesisation from `40cb59df025`. Now unnecessary; safe to un-parenthesise
  in a follow-up, deliberately left alone here so the fix commit changes no
  behaviour outside the parser.
- `src/compiler/50.mir/hwir/sequential.spl:148` —
  `if register.bit_width < 63 and register.reset_value > ((1 << …) - 1):`
  (was affected pre-fix, parses now).
- `src/lib/skia/feature/shaper/ot_layout_gpos_data.spl:303` —
  `if row_size <= 0 or item_count > (limit - rows) / row_size:`
  (was affected pre-fix, parses now).
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl:500`
  — already parenthesised (`(offset < 0) or …`), never affected.

The broad unrestricted shape (`< … digit … or/and … >` anywhere) is 1878 lines
across those two trees; the confirmation requirement (`>` immediately followed
by `(` or `.`) is what narrows it to the 4 above.
