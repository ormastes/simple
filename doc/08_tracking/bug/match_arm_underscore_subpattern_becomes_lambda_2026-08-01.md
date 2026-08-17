# `_` in a match-arm sub-pattern is eaten by the placeholder-lambda desugar

- **Date:** 2026-08-01
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Severity:** high (silent miscompile + loud false "unresolved name")
- **Parent:** `selfhost_names_with_no_import_path_masked_by_seed_flat_resolution_2026-08-01.md`
  (carve-out findings 2 `_`/`_1` and 7 "declared in the same file")
- **Sites:** `src/compiler/10.frontend/core/parser_stmts.spl`
  (`parse_match_arms_common`), `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`
  (`convert_flat_pattern`)

## Symptom

The self-host census reported `unresolved name: selected` for
`src/compiler/70.backend/backend/stage4_symbol_closure.spl` — a name **declared
in the very same file**, on the line that reports it:

```
pub fn stage4_select_requested_archive_indices(...) -> Result<[i64], text>:
    match stage4_resolve_requested_archive_owners(...):
        case Ok((selected, _)): Ok(selected)
        case Err(err): Err(err)
```

## Root cause (PROVED)

Match patterns are parsed with the **general expression parser**
(`parse_expr`), as `convert_flat_pattern`'s own docstring states. `parse_expr`
runs `transform_placeholder_lambda`, which rewrites any expression containing a
`_` placeholder into a lambda. So the tuple sub-pattern `(selected, _)` was
rewritten into an `EXPR_LAMBDA` (tag 26).

`convert_flat_pattern` has no `EXPR_LAMBDA` case. It fell through to the
trailing catch-all and returned `PatternKind.Wildcard`.

Evidence chain, all from `SIMPLE_DEBUG_MATCH_PAT=1` on the pure-Simple
front end driven by `parse_full_frontend` -> `HirLowering.lower_module`:

| source | trace | HIR errors |
|---|---|---|
| `case Ok((selected, _))` | `convert_flat_pattern DROPPED to wildcard: tag=26`, `payload-tuple n=1`, **no** `define binding` | 1 — `unresolved name: selected` |
| `case Ok((selected, rows))` (control) | `define binding: selected`, `define binding: rows` | 0 |
| `case Ok(pair)` (control) | `define binding: pair` | 0 |

Tag 26 is `EXPR_LAMBDA` (`src/compiler/10.frontend/core/_AstExpr/nodes.spl:40`).

## Two failures, one cause

1. **Loud:** the arm body's `selected` reference had no symbol, so HIR lowering
   emitted `unresolved name: selected` for a name declared in the same file.
2. **Silent:** the arm's pattern became an *unconditional* `Wildcard` — it
   matched every scrutinee, including `Err`. Nothing warns about this; it is
   exactly the class of degradation the `EXPR_TUPLE` and `EXPR_BINARY` cases
   already in `convert_flat_pattern` were added to stop.

This is **not** an import defect and must not be "fixed" with an import.

## Fix

`parse_match_arms_common` now suppresses the placeholder transform for the
duration of match-arm **pattern** parsing, on both arm paths (`case`-keyword
and caseless), restoring the caller's previous setting immediately afterwards.
`_` in pattern position is the wildcard pattern and never the lambda
shorthand. Guards and arm bodies are parsed **outside** the suppressed region,
so `case _: xs.map(f(_))` keeps working.

The suppression API (`set_placeholder_transform_suppressed`, returns the
previous value for nested scopes) already existed and is used the same way by
`string_interpolation_expand.spl`.

A level-gated probe (default off, `SIMPLE_DEBUG_MATCH_PAT=1`) was added to
`convert_flat_pattern`'s catch-all so any future pattern shape degraded to a
silent unconditional wildcard names its own expression tag.

## Regression spec

`test/01_unit/compiler/hir/match_arm_underscore_subpattern_spec.spl` — 5
examples: the verbatim `stage4_symbol_closure` shape, `_` in first position, a
bare tuple arm, a no-`_` control, and an arm-body placeholder-lambda control.

**Non-vacuity proved by sabotage.** Flipping only the `case`-arm suppression
to `set_placeholder_transform_suppressed(false)` turns exactly the two
`case Ok((x, _))` examples RED (`expected 1 to equal 0`) while the caseless-arm
example and the no-`_` control stay GREEN. Restoring the fix returns 5/5.

## Verification

Pure-Simple front end interpreted by `bin/simple_seed` (rebuilt 2026-08-01 from
`f93c9b2623`), harness `parse_full_frontend` -> `HirLowering.lower_module`,
asserting on `HirLowering.errors`. Not stage3/stage4 — stage4 aborts in phase 3
and its counts are early-abort artifacts.
