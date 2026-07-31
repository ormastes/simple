# COLL007 does not fire on the array-rebuild-to-pop idiom

**Date:** 2026-07-31
**Component:** `src/compiler/35.semantics/lint/collection_patterns.spl`
**Severity:** the rule is documented and registered but silently matches nothing

## Symptom

COLL007 is documented in the file header as

```
# COLL007: Array rebuild to pop last   arr = arr[0..len-1]      HIGH
```

and is wired into the CLI at `_LintMain/entry_and_fixes.spl`. It does not fire
on the canonical shape:

```
fn drain(ys: [i64]) -> [i64]:
    var arr = ys
    while arr.len() > 0:
        arr = arr[0..arr.len()-1]
    arr
```

Verified via `lint_cli_source(...)` — zero `COLL007` results. COLL001 fires
correctly on the sibling fixture in the same run, so the traversal reaches loop
bodies and the lint pipeline itself is healthy.

## Matcher

`is_array_rebuild_pop` (`collection_patterns.spl:535`) requires:

```
EXPR_ASSIGN
  left  = EXPR_IDENT
  right = EXPR_SLICE
            left = EXPR_IDENT with the same name
```

`EXPR_SLICE` is imported by `parser_expr.spl`, so the parser does emit that tag
somewhere. Not yet isolated which of these is false in practice:

- `arr[0..arr.len()-1]` parses as something other than `EXPR_SLICE` (e.g. an
  index node carrying a range operand), or
- the `while` loop body reaches a different traversal branch than the `for`
  body that COLL001 was confirmed on, or
- the slice's receiver is not a bare `EXPR_IDENT` after parsing.

Cheapest next probe: emit `expr_get_tag(value)` for the assign's RHS from the
matcher and lint the fixture above — one run distinguishes all three.

## Impact

Any codebase using the rebuild-to-pop idiom gets no warning. Because the rule
appears in the header table and in the docs, this reads as coverage that does
not exist — the failure mode the fail-open audit
(`doc/08_tracking/bug/lint_does_not_detect_syntax_errors_2026-07-28.md`) was
about.

## Related

The COLL007 `.pop()` rewrite in `collection_rewrite_for`
(`_LintMain/entry_and_fixes.spl`) is correct in isolation but currently
unreachable, since it is only consulted for a COLL007 warning. It stays in place
so the rule is fix-capable the moment it fires; the spec
`test/01_unit/compiler/lint/collection_easy_fix_spec.spl` documents the gap and
covers COLL001 only.

See also `doc/01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md` §2.
