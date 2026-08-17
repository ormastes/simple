# JS subset parser: ternary dropped, statements after `}` never evaluated

- Status: DEFECT 1 FIXED 2026-08-17; DEFECT 2 was already fixed.
- Status re-verified 2026-08-17 by source inspection (triage shard 02).

## 2026-08-17 verification and fix

**Defect 2 (statement after `}`) was ALREADY FIXED in-tree** —
`js_parse_program_subset` (`parser.spl:16-34`) peels each leading
brace-terminated construct off a `;`-split part via
`_js_parser_leading_construct_end`. Measured: `function f(x) ...` followed by
`f(3)` returns 4.

**Defect 1 (ternary dropped) was LIVE.** `grep -c Ternary` on
`git show HEAD:src/lib/nogc_sync_mut/js/engine/parser.spl` returned **0**,
while `JsExpression.Ternary` exists in `types/ast_types.spl:45` and is
evaluated at `engine/interpreter_eval.spl:116` — an AST node the parser could
never produce.

Measured with the HEAD parser vs the patched parser (same probe, `bin/simple run`):

| source | before | after |
|---|---|---|
| `var x = 5 < 2 ? 1 : 2; x` | `false` | `2` |
| `var x = 2 < 5 ? 1 : 2; x` | `true` | `1` |
| `0 ? 1 : 0 ? 2 : 3` | `0` | `3` |
| `1 ? 0 ? 7 : 8 : 9` | `1` | `8` |
| `null ?? 5` | `5` | `5` |
| `1 > 0 ? 'a?b:c' : 'z'` | `true` | `a?b:c` |

Fix: a conditional production in `_js_parser_expression`, placed between the
assignment and unary/binary productions (correct JS precedence), plus
`_js_parser_find_ternary_question` / `_js_parser_find_ternary_colon`, which are
quote- and depth-aware and skip `??` and `?.`; nested ternaries in the
consequent consume their own colon via a pending counter.

Post-fix spec runs (verbatim):

```
test/01_unit/lib/js/ternary_expression_spec.spl
Results: 7 total, 7 passed, 0 failed
test/01_unit/lib/js/conditional_expression_class_spec.spl
Results: 12 total, 12 passed, 0 failed
```

The pre-fix RED is the `bin/simple run` A/B table above (HEAD parser swapped in
and restored), not a spec run: holding the shared working tree at the HEAD
parser for the ~50 minutes a spec run currently takes under this host's load
would have corrupted other lanes' concurrent runs.

Specs: `test/01_unit/lib/js/ternary_expression_spec.spl` (reproducing) and
`test/01_unit/lib/js/conditional_expression_class_spec.spl` (class detection:
precedence against every neighbouring production, nesting, call args, array
literals, parens, `??`/`?.`, `?`/`:` inside string literals).
- **Date:** 2026-07-11
- **Area:** lib / js engine (`src/lib/nogc_sync_mut/js/engine/parser.spl`)
- **Severity:** P2 (silently wrong values on extremely common JS forms)

## Two defects (no crash since the NaN fix `7f6f44af`; both yield WRONG results)

1. **Conditional (ternary) expressions are dropped.**
   `var x = 5 < 2 ? 1 : 2; x` evaluates to `false` — `_js_parser_expression`
   has no `?:` case, so the expression parses as the bare `<` comparison and
   the `? 1 : 2` tail is discarded. Fix: find top-level `?` (excluding `?.`
   and `??`), split at the matching top-level `:` (mind nested ternaries and
   object literals), emit a conditional expression node.

2. **A statement following `}` without a semicolon never runs.**
   `function fib(n){ return n < 2 ? n : fib(n-1)+fib(n-2) } fib(3)` returns
   the function object — `js_parse_program_subset` splits statements only on
   top-level `;`, so everything after the function body's closing `}` stays
   glued to the declaration and is dropped by the declaration parser.
   Real pages end function declarations with `}` + newline constantly.
   Fix: after a top-level `}` that closes a function/class/block statement,
   also treat a following token as a new statement (or split on top-level
   `}` boundaries followed by non-operator tokens).

## Repros

`tools/pixel_compare/divzero_bisect.spl` (session probe; WHICH=1/3/4) or:
```
rt.eval("var x = 5 < 2 ? 1 : 2; x")                 # false, want 2
rt.eval("function f(x){ return x } f(3)")            # [function], want 3
```

## Also noted (perf)

Google inline script idx1 (37KB) takes 200-550s to interpret through the
subset parser — superlinear; needs its own profile pass once correctness
lands.
