# JS subset parser: ternary dropped, statements after `}` never evaluated

- **Status:** Open
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
