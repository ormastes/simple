# JS subset parser: ternary dropped, statements after `}` never evaluated

- **Status:** Closed (2026-11-25) — both defects fixed in source and verified not reproducible; see the dated verification note at the bottom.
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

## Verification 2026-11-25 (p2w3-al lane, Windows) — both defects FIXED, closing

Runtime: committed `bin/simple.exe` (Rust bootstrap seed v1.0.0-rc.1,
38,403,072 bytes), `SIMPLE_LIB=src ... run`, Windows Git Bash, worktree at
release/1.0.0 @ 1457ddaa176.

**Defect 1 (ternary dropped):** fixed by 98d1ae9c64a (2026-08-17, "parser never
emitted Ternary"), which added `_js_parser_find_ternary_question` /
`_js_parser_find_ternary_colon` (with `??`/`?.` guards) to
`src/lib/nogc_sync_mut/js/engine/parser.spl`. Regression specs exist:
`test/01_unit/lib/js/ternary_expression_spec.spl`,
`test/01_unit/lib/js/conditional_expression_class_spec.spl`,
`test/01_unit/lib/js/ternary_rhs_precedence_spec.spl`.

**Defect 2 (statement after `}` never runs):** `js_parse_program_subset`
(parser.spl:13) now peels each leading brace-terminated construct off a
`;`-split part via `_js_parser_leading_construct_end` before parsing the
remainder — exactly the fix this doc prescribed.

**Live re-verification** (the named specs cannot run here: release/1.0.0 HEAD
is source/binary inconsistent — the pinned seed rejects
`@representation_boundary`, so `bin/simple.exe test` fails repo-wide). Instead
a standalone probe drove `JsRuntime.eval` with JS-side self-scoring (`throw` on
a wrong value, so only Ok/Err crosses the module boundary). All four checks
PASS on this binary:

```
ternary=PASS               # var x = 5 < 2 ? 1 : 2  -> x == 2
ternary_nested=PASS        # 1 < 2 ? (3 > 2 ? 10 : 20) : 30 -> 10
funcall_after_brace=PASS   # function f(x){ return x } var r = f(3) -> r == 3
fib=PASS                   # function fib(n){...} fib(3) -> 2
```

The 200-550s inline-script perf note above is a separate, unverified perf
concern and is not closed by this note.
