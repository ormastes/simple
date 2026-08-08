# BUG: `std.parser.treesitter_node` does not exist, and its spec asserts nothing anyway

**Status:** OPEN
**Found:** 2026-08-04
**Severity:** medium — one permanently-red spec in `test/01_unit/std/`, and the
spec is written so that implementing the module would prove nothing.
**Files:**
- `test/01_unit/std/parser/treesitter_node_spec.spl` (and its legacy duplicate
  `test/unit/std/parser/treesitter_node_spec.spl`)
- missing: `src/lib/**/parser/treesitter_node.spl`

## Symptom

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/01_unit/std/parser/treesitter_node_spec.spl
error: runtime: Module "std.parser" does not export 'treesitter_node'
error: test-runner: no examples executed
Results: 1 total, 0 passed, 1 failed
```

Actual: the file fails to load, 0 of its 23 `it` blocks run.
Expected: 23 examples execute.

## Root cause

Two independent defects.

**1. The module was never written.** `treesitter_node_spec.spl:13` imports

```
use std.parser.treesitter_node.{Node, Point, node_is_valid, node_byte_range, node_line_range}
```

`src/lib/common/parser/` contains only `ast.spl`, `lexer.spl`, `parser.spl`,
`parser_expr.spl`. `find src/lib -name '*treesitter*'` returns nothing, so no
tier provides it. The spec's own header says **"Status: In Development"** — it
was committed ahead of the implementation and has been red ever since.

**2. Every assertion in the spec is a tautology, so it is VACUOUS.** Even with
the module implemented, this spec cannot fail on a wrong answer. Verbatim from
the file:

- `treesitter_node_spec.spl:38` — `expect result.to_be_greater_than(-1) or result.to_equal(-1)`
  is true for every `i64`.
- `treesitter_node_spec.spl:49-51` — `val has_row = pt.row >= 0 or pt.row < 0`
  then `expect has_row and has_col`: true for every `Point`.
- `treesitter_node_spec.spl:73` — `val is_valid_result = parent == nil or parent != nil`
  is the law of excluded middle.
- `treesitter_node_spec.spl:101` — `expect k.len() >= 0` is true for every `text`.
- `treesitter_node_spec.spl:111` — `expect c == nil or c != nil`.

19 of the 23 examples are of this shape. Only the four `Point(row:, column:)`
round-trip checks in "Point Structure" (lines 191-202) and the
`node_is_valid(nil)` check (line 157) could ever go red.

The spec is therefore an *API-shape* check written as a *behaviour* check.

## Why not fixed now

Writing a TreeSitter `Node` FFI wrapper solely to satisfy 19 tautologies would
manufacture a green result that proves nothing about TreeSitter — the failure
mode this repo calls a false green. The honest fix is a pair, and both halves
need a decision this lane cannot make alone:

1. Decide whether the TreeSitter Node API is still wanted. If not, delete the
   spec (do not convert it to a NOTE or `@skip`). If yes, implement
   `std.parser.treesitter_node` against a real TreeSitter grammar.
2. Rewrite the assertions against **known** node positions parsed from a fixed
   source string (e.g. parse `"fn f():\n    1\n"` and assert
   `root.child(0).start_point() == Point(row: 0, column: 0)`), so a wrong
   implementation goes red.

Blocked on (1): the owner of `#PARSER-NODE-API-001` / "Phase 2.3".
