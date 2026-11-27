# Seed interpreter has no `array.sort_by`; every fix rule reaching it failed

**Status:** fix-implemented (call site removed), seed gap open
**Severity:** P2
**Found:** 2026-11-04 while routing `simple fix` through the shared source-edit core

## Symptom
Any `xs.sort_by(cmp)` on an array evaluates under the seed interpreter engine to
`semantic: method `sort_by` not found on type `array` (receiver value: [])` — on
empty and non-empty arrays, with a lambda or a named comparator, called directly
or through a fn value. `src/lib/nogc_sync_mut/src/aop.spl:212` already notes
"array.sort_by is unavailable in interpreter mode".

## Impact
`compiler.tools.fix.rules.impl_.lint_code._collect_indexed_call_replacements`
sorted its candidates with `indexed.sort_by(...)`, so
`check_unnamed_duplicate_typed_args_with_view` — run by every `simple fix`,
lint --fix and code-action request through the registry — raised on every unit
that reached that line. The baseline specs only stayed green because their
inputs never produced candidates.

## Repro
```
bin/simple.exe test <spec with:  var xs: [i64] = []; xs.sort_by(\a, b: a - b)>
```

## Fix
The rule now uses an explicit stable insertion sort (`lint_code.spl`). The seed
builtin itself is still missing in interpreter mode; `sort_by` is registered in
`interpreter_method/mod.rs` as a mutating method name only. Owner decision:
implement it in the seed or lint against `.sort_by(` in interpreter-run code.
