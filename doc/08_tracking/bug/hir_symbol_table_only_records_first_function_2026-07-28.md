# HIR symbol table records only the first top-level function in a module

- **Filed:** 2026-07-28
- **Severity:** medium — tooling-visible, not runtime-visible
- **Status:** open
- **Found via:** HS1 `hir-span-populate` lane, while writing a guard spec

## Symptom

After lowering a module containing two top-level functions,
`hir.symbols.lookup("second_fn")` returns nil. Only the first function's symbol
is present in the module's symbol table.

## What this does NOT affect

**Programs run correctly.** Verified directly:

```simple
fn first_fn() -> i64:  1
fn second_fn() -> i64: 2
fn main():
    print("first={first_fn()} second={second_fn()}")
```
`bin/simple run` → `first=1 second=2`.

Call resolution evidently goes through a path other than the module symbol
table, so codegen and execution are unaffected. This is why the gap has gone
unnoticed: nothing about running or testing normal code exposes it.

## Why it still matters

The symbol table is the query surface for tooling, and several planned lanes
read from it rather than from the call-resolution path:

- semantic `.md` → source links keyed by `SymbolId` (the `spl:fn@module.path~fingerprint`
  design), which must resolve every function in a module, not the first
- LSP go-to-definition / find-references / rename
- any refactoring tool that enumerates a module's declarations

A table that silently holds one entry per module will make those features look
implemented while returning wrong or empty results for everything after the
first declaration — the same silent-degradation shape as the span-zeroing and
`Dict.get()` defects filed today.

## Repro (tooling path)

Lower a two-function module via `parse_full_frontend` → `HirLowering.lower_module`,
then query `hir.symbols.lookup(...)` for each function name. The second returns
nil. HS1's guard spec worked around this by using two separate single-function
fixture modules; that workaround is noted in the spec rather than hidden.

## Fix direction

Audit where module-level function symbols are inserted during HIR lowering and
confirm the insert runs per declaration rather than once per module. Check for
the value-type accumulator trap while doing so: a `struct` threaded through a
loop or recursion silently discards inserts, which is exactly what made the
whole safety checker dead code
(`doc/08_tracking/bug/` — SafetyChecker struct→class, same session).

Guard: a spec that lowers a module with three functions and asserts all three
resolve by name.

## Related

- `doc/08_tracking/bug/hir_lowering_never_populates_function_spans_2026-07-28.md`
  — same lowering path, also silent, also invisible to hand-built-HIR specs.
