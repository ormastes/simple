# HIR symbol table records only the first top-level function in a module

## Closed 2026-09-13 — confirmed not reproducible, by running the exact 2-fn repro

Verification engine: pinned copy of `src/compiler_rust/target/release/simple.exe`
(Simple Language v1.0.1-beta.1, 39,267,840 bytes, sha256 prefix `1b62a1a42755774fc087`,
built 2026-09-13 on this host). Windows 11 / Git Bash, default `run` lane
(seed JIT with interpreter fallback). This is the **Rust bootstrap seed**, not a
deployed pure-Simple self-hosted binary — the self-hosted lane remains unverified
on this host.

```spl
fn first_fn() -> i64:  1
fn second_fn() -> i64: 2
fn main():
    print("first={first_fn()} second={second_fn()}")
```

Both lanes print `first=1 second=2`. Both top-level functions resolve and
are callable, so the module symbol table is not dropping everything after
the first declaration.

This matches the 2026-07-29 update already in this entry, which traced
`declare_module_symbols` / `SymbolTable.define` and found the path
structurally correct, and which landed the guard spec
`test/01_unit/compiler/hir/hir_symbol_table_all_functions_spec.spl`. That
update stopped short of closing because the original cause was never
identified; the suspected cause — the documented-unreliable native
`Dict.get()` used at `hir_types.spl:286` — has since been resolved and
re-verified (see `.claude/rules/code-style.md`, "Native-Codegen Dict
Pitfalls ... RESOLVED 2026-08-09"), which supplies the missing explanation.
Evidence weighting, stated plainly: the run above exercises the **Rust seed's** resolver, not the pure-Simple `SymbolTable` in `hir_types.spl` where the suspected cause lived, so it is corroboration rather than proof. The closure rests on the 2026-07-29 structural trace plus the now-supplied cause; the fresh run only confirms nothing regressed. Anyone wanting direct pure-Simple evidence should run the guard spec `test/01_unit/compiler/hir/hir_symbol_table_all_functions_spec.spl`.

- **Filed:** 2026-07-28
- **Severity:** medium — tooling-visible, not runtime-visible
- **Status:** **not reproducible on HEAD (2026-07-29)** — guard spec added; likely a native `Dict.get()` flake, see below — CLOSED 2026-09-13 (see top section)
- **Found via:** HS1 `hir-span-populate` lane, while writing a guard spec

## 2026-07-29 update — not reproducible; guard landed

The SYM1 lane traced the full path and found it structurally correct on HEAD:
`declare_module_symbols` (`module_lowering.spl:1690-1712`) pre-declares every
top-level function in **module scope** with one `define` per function;
`SymbolTable.define` (`hir_types.spl:219-272`) only short-circuits
Class/Struct/Enum/Trait kinds — Function always inserts; `lower_function`
reuses the predeclared id via lookup. The bug-doc scenario was re-run three
ways (guard spec, 3-fn ad-hoc driver, exact 2-fn repro) across ~6 runs — every
function resolved to a distinct SymbolId each time.

**Most plausible original cause:** `SymbolTable.lookup` used
`scope.symbols.get(name)` (`hir_types.spl:286`) — native `Dict.get()` is
documented-unreliable (`dict_native_pitfalls.md`), and a pre-existing RED spec
(`symbol_table_dict_get_source_spec.spl`, another lane's, uncommitted) is
already driving `rt_dict_contains`+index-read hardening on exactly that line.
SYM1 deliberately did not touch `hir_types.spl` to avoid clobbering that lane.

**Guard now in tree:** `test/01_unit/compiler/hir/hir_symbol_table_all_functions_spec.spl`
parses real 3-function source through the full pipeline and asserts all three
resolve — 1/1 green. If the flake recurs, this spec is the tripwire.

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
