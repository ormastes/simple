# "Common mistake" detector misreads `dict[Ctor(...)] = v` as `List[T]` generics (2026-08-25)

**Status:** OPEN. **Blocks:** `bin/simple test` on clean `origin/main` content (42 sites).

## Symptom
```
error: Common mistake detected: See error message for details
 73 |                 recovered_constants[SymbolId(id: const_idx)] = hir_const
Use <> instead of [] for generics
Old:     List[T]      New:     List<T>
```
`recovered_constants[SymbolId(id: const_idx)]` is a **dict index assignment whose key is a struct
literal**, not a generic type application. The heuristic fires on the shape
`identifier[Identifier(...)]` and cannot tell the two apart, so it rejects correct code with advice
that does not apply.

Same class as `namespace` being rejected as a variable name (fixed in this change by renaming the
variable at `src/lib/nogc_sync_mut/test_runner/test_runner_mcdc_report.spl:331`) and as the
already-fixed contextual-keyword family (`examples`, `and_then`, `move`, `admit`/`assume`).

## Scale
42 `Common mistake detected` sites in one `bin/simple test` run over clean `origin/main`, the first
in `src/compiler/20.hir/hir_lowering/_Items/module_build*.spl:73,81`.

## Fix direction
Only treat `X[Y]` as a generic when `Y` parses as a *type* and the construct is in type position;
a call/struct-literal argument list (`Ctor(field: expr)`) inside the brackets is a dict key, never
a generic parameter. Until then the detector must not be fatal — a heuristic hint that cannot be
suppressed and aborts the run is worse than no hint.
