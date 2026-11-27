# FILE-WORKER-E-CLOSURE-INCOMPLETE: braced qualified re-export `export pkg.{a, b}` is never planned

Date: 2026-11-27
Status: fixed in source; seed spec red -> green; NOT verified on a rebuilt Stage 2
Area: `src/compiler/80.driver/driver_tldr_import_route_v1.spl` (`tldr_route_import_specs_v1`)
Same class as `per_file_unit_closure_incomplete_2026-11-22.md` and
`file_worker_closure_incomplete_unit_tldr_alias_row_2026-11-15.md` (a readiness
edge the PM3 unit plan does not follow).

## Symptom

Stage 2 verification of pinned `3dd00937c329`, `compiler_cli_build|result=FAIL|status=1`.
First error in time order (worker `owner=1/2@0`, log line 328020):

```
FILE-WORKER-E-CLOSURE-INCOMPLETE: import-closure surface missing for
  src/lib/common/diagnostics/__init__.spl; blocking_target_index=2734
  reachable-gap=unbuilt-dependency source_index=2734 target_index=539 inspected_edges=1
  source=src/lib/common/diagnostics/__init__.spl
  target=src/lib/common/diagnostics/diagnostic_v1.spl
```

The retry `owner=1/2@1` fails on the same edge (reached from
`src/app/editor/editor_layout.spl`, `inspected_edges=349`) and claims nothing, so the
pool reports `failed_modules=3347`.

In the failing unit the log has `[tldr-fallback] module=std.common.diagnostics`
(the `__init__.spl` is parsed), `interface-hir hit` for `severity.spl` and
`span.spl`, and only `phase2:surface:file:released` for `diagnostic_v1.spl`: no
summary, no fallback, no parse. Units that pass reach `diagnostic_v1` through a
direct `use std.common.diagnostics.diagnostic_v1.{...}`.

## Root cause

`src/lib/common/diagnostics/__init__.spl`:

```
export severity.Severity
export span.Span
export diagnostic_v1.{DiagnosticV1, LabelV1, ...}
```

The qualified-export branch of `tldr_route_import_specs_v1` split the line on
`,` and required each item to be a dotted path. `diagnostic_v1.{DiagnosticV1`
contains `{`, the other items have no dot, so the line produced no edge. The
export-route freeze does resolve the braced form, so the sibling was a hard
readiness edge (`kind=export` and `kind=import` rows in
`phase2:surface:missing-direct-edge`) that the unit plan never summarised or
parsed. The readiness-side text scan `worker_surface_import_ids_v1`
(`driver_worker_surface_graph_v1.spl`) takes everything before the last `.` of
each comma item as the qualifier with no identifier check, so it does yield
`diagnostic_v1`; the two scanners disagreed only on this spelling (no mixed
`export a.b, c.{x}` line exists in `src/`). 56 `export <path>.{` lines exist in `src/` (15 files, 2 of them under
`src/compiler_rust/lib/std`), some multi-line
(`src/lib/nogc_async_mut/llm_diagnostics/mod.spl`).

A source logic gap, not a Stage 2 miscompile and not the seed `str_<method>`
rebinding: the seed interpreter returns the same missing edge.

## Reproduction (Stage 2 from `3dd00937c329`, committed sources, `SIMPLE_FILE_WORKER_BATCH=1`)

```
src/cfx/env/__init__.spl   export variables.{cfx_env_get}
src/cfx/env/variables.spl  pub fn cfx_env_get(n: i64) -> i64: n + 1
src/cfx/main.spl           use cfx.env.{cfx_env_get}; fn main(): print("v={cfx_env_get(20)}")
```

`SIMPLE_BOOTSTRAP=1 simple native-build src/cfx/main.spl --entry-closure -o out`:
rc=1, `FILE-WORKER-E-CLOSURE-INCOMPLETE ... src/cfx/env/__init__.spl`,
`missing-direct-edge kind=export source=src/cfx/env/__init__.spl target=src/cfx/env/variables.spl`.
Control, same binary, `__init__.spl` spelled `export variables.cfx_env_get`:
rc=0, 0 missing-edge rows, binary prints `v=21`.

## Fix

The export branch recognises `export <dotted>.{names}` (single or multi-line,
`as` aliases, trailing comments) and pushes the same `.prefix` (and absolute
`prefix` when dotted) edges as the unbraced form. Frozen-route callers
(`include_export_from` false) are unchanged.

## Verification

- `test/01_unit/compiler/80.driver/tldr_route_export_from_spec.spl` on the seed:
  before `executed=16 passed=13 failed=3`, after `executed=16 passed=16 failed=0`
  (one case scans the real `diagnostics/__init__.spl` and expects all 7 siblings).
- `test/01_unit/compiler/driver/tldr_route_spec.spl` (7 failures) and
  `unit_lane_tldr_imports_spec.spl` (1 failure): identical failing set with and
  without the change.
- Not run: the braced fixture on a Stage 2 rebuilt from this source (needs a bootstrap).

## Workaround for a compiler built before the fix

Spell the facade unbraced (`export pkg.a, pkg.b`), or `SIMPLE_UNIT_TLDR_IMPORTS=0`.

## Separate failure in the same log (open, not addressed here)

`owner=0/2@0` exits 1 for its own reason (log ~line 632160):
`AOT compile error in compiler.mir._MirLoweringExpr.expr_dispatch: Failed to
write LLVM IR to private staging` (1 ICE, `claimed=16 passed=15 sealed_failed=1`).
The log gives no staging path or OS error. Not classified: it may be independent
or a consequence of the pool already being blocked at line 328027.
