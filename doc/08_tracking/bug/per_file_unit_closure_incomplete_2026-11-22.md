# Per-file unit fails CLOSURE-INCOMPLETE when a target imports a summarised package `__init__.spl`

Date: 2026-11-22
Status: fixed in source (plan step); not yet proven on a redeployed compiler
Area: `src/compiler/80.driver/driver_unit_tldr_imports_v1.spl` (PM3 unit plan)

## Symptom

Default per-file native-build lane, Stage 2 built from release `53795406ba6`,
bootstrap CLI closure (1601 modules), `SIMPLE_FILE_WORKER_BATCH=8`, 8 workers:

```
error: FILE-WORKER-E-CLOSURE-INCOMPLETE: import-closure surface missing for src/compiler/10.frontend/core/_AstExpr/accessors.spl
[ERROR] phase 2 FAILED (1 recorded error(s))
[file-worker] owner=5/8@0 unit exit=1 hir_claimed=0 mir_claimed=0 closure_incomplete=false orphan_picks=8
```

Also reported for `core/ast_stmt.spl`, `treesitter_types.spl` and
`30.types/_TypeLayout/c_assert_gen.spl`. The named file is only the last
unready target of the unit in surface order, not the cause.

## Where it is raised

`src/compiler/80.driver/driver_source_parse_streaming.spl`, the `mir_scoped`
readiness check after phase 2 (`self.ctx.add_error("FILE-WORKER-E-CLOSURE-INCOMPLETE: ...")`).
A target is ready only when its surface is built and every import /
export-route edge target is ready, transitively (`worker_surface_ready_v1`).
In the unit lane a row is "built" when it was parsed here
(`unit_tldr_plan.parse_paths`, i.e. picked + fallback modules) or took a
summary surface from the plan.

## Root cause

The streaming loop refuses a summary surface for any `/__init__.spl` row (it is
parsed for its manifest facts), but `unit_tldr_plan_v1` still summarised such a
package when the summary succeeded. The row was then neither in `parse_paths`
nor on the summary lane: it became a mode-2 placeholder, `worker_built` stayed
false, and every target that reaches it through parsed rows was unready.

A summary succeeds for an `__init__.spl` that holds only qualified sibling
re-exports (`export variables.env_get, ...`), which is exactly
`src/lib/nogc_async_mut/env/__init__.spl` (`std.env`). Packages whose
`__init__.spl` has a docstring or `export use` already fell back to a source
parse, which is why most units pass.

Not the import-cycle peer pick, batch size, or a cache race:

- failing units include plain `picked=8` units and a `picked=15` unit; the
  same pick set fails again after the worker is re-launched (deterministic);
- attempts 1 (batch 1) and 2 (6 workers) never reached a unit that imports
  `std.env` (0 `module=std.env.types` fallback lines; attempt 3 has 13), so
  they prove nothing about batch or concurrency;
- in the failing unit's log `std.env.types/.variables/.config` are fallbacks
  while `std.env` itself is not, i.e. `std.env` was summarised;
- `_AstExpr/accessors.spl` imports `std.env.{env_get_or}` directly; the other
  three reach it through `ast_expr`.

## Reproduction (3 files, Stage 2 from `53795406ba6`)

```
src/cfx/env/__init__.spl   export variables.cfx_env_get
src/cfx/env/variables.spl  pub fn cfx_env_get(n: i64) -> i64: n + 1
src/cfx/main.spl           use cfx.env.{cfx_env_get} ...
```

`native-build src/cfx/main.spl --entry-closure` fails with
`FILE-WORKER-E-CLOSURE-INCOMPLETE: import-closure surface missing for src/cfx/main.spl`.
Adding a docstring to `__init__.spl` (forcing the existing fallback route)
makes the same build pass and the binary print `v=21`.

## Fix

`unit_tldr_plan_v1` no longer summarises an `/__init__.spl` module: it takes
the existing fallback route (`parse_paths`, `[tldr-fallback] ... source-load=1`),
so the row is parsed, built and HIR-loaded like any other fallback module.

## Workaround for a compiler built before the fix

`SIMPLE_UNIT_TLDR_IMPORTS=0` (read at
`src/compiler/80.driver/driver_tldr_import_route_v1.spl`,
`unit_tldr_imports_enabled_v1`) turns the unit summary route off; the fixture
then passes. It restores the per-unit import-closure parse, so expect a higher
per-worker RSS.

## Verification

- fixture fail / fallback pass / knob pass: run on the Stage 2 binary above;
- spec `it "parses an imported package __init__ instead of summarising it"` in
  `test/01_unit/compiler/driver/unit_lane_tldr_imports_spec.spl`: written, not
  run (no test-capable `simple` binary on the host);
- the fix itself on a rebuilt compiler: not run (needs a bootstrap redeploy).
