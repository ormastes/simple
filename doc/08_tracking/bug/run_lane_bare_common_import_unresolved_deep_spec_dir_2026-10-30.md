# Run/HIR lane cannot resolve `common.*` / `std.*` from deep spec dirs under `test/01_unit/lib/<family>/`

## Status
Fixed in the Rust seed resolver on 2026-10-30. The shared `bin/simple` picks up the fix only after the seed is redeployed.

## Symptom
In a directory sweep (`simple test test/01_unit/lib/nogc_async_mut/`), which
runs each file through `simple run`:
`cannot resolve import common.gpu.environment_variant_task_contract_v1:
module path segment 'common' not found`, plus the same error for
`common.ui.draw_ir` and `common.gpu.engine2d.gpu_epoch`. A single-file
`simple test <file>` passed, because that path does not do HIR lowering
through this resolver.

## Root cause
`module_resolver/types.rs`:
1. `find_project_root` stops at the first ancestor with a `src/` dir. The spec
   mirror `test/01_unit/lib/nogc_async_mut/src/` (it mirrors
   `src/lib/nogc_async_mut/src/`; `gc_async_mut`, `gc_sync_mut` and `nogc_sync_mut`
   have the same mirror) therefore makes `test/01_unit/lib/nogc_async_mut` the
   "project root". That root has no `src/lib`.
2. `detect_stdlib_root`'s fallback climbed at most 5 levels from the file. From
   `.../nogc_async_mut/gpu/` it never reached the repo root. Even at the repo root
   it would have picked `src/compiler_rust/lib/std/src`, which sits first in the
   candidate list, instead of `src/lib`.

## Fix
`detect_stdlib_root` now climbs until it reaches the existing `.git`/`.jj`
workspace boundary (or `/` when there is none, same as the interpreter lane),
with no fixed depth cap. On the climb it takes the first
ancestor's `src/lib` before the other candidates. `find_project_root` is
unchanged, so fixture projects with their own `src/` keep their roots.

Blast radius: only files whose `project_root` has no stdlib candidate reach the
climb. Shallow specs in the `gc_sync_mut`/`gc_async_mut`/`nogc_sync_mut` mirrors
and `test/fixtures/arch_check` now get `src/lib` where they previously got the
seed snapshot `src/compiler_rust/lib/std/src`. This matches the interpreter lane's
ordering, and none of them import a seed-only module. Files whose project root
is the repo still go through the unchanged first loop, so seed-first ordering
there is not addressed here.

## Specs
- Reproduction: `test/01_unit/lib/nogc_async_mut/gpu/environment_variant_task_{owner,contract}_v1_spec.spl`,
  `environment_variant_native_task_bridge_v1_spec.spl`, and
  `engine2d/{packed_completion_authority_v1,environment_variant_completion_bridge_v1,draw_ir_runtime_queue}_spec.spl`.
- Generalization: `test/01_unit/lib/nogc_async_mut/gpu/engine2d/bare_common_import_deep_spec_dir_spec.spl`
  (on the `simple run` lane that directory sweeps use: ERROR on the old seed,
  PASS on the fixed one; single-file `simple test` does not use this resolver).
