# An entry outside `src/`/`examples/` under SCV freeze is never the native entry (no `__simple_main`, link fails)

- **ID:** scv_frozen_entry_outside_src_never_native_entry_2026-11-03
- **Priority:** P2 (phase 3: `test/04_smoke/bootstrap_hello_world.spl` cannot be a native-build entry; `src/app/...` entries work)
- **Status:** open. No source change yet; the phase-3 smokes moved their entries under `src/app/fable_smokes/`.

## Symptom
`native-build --entry-closure --entry test/04_smoke/bootstrap_hello_world.spl ...` on the stage3 candidate compiles
the module to an object and the link fails with `ld.lld: error: undefined symbol: __simple_main` (referenced by
`simple_entry.o:(main)`). The emitted object defines
`__simple_main_C__dev_wt_p3_envpol_build_scv_snapshots_scv_revision_v1_<hash>_test_04_smoke_bootstrap_hello_world`
instead (per-module main), i.e. the backend did not classify the module as the entry.

## Root cause
`MirToLlvm.translate_module` decides the entry with
`llvm_module_is_native_entry(module.name)` = `module.name == module_logical_name_from_path($SIMPLE_NATIVE_BUILD_ENTRY)`.
`SIMPLE_NATIVE_BUILD_ENTRY` is the relative `test/04_smoke/bootstrap_hello_world.spl` -> logical
`test.04_smoke.bootstrap_hello_world`. The module itself was parsed from the frozen SCV snapshot copy, and
`module_source_relative_path` (00.common/module_path_naming.spl) only anchors absolute paths at the first
`/src/` or `/examples/`; a `/test/` entry keeps the whole absolute snapshot path, so `module.name` is the
mangled `C_.dev.wt.<worktree>.build.scv.snapshots.scv_revision_v1_<hash>.test.04_smoke.bootstrap_hello_world`
and never equals the logical entry name. Every stage2-lane smoke lived under `src/app/_scratch_ed/...`, which is
why the gap was invisible there.

## Fix direction
Either anchor `module_source_relative_path` at `/test/` as well (and any other repo-root source tree the entry
may live in), or compare both sides through the same normalization (strip the SCV snapshot root before naming).
Add a spec that freezes an entry under `test/` and asserts the module name equals the logical entry name.
