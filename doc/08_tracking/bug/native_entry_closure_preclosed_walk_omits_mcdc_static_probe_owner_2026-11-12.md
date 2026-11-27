# `--entry-closure` native build under `SIMPLE_MCDC_MODE=on` links against an MC/DC probe owner the CLI walk never admitted

Status: FIXED (walker admits the owner; spec red->green on the seed). Needs a Stage 2 redeploy to take effect in the matrix.
Severity: P1 for the Phase 4 native test lanes (every native doctest fails; any native spec whose authored closure lacks the owner fails the same way). Not a Stage 3 self-compile blocker: the bootstrap chain compiles with MC/DC off.
Found: 2026-11-12, Stage 2 test-runner lane, run 16 (`c7431e08861`), four-kinds driver, kind 2 (`SIMPLE_SDOCTEST_SPL=1 ... --sdoctest src/lib/nogc_sync_mut/concurrent/channel.spl --native-backend=cranelift`).

## Symptom

All four `channel.spl` doctest examples compile (64-65 modules, 150-200 s each) and fail at link. The runner reports only `native-doctest: compilation failed or artifact missing`; the producer stderr ends with `[LLVM-LINK] failed link inputs retained for replay (45 runtime objects)` and never prints the linker error. Replaying the retained `*.link-command.txt`:

```
ld.lld: error: undefined symbol: lib.nogc_sync_mut.mcdc.static_probe.mcdc_static_probe_configure_bytes
>>> referenced by test.native_generated__5f2ffcbf84c9.entry
```

`lib.nogc_sync_mut.mcdc.static_probe` is absent from the 70 loaded modules.

## Cause

The runner publishes `SIMPLE_MCDC_MODE=on` to every producer (`test_runner_config.spl` `apply_mcdc_mode_env`, fail-closed default). The compiler reads it (`src/compiler/00.common/config.spl:152`), so `config["mcdc_mode"] = "on"` and MIR emits the one entry-side configure call (`function_lowering.spl:1056` -> `emit_mcdc_runtime_configuration`, `mir_lowering_stmts.spl:3346`) targeting `std.nogc_sync_mut.mcdc.static_probe.mcdc_static_probe_configure_bytes` with no authored `use`.

That hidden ABI edge is admitted only by the pipeline's closure scan (`driver_source_pipeline_loading.spl:1098`, `closure_imports.push("std.nogc_sync_mut.mcdc.static_probe")`, exempted from parity by `driver_closure_synthetic_spec_v1`). A native-build whose parent walk published a frozen preclosed request hands it over with `closure_walks=0`:

```
[BOOTSTRAP-PHASE] +2231ms phase1:load_sources:preclosed:admitted selected=70 closure_walks=0
```

(probe: run 16 Stage 2, same argv/env as the runner, `SIMPLE_COMPILER_TRACE=1 SIMPLE_LOG=phase`). The preclosed selection comes from the CLI walk `_native_build_entry_closure` (`src/app/io/_CliCompile/native_build_closure.spl`), which follows authored `driver_closure_import_specs_v1` only. So the owner is admitted only when the authored closure happens to import it: unit specs reach it through `lib.nogc_async_mut.spec` -> test-runner MC/DC runtime (the kind 3 builds list `lib.nogc_sync_mut.mcdc.static_probe`; their link failures are the separate `rt_bdd_*` bundle gap), doctest entries do not.

Not a Stage 2 miscompile: the walk has no synthetic-edge code at all. Same hole for the `rt_hal` synthetic edges (`std.nogc_sync_mut.rt_hal.boundary`, `process_task_arena`) on `@rt_hal`-annotated entries; not fixed here.

## Fix

`native_build_mcdc_closure_spec_v1(mode_text)` maps the configured mode (`SIMPLE_MCDC_MODE`, the only source this binary honours; `bootstrap_main` has no `--mcdc`) to the probe owner spec, and the walk pushes it onto the entry file's import specs. Spec: `test/01_unit/compiler/driver/native_build_mcdc_closure_spec.spl` (helper mapping + walk of an import-free fixture entry with the mode on/off).

## Verification

- Seed (`bin/simple` absent; pinned seed `pinned-f8ad54b28467/.../target/bootstrap/simple`) on the spec: red (`native_build_mcdc_closure_spec_v1` unresolved) -> green after the change. Numbers in the PR body.
- End to end needs a Stage 2 rebuilt from this change; the four-kinds driver's kind 2 is the regression (expected: 4 examples link).

## Related

- `doc/08_tracking/bug/mcdc_entry_configuration_not_emitted.md` (the configure call this edge serves)
- `doc/08_tracking/bug/full_suite_aborts_mcdc_dynamic_probe_symbol_2026-08-26.md` (dynamic twin, pipeline-side)
- `doc/08_tracking/bug/test_runner_native_producer_failure_reported_as_exit_minus_one_empty_output_2026-11-12.md` (why the runner showed nothing)
