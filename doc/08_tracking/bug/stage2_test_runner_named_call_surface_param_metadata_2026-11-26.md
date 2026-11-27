# Stage 2 test_runner_build: named call lacks bootstrap parameter metadata (surface-only callee)

- Filed: 2026-11-26
- Status: FIXED (this change)
- Found by: release/1.0.0 stage2 compiler-test matrix, lane v6
  (`stage2-compiler-tests/aarch64-unknown-linux-gnu`, pinned e803fa9762cd)

## Symptom

`test_runner_build` FAIL after 1714 s; 23 modules blocked, link refused:

```
[first-compile-error] MIR lowering error: named call lacks bootstrap parameter metadata:
  extract_blocks_from_content at src/lib/nogc_sync_mut/test_runner/test_manifest_scanner.spl:313:5
```

Only `lib.nogc_sync_mut.test_runner.test_manifest_scanner` actually failed;
the other 22 "failed modules" were blocked dependents.

## Root cause

The PM3 per-file unit lane (`SIMPLE_BOOTSTRAP_STAGE3=1 --mode dynload`,
`SIMPLE_MIR_SHARDING=1`) resolves imports through TLDR summary surfaces and
loads HIR only for each unit's claimed targets. The MIR bootstrap branch of
`named_call_slots_v1` (`src/compiler/50.mir/_MirLowering/named_call_arguments_v1.spl`)
binds named-call arguments from `bootstrap_fn_param_defaults_lookup`
(`src/compiler/50.mir/mir_data.spl`), which is populated by the HIR prescan
(`prescan_one_function_v1`) — and the prescan only visits HIR-resident
modules. A callee held only as a module surface (here
`extract_blocks_from_content` from `sdoctest/extractor.spl`, claimed by a
different unit than its caller) had no registry row, so the call failed
closed.

The sibling gap for call-origin rows was fixed the same way in
`driver_surface_call_origin_rows_v1.spl` (bug
`stage2_slim_driver_app_native_build_unproven_call_origin_2026-11-19`);
parameter rows had no equivalent transport.

## Minimal repro

41 modules `m01..m40` + `main`, each `mNN` calling `mNN+1.f(a: a, b: b)`
with all arguments named (callees have no defaults), built with the admitted
stage2 compiler:

```
SIMPLE_BOOTSTRAP_STAGE3=1 SIMPLE_MIR_SHARDING=1 SIMPLE_MIR_SHARD_COUNT=8 \
  simple native-build --mode dynload --entry-closure --entry main.spl ...
```

fails with `named call lacks bootstrap parameter metadata: f05` as soon as a
unit boundary splits caller from callee (reproduced 2026-11-26 on pinned
e803fa9762cd; repro sources under `build/repro-named-default/`).

## Fix

Transport parameter rows from the surfaces, mirroring the call-origin rows:

- `driver_surface_call_origin_rows_v1.spl`: new `SurfaceParamRowsV1` capture
  (owners, names, param counts, flat param names + default flags) taken while
  the surfaces are still alive.
- `driver_compiler_type.spl` / `driver_hir_pipeline_lowering.spl`: capture
  stored on the driver next to `surface_call_origin_rows_v1`.
- `mir_lowering_types.spl`: `surface_fn_param_rows_v1` /
  `surface_fn_param_ambig_v1` dicts on `MirLowering` (contents-mutated only).
- `provider_metadata.spl`: `register_surface_param_rows_v1` fills absent keys
  (bare name and `owner.name`), marks shape mismatches ambiguous.
- `driver_pipeline_lowering.spl`: registration next to the origin rows in the
  `mir_unit_scoped` MIR-setup block; HIR-prescan rows stay authoritative.
- `named_call_arguments_v1.spl`: on a bootstrap-registry miss, bind slots from
  the surface row. Surface rows carry no default expressions, so every
  parameter must be supplied by name; an unsupplied defaulted parameter keeps
  the fail-closed `named default requires admitted declaration scope`
  refusal. `complete_named_call_operands_v1` reorders the fully-supplied
  operands by slot for this path.

Module-level callables only; named calls to surface impl methods keep the
previous behaviour (their call-site key spelling is receiver-derived).

## Verification

- Minimal repro above: fails before, passes after (stage2 lane rerun).
  CONFIRMED 2026-11-26: the 41-module repro built with the pinned-06ba866385d5
  stage2 binary (`native-build --mode dynload --entry-closure`, MIR sharding
  8) links 41/41 and the executable runs clean (no panic, no
  `named call lacks bootstrap parameter metadata`). SCV admission note: the
  repro dir must be a git checkout with sources under `src/` and a `.simple`
  storage dir (`mkdir -p .simple/storage`).
- Stage 2 compiler-test matrix `test_runner_build` row: the
  `test_manifest_scanner.spl:313` call binds and the row builds.
