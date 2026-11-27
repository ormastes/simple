# Seed JIT: `type X = Y` alias silently captures dispatch of a same-named trait in another module

Status: open (seed bug; worked around in source). No todo row by owner decision for this sweep.

## Symptom

`native-build` final worker died rc=70 at `BackendSessionOwnedLeaseV2.open` with
`Runtime error: Function 'CraneliftCodegenState.supports_target' not found` followed by the generic
"unresolved symbol -- code-generation dispatch gap" text. No compile-time or load-time diagnostic.

## Cause

`src/compiler/70.backend/codegen.spl` had `type Codegen = CraneliftCodegenState`, re-exported from
`src/compiler/70.backend/__init__.spl`. The trait `Codegen` lives in `codegen_types.spl`. Under JIT a trait-object
method call (`codegen.supports_target(target)`, `backend_plugin/builtin_adapter.spl`, receiver from
`CodegenFactory.create` returning the trait) was resolved against the alias target `CraneliftCodegenState`, which has no
`supports_target`. The alias is registered by simple name, so it wins over the trait in a different module.

## Fix in source

Alias and re-export removed (no importer). Pinned by
`test/01_unit/compiler/backend/backend_declaration_name_collision_spec.spl` (asserts the alias is absent).

## Seed bug to fix

- A `type X = Y` alias should not shadow a trait or type named `X` declared in another module; resolve by module-qualified
  identity, or reject the duplicate simple name with a diagnostic at load time.
- At minimum the dispatch-gap message should say the receiver's static type came from an alias.

## Latent sibling

`src/compiler/70.backend/backend/backend_api.spl:166`: `type Backend = CompilerBackend`. Any other module or trait named
`Backend` is exposed to the same capture. Same class as the whole-module de-JIT collisions in
`doc/08_tracking/bug/browser_4k_whole_module_dejit_name_collisions_2026-10-04.md`.

Found by the todo 478 native-build smoke; see
`doc/08_tracking/bug/native_build_scv_cold_init_runs_interpreted_after_jit_demotion_2026-11-27.md`.
