# Bare Ok/Err arms on imported trait method result ambiguous in stage2

**Status:** open

## Symptom
Under `SIMPLE_BOOTSTRAP=1` the current stage2 reports
`bare variant 'Ok' is ambiguous ... subject method call <Trait>.<m>() ... has type unresolved`
for `match` on an imported trait method call (`Codegen.compile_module`) with bare `Ok`/`Err` arms.

## Sites
- src/compiler/70.backend/backend/backend_api.spl (`CompilerBackend.compile`)
- src/compiler/70.backend/backend/backend_helpers.spl (`compile_module_with_backend...` tail match)
- src/compiler/20.hir/hir_codec_support.spl:554,582 are reported too but are `val slot: T = call(...)` bindings, not matches; left unchanged.

## Workaround
Typed local `val compiled: Result<CodegenOutput, CompileError> = ...` before the match, tagged `@workaround`.

## Real fix
#4998 (merge 275989c9af6) resolves imported trait method declared returns for bare Ok/Err arms.
Remove the workarounds once a compiler built from >= 275989c9af6 is deployed.
