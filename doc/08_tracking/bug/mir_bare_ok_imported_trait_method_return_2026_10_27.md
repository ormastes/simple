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

Note: the current stage2 6b0ba5f3 accepts typed Result locals (the phase3_result_local_match_owner constraint no longer applies), which is why the typed local is safe here.

## Verification pending (2026-11-04)
Compiler fix #4998 (275989c9af6) is on release/1.0.0. The typed-local @workaround at backend_api.spl:161 and backend_helpers.spl can be removed once a compiler built from >=275989c9af6 is deployed (stage3).

Related row wm_production_fullscreen_evidence_security_registry_any_field_infer_2026-08-09: fix 7fa2d06aaa8 is on release/1.0.0; verify with `sh scripts/check/check-wm-production-fullscreen-evidence.shs` on a stage3-deployed bin/simple.
