# LLVM direct translation scratch and bootstrap-cache lifetime

**Status:** open

The admitted LLVM file-emission path bypassed `compile_module_with_backend_scoped_v1`, so `SIMPLE_CODEGEN_MODULE_SCOPE=1` did not reclaim its translator scratch. The direct route is `compile_owned_aot_into_path_v2` → `BuiltinBackendCompileAdapter.compile_aot_into_path` → `compile_llvm_module_to_object_path` → `llvm_compile_module_direct_to_path`.

The candidate scopes only `llvm_translate_module_direct_ir_for`, promotes the returned IR text, closes the scope, then invokes the existing object-file emitter. MIR storage lowering/optimization, persistent backend authority mutation, tool initialization, object publication and diagnostics remain outside the new scope. The option remains off by default. This reclaims translator scratch only; retained IR text and optimizer allocations remain outside the claimed savings.

## Intentional temporary exclusion

The `@workaround` tagged `llvm_bootstrap_string_cache_scope_escape_2026_10_25` refuses the new scope when `SIMPLE_BOOTSTRAP=1`. The translator's bootstrap path assigns heap text to `_llvm_bootstrap_string_globals_text_cache` in `_MirToLlvm/asm_constraints_helpers.spl`. The exported accessor can read that text until a later reset. Freeing it at scope end would leave a dangling global; silently clearing it would change the accessor contract. Remove this exclusion only after that cache has an explicitly owned/preserved lifetime and repeated bootstrap string-literal emission is qualified natively.

The other audited owners must not be moved inside the scope: MIR optimization appends provider events to the persistent SIMD report; strict tool admission can initialize persistent binding arrays; backend session authority owns retained uses/results. The existing LLVM header override is scalar, and the temporary translator restores it on its normal return path. No input MIR, target options, or retained target configuration is scope-owned.

A borrowed active/paused scope is never ended by this function. An unavailable new scope keeps the old unscoped path with a warning. After successful scope end, failed IR promotion returns a diagnostic/status without inspecting freed text. Failure to end the owned scope panics rather than returning to persistent authority bookkeeping with unknown ownership state.

## Qualification status: draft, native validation pending

`llvm_direct_translation_scope_native_spec.spl` exercises real LLVM emission of a string literal, repeated calls using the same retained configuration, scope-off/on object comparison with debug metadata disabled, file-publication failure diagnostics, an outer caller-owned scope, and the bootstrap exclusion. The first call permits cold tool admission; the outer-scope case warms tools before borrowing its scope. The spec is not represented as passed until executed with a compiler containing this candidate. Actual P3/native lifetime and memory measurements remain required before merge. No Phase 2 compiler or runtime rebuild is authorized or performed for this draft.

The earlier SIG9 below a 17 GiB guard remains unattributed; this source-level scratch-lifetime gap does not establish the cause of that termination.
