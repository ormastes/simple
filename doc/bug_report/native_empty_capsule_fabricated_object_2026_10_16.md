# Unexpected empty native capsules must fail closed

Status: source repair; native verification pending. Bug database registration pending qualified tooling.

The preexisting empty-module fallback in `_compile_selected_module` wrote a C
global named `simple_empty_module_*` and compiled it as a successful object.
Its condition examined only functions and statics, with no parsed declaration
proof. Missing lowering output for a real function could therefore be hidden
behind an apparently valid physical object and receipt.

The repair restores the previous hard error for unexpected scheduled modules
with neither functions nor statics. Constants handling remains unchanged.
Legitimate objectless modules are still retained in the source inventory and
receive their typed objectless outcome before capsule scheduling: the native
cache loop checks the identity-bound frozen parsed proof or live parsed
predicate, records the outcome, and continues. Runtime/std selection rejects
objectless members requiring a different typed outcome. The selected-module
function has one caller, the frozen capsule emitter; it has no parser evidence
that could justify fabricating code.

The retained A174 producer has a separate older classification defect: its
facade predicate requires an import/export/type declaration and consequently
rejects the comment-only env.utilities module. Current source already removes
that positive witness requirement while preserving body/data guards. This
repair does not update the retained executable and is not an input workaround.

Evidence: manual-enum-wire-contract-cycle3 under the external Phase3 validation
directory, exit1, zero retained objects, no link. Existing behavioral predicate
tests in native_build_cache_plumbing_spec cover empty modules and rejection of
runtime-bearing declarations. They have not been rerun. Native negative
qualification must demonstrate that a scheduled capsule with missing function
lowering fails without producing a C file/object; no runtime PASS is claimed.
