# LLVM env_get alias captures a local definition

Status: source repair and regression specifications authored; verification pending.

Astra review found that `core_codegen.spl` rewrites every bare `env_get` call
to `rt_env_get_value` (one argument) or `rt_env_get` (split arguments), even
when the entry module defines its own function with that name. A local
`fn env_get(key: text) -> text?: Some("local-value")` therefore reads the
process environment instead of executing its body. The name is not reserved
by `mir_runtime_owned_call_name`.

The LLVM pre-emission ownership pass now records a local `env_get` body in
the existing local-collision map. Runtime alias rewriting applies only when
that local identity is absent. This does not depend on `defined_func_names`
or function emission order. The bootstrap return ABI override also excludes
a local `env_get`, preserving unrelated integer signatures. Explicit
`rt_env_get` calls and bodyless imported `env_get` aliases retain their
runtime ABI routing.

Authored evidence gates:

- `test/01_unit/compiler/backend/llvm_env_get_local_owner_spec.spl`: direct
  MIR-to-LLVM owner checks, callers before/after the definition in sorted
  emission, entry/nonentry naming, explicit bootstrap on/off modes, nonlocal
  alias, and explicit runtime call beside a local collision.
- `test/02_integration/compiler/backend/llvm_env_get_local_owner_native_spec.spl`:
  real optional text local values with source order permutations, an imported
  bare extern positive control, and a local integer signature collision. It
  requires `SIMPLE_BINARY`, isolated caches, and disables stub fallback.
- Existing `test/01_unit/compiler/mir/inline_text_extern_abi_spec.spl` retains
  the bodyless extern alias ABI positive fixtures unchanged.

No admitted rebuilt producer is available in this repair lane. These tests
have not executed; no runtime, LLVM verification, or production readiness
PASS is claimed. Resume with an admitted producer containing this exact
source delta, run the two authored specs and existing alias ABI spec, then
complete the compiler/core/lib and MCP native smoke gates.
