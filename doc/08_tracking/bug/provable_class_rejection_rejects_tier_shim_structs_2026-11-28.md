# provable_class_rejection rejects identical tier-shim structs (ShaderSource owner collision)
## Registered 2026-11-28 by p3sweep5 lane (regression interaction of interpreter_wrong_owner_arg_overload_fallthrough_2026_11_27's fix)

**Status:** OPEN
**Severity:** P3
**Lane observed:** Windows x86_64, tree-built seed

## Symptom

Calls with a class argument fail with the wave-9 ambiguous-call error even
though the argument is legitimately typed:

```
error: semantic: ambiguous call to `create_shader_program`: argument of
class `ShaderSource` selects none of the overloads
```

Concrete case: `test/01_unit/lib/engine/gpu_bridge_spec.spl` — the
`create_shader_program(source: ShaderSource)` API exists exactly as pinned,
but three IDENTICAL `struct ShaderSource` definitions (tier shims in
`gc_async_mut` / `nogc_async_mut` / `nogc_sync_mut` `render/shader.spl`)
collide under co-compilation; the value's owner-stamped class never matches
the parameter's owner, so `provable_class_rejection`
(`src/compiler_rust/compiler/src/interpreter_call/mod.rs`) rejects every
candidate. Both a builtin-produced value and a spec-constructed
`ShaderSource` are rejected; fails with and without `SIMPLE_LIB=src`.
Regression since 2026-11-11 (seed `46fe8f6b6def` green).

## Root cause direction

`provable_class_rejection` treats owner mismatch as conclusive rejection,
but tier-shim families define byte-identical structs in each runtime tier;
the owner-exact identity check can never match across tiers. The rejection
needs an exemption (or the collision needs first-wins resolution) for
same-name same-layout classes from tier shim modules — or the tier shims
should re-export a single canonical definition instead of re-declaring.

## Acceptance

A call passing a `ShaderSource` from any tier shim to
`create_shader_program` resolves (per the overload set's intent), pinned by
gpu_bridge_spec returning to green and a regression spec for the
tier-shim exemption.
