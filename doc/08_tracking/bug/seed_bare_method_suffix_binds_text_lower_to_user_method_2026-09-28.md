# Seed binds untyped bare `x.lower()` to the only user `*.lower` method (2026-09-28)

**Status:** open (seed). Symptom worked around in `.spl` by PR `work/fix-aarch64-simd-avx512-owner`.

## Symptom
macOS arm64 Stage 2 sanity (run 36345547574, sha 3caa0bb071f) aborted on the
hello-world `native-build` after `monomorphize` with
`non-SIMD instruction reached AVX-512 instruction owner` (rc 134). The x86
AVX-512 owner was never selected by target dispatch; aarch64 routes to
`isel_module_aarch64`.

## Root cause
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`,
`compile_method_call_static`: when direct/use_map/import_map lookup fails, a
bare method name is resolved by scanning `func_ids` for keys ending in
`.{method}` / `_dot_{method}`. With exactly one candidate it binds silently
(~lines 1136-1152), before the builtin text mapping (`lower` ->
`rt_string_to_lower`, ~line 2542) is consulted. Only bare `has`, `len` and
`length` are excluded (~lines 962-970). `Avx512InstructionLowerer.lower` was
the only user `*.lower` method in the closure, so every text `.lower()` whose
receiver MIR did not type as STRING called the AVX-512 owner.

## Reproduction (Rust seed, aarch64 Linux)
```
class OwnerLowerer:
    count: i64
    me lower(n: i64):
        print "MARKER owner reached"
fn shout(v) -> text:
    v.lower()
fn main():
    var o = OwnerLowerer(count: 0)
    o.lower(1)
    print shout("HeLLo")
```
`SIMPLE_ALLOW_UNRESOLVED_RT=1 SIMPLE_BOOTSTRAP=1 simple compile fx.spl --native --backend=cranelift`
prints `MARKER` twice and `0`, where it should print `MARKER` once and `hello`.

## Fix needed in seed
Resolve bare text-builtin method names (`lower`, `upper`, `trim`, ...) builtin
first, or exclude them from the single-candidate name-suffix bind, as was done
for `has`/`len`. Until then, no user method may be named after a text builtin.
