# A qualified enum variant is shadowed by a same-named global type inside fn/method bodies

- Status: OPEN (2026-09-12)
- Component: seed name resolution (`src/compiler_rust`)
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple`, sha256 `3d120a6f9ab5704b`
- Found by: L78-INT while running the L7/L8 V4 unit specs

## Symptom

`L78TokenKindV4.Scope` — a fully qualified nullary variant of
`L78TokenKindV4` (declared in
`src/compiler/00.common/cache_contract/semantic_scope_live_port_contract_v1.spl`)
— evaluates to a CONSTRUCTOR object rather than the enum value, whenever
the module graph also contains an unrelated global type named `Scope`
(e.g. `src/compiler/20.hir/hir_types.spl:230 struct Scope`, reachable via
`compiler.driver.cache.reference.reverse_reference_coordinator_v1` and
`compiler.driver.cache.gateway.semantic_scope_authority_v1`).

Printing it gives `<constructor:Scope>` instead of `L78TokenKindV4::Scope`,
and `x == L78TokenKindV4.Scope` is then false for a correctly built token.
No diagnostic is issued. Sibling variants of the SAME enum
(`.Namespace`, `.AffectedDomain`) and other enums (`L78AuthorityDomainV4`,
`L78BoundaryErrorV4`) resolve correctly — only the colliding name breaks.

## Where it breaks and where it does not

Measured in one spec file whose imports are explicit (no wildcard needed):

| context | result |
|---|---|
| top-level `fn` body | BROKEN (`<constructor:Scope>`) |
| class `me` method body | BROKEN |
| `match` arm pattern in a top-level fn | BROKEN (arm never matches) |
| module-level `val K: L78TokenKindV4 = L78TokenKindV4.Scope` | CORRECT |
| inside an `it` closure in a spec | CORRECT |

Wildcard vs explicit imports does not change the outcome; what matters is
whether the colliding global type is anywhere in the module graph.

## Impact

`test/01_unit/compiler/cache/l78_affected_domain_port_v4_spec.spl` failed
6 of 9 examples with `L78BoundaryErrorV4::ForeignToken` from the RR fake's
`token.kind == L78TokenKindV4.Scope` check, on a token that genuinely
carried the Scope kind.

## Workaround applied (this is a workaround, not the fix)

Each affected file gained a module-level constant

```simple
val L78_KIND_SCOPE_V4: L78TokenKindV4 = L78TokenKindV4.Scope
```

and every in-body use of `L78TokenKindV4.Scope` now reads the constant.
The frozen design-8.1 variant name `Scope` is unchanged. The real fix is
for a qualified `Enum.Variant` path to never be resolved against an
unrelated global type.
