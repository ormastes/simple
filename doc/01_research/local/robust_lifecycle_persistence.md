# Local Research: Robust Lifecycle Persistence

## Current language evidence

- `doc/07_guide/quick_reference/syntax_quick_reference.md` establishes ordinary `enum`, `struct`, `trait`, function, direct-constructor, generic `<>`, `val`, and `if val` syntax.
- `doc/07_guide/language/strictness_tiers.md` defines the current `moderate`, `strict`, `robust`, and `critical` profiles.
- `@section` and linker/board SDN already own source placement and physical memory-region policy.
- Existing AOP `pc{...}` syntax is unrelated and does not justify a second lifecycle block grammar.

## Existing owner collisions

`src/lib/common/structural/identity/entity_id.spl` freezes two meanings:

- `EntityRef`: compact snapshot-local reference;
- `EntityKey`: durable cross-revision identity.

The prior proposal's new generic `EntityRef<T>` would collide with that owner and
incorrectly suggest reboot stability. The revised design reuses or distinctly
wraps `EntityKey`.

## Existing lifecycle patterns

The repository represents lifecycle configuration with normal structs and
factory functions, for example `LifecycleConfig` in
`src/compiler/99.loader/loader/resource_lifecycle.spl`. Pure validation modules
already use typed values rather than adding declaration grammar.

## Conclusion

No language-surface gap requires new lifecycle declarations. A pure common model,
default stdlib facade, typed validation, and product-owned SDN adapters fit the
current architecture and conventions.

