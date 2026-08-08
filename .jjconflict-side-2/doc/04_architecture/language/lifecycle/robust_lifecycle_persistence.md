# Robust Lifecycle Persistence Architecture

## Decision

Lifecycle persistence is a library-and-metadata concern, not a grammar concern.
The feature uses existing Simple syntax and lowers product policy through typed
values, ordinary functions, and linker/board SDN.

```sdn
LifecyclePersistence {
  source: [enum, struct, trait, function, generic_wrapper]
  typed_model: [LifecycleGraph, LifecycleTransition, RecoveryRegistration]
  validation: [graph_acyclic, dependency_order, metadata_complete]
  platform: [section_attribute, linker_sdn, board_sdn]
  consumers: [runtime, boot, persistence_backend, verification]
}
```

## Ownership

- `src/lib/common/lifecycle_persistence/`: tier-neutral value model and pure validation.
- `src/lib/nogc_async_mut/lifecycle_persistence.spl`: default stdlib-family facade.
- Existing structural identity owners keep `EntityRef`, `EntityKey`, and codec contracts.
- Existing linker and board owners keep physical region/section durability.
- Product modules own recovery implementations and register them as ordinary values.

## Public-to-next-layer flow

1. Product code constructs a `LifecycleGraph` with ordinary values and edges.
2. Product code constructs transition and recovery registrations with normal constructors.
3. Pure validation rejects cycles, invalid dependency ordering, and incomplete metadata.
4. Platform code cross-checks validated metadata against existing SDN section/region data.
5. Runtime, boot, and proof generators consume the validated model; none reparses source syntax.

## Encapsulation

The common model exposes values and validators only. It does not own storage I/O,
global registries, linker parsing, runtime handles, or code generation. This keeps
the layer reusable on hosted and freestanding targets and prevents a parallel
persistence engine.

## Rejected alternatives

- New `life`, `virtual life`, `transition`, and `recovery` declarations: duplicate existing data/type/function syntax and require lexer-to-tooling changes.
- Lifecycle-only field attributes: wrapper values and registration records are sufficient for the selected scope.
- A new generic `EntityRef<T>`: conflicts with the frozen existing snapshot-local `EntityRef`; durable identity should build on `EntityKey` or use a distinctly named typed wrapper.
- Runtime-call shortcuts: the core validation requires no host/runtime access.

## Invariants

- A graph contains unique level identifiers and no directed cycles.
- `owner -> dependency` is accepted only when `dependency` is equal or longer lived.
- Every transition names a known boundary.
- Every recovery registration has positive schema, codec, validation, recovery, clean-start, reconciliation, and activation names.
- Validation returns a typed failure and never converts missing metadata into a default.

## Verification boundary

Focused pure-Simple tests prove the model and validation rules. Storage crash
consistency, linker placement, boot execution, and formal refinement remain
separate product/platform acceptance lanes and cannot be inferred from model tests.

