# Robust Lifecycle Persistence — TLDR

The selected design adds no grammar. Lifecycle persistence is represented by
ordinary Simple values and pure validators.

```sdn
LifecyclePersistence {
  syntax: existing_simple
  grammar_changes: none
  model: [LifecycleGraph, LifecycleTransition, RecoveryRegistration]
  identity: reuse_EntityKey
  placement: [section_attribute, linker_sdn, board_sdn]
  checks: [acyclic, dependency_order, metadata_complete]
}
```

- Removed proposals: `life`, `virtual life`, `transition`, and `recovery` declarations.
- Use `val`, `<>` generics, direct constructors, qualified enum variants, and ordinary functions.
- Do not redefine the frozen snapshot-local `EntityRef`; durable products reuse/wrap `EntityKey`.
- Recovery algorithms remain normal Simple state machines.
- Strictness uses `moderate`, `strict`, `robust`, and `critical`.
- Model tests do not substitute for product power-cut, boot, linker, or proof evidence.

