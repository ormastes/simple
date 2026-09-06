# Robust Lifecycle Persistence Architecture — TLDR

```sdn
LifecyclePersistence {
  owner: common.lifecycle_persistence
  facade: std.lifecycle_persistence
  inputs: ordinary_simple_values
  validation: [acyclic, dependency_order, metadata_complete]
  downstream: [linker_sdn, runtime, boot, proof]
}
```

- The common layer owns pure values and validators only.
- Existing identity owners keep `EntityRef` and `EntityKey`.
- Linker/board owners keep physical durability.
- Products own recovery functions and platform adapters.
- No parser, keyword, runtime-call, or parallel persistence-engine changes.

