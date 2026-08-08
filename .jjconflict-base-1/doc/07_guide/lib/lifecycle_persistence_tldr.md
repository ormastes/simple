# Lifecycle Persistence — TLDR

```sdn
LifecyclePersistence {
  grammar: unchanged
  API: std.lifecycle_persistence
  checks: [graph, dependency, transition, recovery]
  identity: durable_EntityKey_owner
  placement: [section_attribute, linker_sdn]
}
```

- Build metadata with ordinary structs, enums, arrays, and functions.
- An edge points from shorter to longer survival.
- Validators fail closed on cycles, unknown boundaries, and missing metadata.
- Recovery code remains ordinary Simple code.
- Model validation is not storage, reboot, power-cut, or proof evidence.

