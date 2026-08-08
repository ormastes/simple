# Robust Lifecycle Persistence Research — TLDR

```sdn
ResearchSynthesis {
  topics: [typestate, persistent_identity, crash_logic, recovery, boot]
  useful_semantics: [partial_order, validation, migration, reconciliation]
  rejected_surface: [life_decl, virtual_life_decl, transition_decl, recovery_decl]
  selected_surface: existing_simple_library_model
}
```

The preserved synthesis surveys lifecycle, persistence, crash recovery, boot,
linker, AOP, and Lean concerns. Its semantic research remains useful, but its
custom declaration grammar and duplicate `EntityRef<T>` proposal are
non-normative. The selected design uses existing Simple constructs and reuses
the durable identity owner.

