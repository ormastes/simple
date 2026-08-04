# Local Research — TL;DR

```sdn
owners:
  semantics: compiler AOP/HIR/MIR
  package: std.sfm
  code_unit: ordinary SMF
  lifecycle: loader + DynSmfSession
```

- Original SMF-pack proposal conflicts with current SFM capsule ownership.
- Type/runtime facet contracts do not yet exist.
- Reuse `ModuleSurface`, variant resolver helpers, `ObjectProvider`, staged loader generations, and dynSMF evidence/policy.
- Variants stay build-time-only.
- V1 private access goes through owner capability facades.
- First dependency is shared `TypePredicateBytecode`.

