<!-- codex-design -->
# Architecture: SFFI v2 admission acceptance

## Capsule boundary

`SffiAdmissionAcceptance` is a test-only orchestration capsule over existing
admission primitives. It owns fixture discovery, one admission invocation,
typed result normalization, and receipt inspection. It does not duplicate
crypto/signature parsing or mutate provider loading behavior.

```text
fixture artifact + manifest + trust store + receipt
        -> existing evidence-admission checker
        -> typed acceptance result
        -> modern SSpec scenario / CI receipt
```

## Invariants

- Fixture labels map to declared expected categories; unknown labels fail.
- The runner calls admission once per fixture and records its exact exit/result.
- A successful fixture must bind the expected artifact and provider identity.
- A rejected fixture must name a stable rejection class, not return a fabricated
  valid value.
- The runtime call path is outside this capsule; it receives only admitted,
  cached typed slots.

## MDSOC decision

No runtime feature transform is needed. This is a test/tool virtual capsule
because it composes audit, receipt, and SSpec concerns without adding a second
loader or provider registry.
