# SFFI manifest-signature native test compile cost

Status: Open

## Observation

On 2026-08-21, the focused command

```text
simple test test/01_unit/os/kernel/loader/executable_manifest_signature_verifier_spec.spl --mode=native
```

recompiled a broad compiler/test-runner closure. Two attempts consumed sustained
CPU for more than six minutes; the final attempt was terminated under the
mandatory runaway guard. The first completed compile reached the fixture in
roughly four minutes and reported a fixture-only HIR issue, demonstrating that
the dominant cost occurs before Ed25519 test execution.

## Required resolution

- preserve and reuse the focused native-build cache;
- avoid compiling unrelated test-runner/compiler modules for this leaf spec;
- report setup, compile, link, and execution time separately;
- keep the manifest verifier on the admission path only;
- retain the static signed golden vector so tests never generate Ed25519 keys or
  signatures at runtime.

This performance gap blocks a native PASS claim for the new verifier. It does
not permit falling back to caller-supplied verification booleans or moving
signature verification into the per-call SFFI hot path.
