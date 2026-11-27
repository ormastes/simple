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


---

## Lane disposition 2026-11-13 (p3-misc-b)

open compile-cost concern; owner: SFFI manifest lane.
---

## Lane disposition 2026-11-13 (live-p3-l4, work/live-p3-l4-20261113, base f790f7f266e)

Concurs with p3-misc-b: the required resolution (focused native-build cache preservation/reuse, not compiling unrelated test-runner/compiler modules for the leaf spec, separate setup/compile/link/execution timing, verifier kept on the admission path) is a native-test-infrastructure performance program for the SFFI manifest lane. Attempting to reproduce the 6-minute native compile on this Windows interpreter host would measure this host, not the fix. No in-lane change. Owner: SFFI manifest lane.
