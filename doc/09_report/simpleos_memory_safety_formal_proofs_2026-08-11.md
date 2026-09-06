# SimpleOS Memory-Safety Formal-Proof Evidence — 2026-08-11

Status: **PASS**

## Authoritative producer

```sh
sh scripts/check/check-simpleos-memory-safety-formal-proofs.shs
```

The producer exited `0` on 2026-08-11 and ended with
`STATUS: PASS simpleos-memory-safety-formal-proofs`.

## Retained evidence

- Log: `build/evidence/mci-v2/formal-memory-20260811/memory_safety_formal.log`
- Log SHA-256: `c72caf9a01ae23fdac34560a452632170a0ee732fa4f6e281ce5968bcf7dd81b`
- Log size: 1095 bytes
- `verification/gc_reachability`: PASS, 1 Lean file, 0 trust bypasses
- `verification/gc_boundary`: PASS, 4 Lean files, 0 trust bypasses
- `verification/gc_manual_borrow`: PASS, 2 Lean files, 0 trust bypasses
- `verification/manual_pointer_borrow`: PASS, 2 Lean files, 0 trust bypasses
- `verification/nogc_compile`: PASS, 2 Lean files, 0 trust bypasses

The wrapper also ran the Lean-proof negative self-test and required the named
GC reachability, GC/no-allocation boundary, manual-borrow, pointer-borrow, and
no-GC compilation theorems after successful project builds.

## Claim boundary

This proves the current host-independent Lean memory-safety models and named
theorem-presence gate only. It does not prove native runtime/code-generation
semantic correspondence, real concurrent execution, native/QEMU behavior,
hardware behavior, the full 26-row hardening matrix, or mission-critical
release readiness.
