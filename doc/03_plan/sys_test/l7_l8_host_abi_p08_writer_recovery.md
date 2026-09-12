# P08 L7/L8 writer and selected-head recovery test plan

Status: authored structural sidecar; physical execution remains
`MissingEvidence`. Base: reconciliation `877fa563005198d464784109f1fdbf84d4953a75`.
Independent reviewer: Astra. Merge owner: `/root`.

## Scope and dependency order

P08 covers only the frozen writer/journal/selected-head recovery rows HABI-01,
HABI-02, HABI-04, HABI-05, HABI-06, HABI-07, and HABI-09. It depends on the
P06 host-ABI and P07 namespace/GC packets. It preserves the existing journal,
CAS, selected-head, reader-pin, lease, and quarantine owners; it adds no
parallel persistence or authority implementation.

The executable suite is
`test/03_system/compiler/cache/l7_l8_host_abi_spec.spl`; its fail-closed
adapters are in
`test/03_system/compiler/cache/fixtures/l7_l8_host_abi_v3.spl`; the mirrored
manual is
`doc/06_spec/03_system/compiler/cache/l7_l8_host_abi_spec.md`.

## Traceability

| HABI row | Requirement(s) | Boundary |
|---|---|---|
| HABI-01 | REQ-CSM-007, REQ-CSM-008 | Same opened descriptor and parent-directory sync |
| HABI-02 | REQ-CSM-007, REQ-CSM-008 | Rename versus directory durability; postmutation `Unknown` |
| HABI-04 | REQ-CSM-008 | Expected old head is distinct from target head |
| HABI-05 | REQ-CSM-009 | Competing head does not become this operation's receipt |
| HABI-06 | REQ-CSM-007, REQ-CSM-008, REQ-CSM-009 | Exact operation recovery after lost acknowledgement |
| HABI-07 | REQ-CSM-007, REQ-CSM-008 | Torn/pruned/ambiguous history stays `Unknown` |
| HABI-09 | REQ-CSM-009, REQ-CSM-012 | Retained scope and complete root protection across cleanup |

## Required evidence

The admitted provider must own temporary-root descriptors, writer epoch,
reader pin, journal append, selected-head replacement, parent-directory sync,
crash/fault boundary, and fresh-process recovery. It must return operation,
generation, manifest, selected-head, journal-prefix, process-identity, and
quarantine receipts from the existing owners. A model, synthetic journal,
caller-issued digest, logical durability result, or Rust seed cannot satisfy a
row. Until then, every adapter fails explicitly with `MissingEvidence` before
mutation.

Run the executable suite and regenerate its manual only after the provider and
runner are independently qualified. No runtime, docgen, power-loss, or
admission result is recorded by this authored plan.
