# MIR Coverage V1 Probe Plan

This executable unit specification freezes the standalone bridge between
coverage sites discovered during lowering and the finalized closure catalog.
It does not add a MIR instruction, change a compiler driver, export a package
surface, or emit backend/runtime calls.

## Contract

A provisional decision probe carries its authored `MirCoverageSiteKeyV1` and a
boolean operand. A provisional condition probe additionally carries the parent
decision site. The operand is intentionally independent of `MirOperand`: it is
either a nonnegative function-local ID or a boolean literal. A later opcode
integration may translate this abstraction only after the complete closure
catalog has assigned IDs.

`mir_coverage_resolve_probe_plan_v1` performs a pure closure resolution. It
requires exactly one provisional probe for every catalog decision and
condition, and exactly one catalog mapping for every provisional probe. It
derives each decision identity with `mir_coverage_site_id_v1(provisional.site)`
and each condition identity with
`mir_coverage_condition_id_v1(provisional.decision, provisional.site)`. It
validates site kinds, parent-bound condition semantic identities, exact
canonical `1..N` runtime IDs,
the unsigned 32-bit ABI bound, canonical record order, condition-parent
identity and runtime ID, parent source/function ownership, parent-span
containment, and boolean operands. Missing, extra, duplicate, zero, gapped,
overflowing, reordered, wrong-kind, owner-conflicting, span-conflicting, or
parent-conflicting mappings fail closed.

Final decision payloads contain the stable semantic ID, assigned decision ID,
and retained operand. Final condition payloads additionally contain the parent
semantic and numeric IDs. Payload arrays are sorted by numeric ID before the
plan is encoded, so provisional discovery order cannot change output. The
canonical `MirCoverageProbePlan-v1` codec uses length-framed fields and retains
operand kind and value without delimiter ambiguity.

## Executable scenarios

The mirrored spec verifies:

1. provisional input permutations resolve to identical canonical text;
2. the result is a bijection with the closure catalog;
3. function-local zero and literal boolean operands survive resolution;
4. missing, extra, and duplicate provisional probes fail closed;
5. sites outside the catalog fail closed;
6. wrong provisional kinds and negative local operands fail closed;
7. condition-parent mismatches fail closed;
8. zero and duplicate catalog mappings fail closed;
9. catalog semantic identity conflicts fail closed;
10. wrong-kind catalog records fail closed;
11. swapped, gapped, overflowing, and noncanonically ordered catalog IDs fail
    closed; and
12. forged cross-function and out-of-parent-span condition records fail closed;
    and
13. a nested condition reparented to a containing outer decision fails both
    catalog validation and provisional resolution.
14. a valid condition resolves to its exact parent-bound semantic identity.

## Deferred integration

`MirInstKind`, lowering insertion, optimizer preservation, driver wiring,
runtime ABI calls, backend emission, and package exports remain separate
changes. Those changes must consume these finalized numeric payloads and must
not recalculate IDs from module order or observed runtime coverage.
