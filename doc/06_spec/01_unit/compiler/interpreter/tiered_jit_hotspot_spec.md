# Tiered JIT hotspot lexical fact specification

This unit specification freezes the ordered lexical-fact contract for the
tiered-JIT backend planner. It calls the private fact-build seam and compares
complete arrays against pre-index goldens; membership-only checks are not
enough because downstream plugin order is observable.

## Scope and evidence

| Field | Value |
|---|---|
| Source | `test/01_unit/compiler/interpreter/tiered_jit_hotspot_spec.spl` |
| Importance | critical (weight 3), high (weight 2) |
| Oracle | exact fact arrays and exact skipped decision name/reason pairs |
| Native/JIT handles | none |
| Timing oracle | none |

## Scenarios

### Frozen fact order

The complete fixture exercises loop, fixed-trip, predication, vector, range,
strength-reduction, bounded-scan, and checksum predicates. The expected array
retains profile facts, var facts, scalar proof facts, lexical facts, and the
backend availability fact in that order.

### Raw-substring compatibility

Repeated and overlapping needles, a Unicode code point, and an embedded NUL
remain source bytes presented to the scanner. Comment/string-like text is not
lexed away: the expected result preserves the former `text.contains` behavior.

### Existing fixture parity

The fixed-trip, byte-scan, checksum, and direct-call fixtures assert complete
vectors, preserving the already-established hotspot behavior.

### Backend decision parity

The same fully proven profile is planned for Cranelift and LLVM. Each scenario
asserts recommendation order and every skipped decision’s stable name and
reason, including backend-owned and cost-budget skips.
