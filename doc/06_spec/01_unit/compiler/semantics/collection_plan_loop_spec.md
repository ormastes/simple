# Canonical typed loop provenance

Authored manual, 2026-10-03; not generated execution evidence. Source:
`test/01_unit/compiler/semantics/collection_plan_loop_spec.spl`.
Nine scenarios exercise partial REQ-007. None has been executed in this session.

| Case | Assertion |
|---|---|
| Typed identity loop | Source -> Map retains original loop, mapped operand and append symbol; no fabricated operation symbol/callback or purity proof. |
| Unsupported dependencies | Accumulator reads, captured bindings, unknown append symbols and labels reject extraction. |
| Region shape | Extra statements and a different final accumulator reject extraction. |
| Exclusive origin | Simultaneous call/loop origins and source-node loop origins reject validation. |
| Stale evidence | Altered append symbol and untyped mapped operand reject validation. |
| Induction type | Forged source boolean array with integer induction mapping rejects extraction. |
| Original body | Replacing only the origin mapping with a typed constant rejects validation. |
| Structural types | Equivalent array types at different source spans remain admissible. |
| Shared collector | An accepted block produces one region and no blocker; append shell is not rediscovered. |

The supported region has a fresh empty array local, one unlabelled for-loop,
one resolved admitted append, and the final accumulator. Source is an independent
typed array variable. Mapping admits only its induction binding or typed scalar
literals. Complete chain/loop equivalence, filters, general expressions, physical
rewrites, engine parity and measured performance remain outside this increment.
