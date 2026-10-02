# Logical collection-plan validation

Source: `test/01_unit/compiler/semantics/collection_plan_spec.spl`.
Requirement: REQ-007. This is an authored companion, not generated test evidence.
Execution and admitted `spipe-docgen` verification remain pending.

## Scenarios

| Scenario | Production behavior and oracle |
|---|---|
| Source followed by filter | A typed, bound source followed by a backward-only unary filter validates successfully. |
| Invalid edge and arity | A self-reference and a join with one input each fail structural validation. |
| Root and node identity | An out-of-range output and a node ID differing from its position each fail. |
| Missing bindings and disconnected nodes | Missing source expression, missing operation symbol, and an unused source each fail. |
| Missing key and nonfinal output | A structurally valid DistinctBy plan reports missing key evidence; a nonfinal output fails validation. |
| Missing rewrite evidence | Deliberately absent output type/source binding are reported together with unknown legality facts. |
| Index key and symbol | Deliberately absent index key and operation symbol remain explicit blockers. |
| Existing bindings | Supplied output type/source expression/operation symbol are not reported missing; independent alias/key blockers remain. |

## Fixture correction (2026-10-03)

The shared node builder supplies an output type, a source expression for Source,
and a symbol for operations. Two negative tests previously expected these
populated fields to be missing. They now clear the relevant fields explicitly;
the new positive controls reject an implementation that reports every binding
missing regardless of input. Production behavior was not changed.

These unit scenarios do not prove production extraction, MIR lowering, backend
execution, callback semantics, or any NFR. The full CP-007 acceptance rows remain
in `doc/03_plan/sys_test/collection_planner.md` and are not closed here.
