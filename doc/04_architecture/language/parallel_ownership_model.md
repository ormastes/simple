<!-- codex-design -->
# Parallel Ownership and Parent-Commit Architecture

## Current state

`src/lib/common/structural/mutation/` already owns MutationPlan/receipt conflict vocabulary. `src/lib/common/structural/placement/` owns wire placement and lease vocabulary, while `src/lib/common/compute/placement_contracts/` owns host semantic placement carriers. These must be consumed, never redeclared. Current application transport and borrow paths require the Wave 1 safety gates before they can support optimization claims.

## Target layers

1. `src/lib/common/structural/transfer/` owns frozen transfer records, wire validation, ownership-token semantics, and codecs.
2. `src/lib/common/structural/storage_layout/` owns frozen storage-plan records and mapping/validation vocabulary.
3. `src/lib/common/structural/parallel_commit/` owns result envelopes, ordering/conflict vocabulary, and receipts; it consumes mutation contracts rather than replacing them.
4. Compiler HIR/MIR/borrow layers derive facts and emit semantic operations; they do not own wire enums.
5. Runtime `parallel_app/` implements bounded transport, structured task lifecycle, and receipt capture behind the common contracts.
6. `src/compiler/85.mdsoc/` adapts the common contracts to stage routing; it may not define competing task/transfer/layout types.

## Ownership flow

```text
Owner Snapshot N --FrozenShare/ObjectRef/Copy--> Child task/process
ChildFresh task arena --IsolatedMove/MutationPlan--> bounded result transport
bounded transport --> owner validation/order/conflict/apply --> Snapshot N+1
```

`Local(owner, generation)` may freeze, begin move, begin scoped loan, or free. A move enters `InTransit`; receipt creates `Local(destination, generation + 1)`. A loan returns only at structured scope join. Source access after move is invalid. Device and process boundaries carry a lease/codec/handle, never an ordinary host address.

## Tree encapsulation and visibility

| Raw layer | Common tree node | Public to parent | Public to next-layer sibling |
|---|---|---|---|
| HIR semantics | `structural/transfer` | transfer-class fact | frozen envelope descriptor only |
| MIR/borrow | `structural/storage_layout` | access/projection proof | plan request, never backend storage internals |
| Runtime | `structural/parallel_commit` | receipt and typed failure | commit port only |
| MDSOC adapters | all three common nodes | routed policy/receipt | selected port facade only |

Sibling layers remain tree-private. Any compiler/runtime shared identifier is extracted into one of these common nodes. No new grammar is required: `mut`, `iso`, `move`, attributes, library APIs, and typed policy are the semantic surface.

## Compiler-owned typed storage authority

Physical projection is admitted only from a compiler-private declaration that
binds a final MIR function/base local to one exact compiler-owned raw allocation,
source revision, fixed record schema/capacity, bounds proof, and the canonical
`StorageLayoutPlanV1`. The runtime region remains owned by its allocation
domain; the declaration is metadata evidence, not a second owner.

Ordinary RuntimeValue arrays, external or ABI-pinned storage, address-observed
data, unknown bounds, and unsupported field widths/layouts cannot enter this
route. MIR lowering will eventually consume an admitted declaration and emit
`mir.storage.project_field.v1` plus its site evidence atomically. The driver
module-qualifies and freezes that evidence before cache lookup and parallel
codegen; workers may only read module-local snapshots.

The v1 producer recognizes only one same-block SSA-shaped chain. A canonical
owned-raw marker must bind the base, allocation bytes, logical type, revision,
and element count. The producer independently verifies a constant index range
and exclusive intermediate uses, then emits an address projection followed by
the original typed value load. Allocation markers are consumed as compile-time
evidence and never reach a backend. Logical projections resolve against their
final LocalIds before generic optimization can renumber them.

## Migration order

Freeze contracts and diagnostic names; make boundary/borrow facts authoritative; replace unsafe transport and add bounded task lifecycle; add parent commit; then implement typed storage layouts and MDSOC/project pilots. Performance lowering cannot precede the raw-pointer and alias-soundness gates.
