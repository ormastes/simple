# Local Research: Parallel Ownership and Storage Layout

Baseline inspected: `ddfcfbea806cb2dc0f2fbc311bb922962a0ea29c` on 2026-08-12.

- `src/lib/common/structural/mutation/` already owns deterministic mutation-plan and conflict vocabulary.
- `src/lib/common/structural/placement/` owns frozen placement/lease wire records, while `src/lib/common/compute/placement_contracts/` owns semantic placement carriers.
- No existing `TransferEnvelopeV1`, `StorageLayoutPlanV1`, or general parallel-commit common contract was found in owned source paths at inspection.
- `src/compiler_rust/runtime/src/parallel.rs` is a data-parallel kernel surface and must remain separate from ownership-aware application task runtime work.
- Existing borrow and transport paths require their dedicated WP-10 through WP-18 evidence before they can justify no-alias, transfer, or isolation claims.

The first safe implementation slice is common transfer vocabulary plus a unit contract test; runtime codecs, task queues, actor/process migration, and layout lowering remain future work packages.
