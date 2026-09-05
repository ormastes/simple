# Legacy flat function lowering can replace a present tail with local zero

- **Date:** 2026-08-16
- **Component:** pure-Simple MIR bootstrap compatibility lowering
- **Severity:** high if the dormant path is reactivated
- **Status:** OPEN / TODO (currently unused method)
- **Owner:** `MirLowering.lower_bootstrap_flat_function`

## Problem

`src/compiler/50.mir/_MirLowering/module_lowering.spl` retains a legacy
`lower_bootstrap_flat_function` method that lowers a block to `LocalId?`, tests
`result.?`, then emits:

```text
result ?? LocalId(id: 0)
```

The staged-native mixed-tail defect can preserve optional presence while losing
the `LocalId` payload. If this compatibility method is called again, a present
tail can therefore become `Ret(Copy(l0))`. For pointer/text-returning functions
whose first parameter is numeric, this recreates the exact impossible
float-to-pointer return category fixed in the active `lower_function` owner.

Repository reference search on 2026-08-16 found no caller of this MIR method;
the same-named HIR method in declaration lowering is a different owner. The
dormant method is not widened into the current Stage 3 blocker fix.

## Required fix before reactivation

- Publish and consume a scalar local-id sentinel, matching active
  `lower_function`'s `last_block_result_local_id` contract, or delete the
  unused compatibility method after proving no external/generated consumer.
- Add an executable mixed explicit/implicit text-tail fixture with numeric
  argument local zero.
- Reject any resulting `Ret(Copy(l0))`; do not add a float-to-pointer backend
  conversion and do not patch callers with explicit returns.
- Use an admitted pure-Simple compiler/runtime for acceptance. Rust-seed
  behavior is diagnostic only.
