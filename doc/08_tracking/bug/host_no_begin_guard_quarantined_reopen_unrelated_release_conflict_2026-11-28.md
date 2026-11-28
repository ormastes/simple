# no-BEGIN guard spec vs quarantined reopen: unrelated no-effect release stays Uncertain (2026-11-28)

**Status:** resolved 2026-11-28 — owner decision: keep product behaviour (`750356ce7c6`), correct the spec. Not a seed defect.
**Spec:** `test/03_system/app/orchestrator/feature/host_runtime_exec_no_begin_guard_spec.spl`
example "reopens exact parent completion with qualified child and preserves
unrelated no-effect release" (5/6 on the Rust seed interpreter, diagnostic).

## Evidence (instrumented one-example copy, Rust seed interpreter, diagnostic, 98 s)

After `host_capacity_owner_open_quarantined_owned_v2`:

```
parent=true unrelated=false rows=2
row operation_1       Released
row unrelated-parent  Uncertain
```

`assert(unrelated_released)` (spec line 163) is the failing assert.

## Cause

`host_capacity_owner_open_internal_v1` / owned v2 projection
(`src/lib/nogc_sync_mut/orchestration/host_capacity_owner_v1.spl`, the
`elif quarantine_previous:` arm, from `750356ce7c6` "quarantine prior service
fences without releasing capacity", 2026-11-07) marks every row without a
completion proof Uncertain on a quarantined reopen, including an
admitted->cancelled row whose outcome equals the abort outcome. The
cancelled/no-effect release arm requires `continuity_proven`, which a
quarantined open never has. Release of such rows is done later by
`host_service_reconciliation_v2` (`no_effect` path) after a native inventory.

The spec (`316d0e2cecf`, 2026-11-08, landed NOT_RUN) and its design note state
"Unrelated sibling reservation may release through its own existing no-effect
proof" on the owned quarantined reopen itself.

## Resolution (owner decision 2026-11-28)

Keep the product behaviour from `750356ce7c6`: under quarantine the runtime
refuses to release state it cannot verify, so the unrelated admitted->cancelled
row stays `Uncertain` (and charged) after `host_capacity_owner_open_quarantined_owned_v2`.
The spec from `316d0e2cecf` was wrong to expect release on the quarantined open.

Spec change (same example, renamed to "... keeps unrelated no-effect
quarantined, releases it on continuity reopen"):

- after the quarantined reopen it asserts parent `Released`, unrelated
  `Uncertain`, both rows present, and available memory = capacity - 1;
- it then closes and reopens through the documented non-quarantine path,
  `host_capacity_owner_open_owned_v2(..., continuity_proven=true)` (the
  `cancelled` + exact abort outcome + no child barrier arm), and asserts the
  unrelated row `Released`, parent still `Released`, full capacity available
  and cleanup still settled — so release is still proven, on the path that has
  continuity.
