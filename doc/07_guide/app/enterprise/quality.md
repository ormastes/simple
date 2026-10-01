# Enterprise Quality — QC inspection and nonconformance

Module: `src/lib/nogc_sync_mut/enterprise_quality/quality.spl`
Spec: `test/01_unit/lib/nogc_sync_mut/enterprise_quality_spec.spl`
Probe: `src/app/enterprise/quality_probe_main.spl`

A standalone quality vertical of the Simple Enterprise Suite. It does not read
or modify `enterprise_manufacturing`, and it never edits the FROZEN
`enterprise_sale/foundation.spl` or `enterprise_sale/rbac_registry.spl`.

## Storage model

Three insert-only tables — there is no `UPDATE` anywhere:

| Table | Columns | Role |
|-------|---------|------|
| `qc_plans` | `tenant_id, plan_id, sample_size, set_by` | a re-plan appends; the LATEST row wins |
| `qc_inspections` | `tenant_id, inspection_id, plan_id, lot_id, measured, verdict, by_actor` | one row per recorded inspection |
| `qc_ncr_events` | `tenant_id, ncr_id, event, detail, by_actor` | the NCR lifecycle as an append-only event log |

Every read is a pure fold filtered on the session's authoritative tenant id, so
tenant B can never observe tenant A's plans, inspections, or NCRs.

## Inspection and the auto-raised NCR

An inspection records a verdict of exactly `pass` or `fail` against an existing
plan (an unknown plan denies `not-found`). A `fail` verdict AUTOMATICALLY
appends the NCR `raised` event in the SAME unit of work as the inspection row —
an inspection can never become durable without its NCR. The NCR id is derived
deterministically as `NCR-<inspection_id>`, so the link needs no extra column
and a replayed idempotency key cannot mint a second NCR.

## NCR lifecycle (derived, never stored)

`ncr_state` folds the event log:

```
none  --raised-->  open  --dispositioned-->  dispositioned  --closed-->  closed
```

Dispositions are exactly `rework`, `scrap`, `use-as-is`. **Closing requires a
recorded disposition**: `ncr_close` on an `open` NCR is denied and the NCR stays
open. Close-out records the signing actor, recoverable via `ncr_closed_by`.

## Denial reasons

`foundation.reason_set` is a CLOSED vocabulary that a vertical never extends, so
domain denials map onto existing members:

| Situation | Reason |
|-----------|--------|
| unknown plan / unknown NCR | `not-found` |
| close without a disposition | `invalid-transition` |
| act on an already-closed NCR | `invalid-transition` |
| bad verdict / disposition / empty id / non-positive sample size | `invalid-record` |
| non-`quality`, non-`admin` actor | `forbidden` |
| replayed idempotency key | `duplicate-key` |

The spec asserts `reason_allowed` on the returned reasons directly.

## RBAC and the frozen sequence

All four guarded commands (`qc_plan_set`, `qc_inspect_record`,
`ncr_disposition_set`, `ncr_close`) reuse the `quality` role via the LOCAL
`quality_role_allows` gate (`admin` passes for everything) and run the frozen
sequence session -> rbac -> validation -> idempotency -> effects in one UoW.
Audit hashing goes only through `records.audit_append`; the module never imports
`std.common.crypto.sha256`.

Lane: `.spipe/simple_enterprise_suite` (W23-FAN, quality).
