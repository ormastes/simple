# HCM — employee, contract, attendance, leave, payroll BOUNDARY

`std.enterprise_hcm` (impl: `src/lib/nogc_sync_mut/enterprise_hcm/hcm.spl`) is the
safer-first-release human-capital vertical of the Simple Enterprise Suite
(lane `.spipe/simple_enterprise_suite`, W6-A). It builds on exactly two modules —
`std.enterprise_store` (durable store, UoW, idempotency, audit, outbox) and
`std.enterprise_sale.foundation` (tenant/actor/session contexts, RBAC, the frozen
closed set of denial reasons) — and copies the goods-sale guarded sequence verbatim.

## The payroll boundary (read this first)

**There is no payroll engine here, and there will not be one in this module.**
`hcm_payroll_export` emits calculation **INPUT** rows for an external payroll
system:

```
employee_id|wage_cents_per_hour|worked_seconds|approved_leave_days
```

- `wage_cents_per_hour` — the contract-effective wage at `period_end`.
- `worked_seconds` — sum of **CLOSED** clock-in/clock-out intervals, clipped to
  `[period_start, period_end)`. An interval still open contributes nothing.
- `approved_leave_days` — approved-leave seconds in the same window / 86400.

No gross pay, no net pay, no tax, no deduction, no jurisdiction rule is computed.
Consuming this export and calling the result "payroll" is a misuse. A **Korean
payroll/tax pack is a future, separately reviewed lane** — nothing in this module
anticipates or partially implements it.

## Guarded sequence

Every write runs the frozen sequence in one unit of work:

```
session_valid -> role_allows -> domain validation -> idempotency -> effects (UoW)
```

Effects always include the domain rows plus `audit_append`, and `outbox_append`
for lifecycle/leave events, plus `idempotency_record`. A replayed idempotency key
returns `ok=true, reason="duplicate-key"` with the original detail and produces
zero new effects. Role `hcm` was added to `role_allows`; `admin` passes via the
existing blanket rule.

## Commands

| Command | Notes |
|---------|-------|
| `hcm_hire` | employee `hired` event + first effective-dated contract row |
| `hcm_contract_amend` | appends a **NEW** effective-dated row — never a mutation |
| `hcm_terminate` | appends a `terminated` event carrying the end epoch |
| `hcm_clock_in` / `hcm_clock_out` | caller-supplied `now_epoch` punches |
| `hcm_leave_request` | range + type |
| `hcm_leave_decide` | admin-tier approve/deny |

Reads: `hcm_employee_status`, `hcm_contract_count`, `hcm_wage_at`,
`hcm_time_entries`, `hcm_worked_seconds`, `hcm_leave_status`,
`hcm_leave_balance`, `hcm_payroll_export`.

## Rules the design enforces

- **Insert-only.** Contracts are effective-dated rows; the row with the greatest
  `effective_epoch <= now` wins. History never shrinks or is rewritten, and stays
  readable after termination.
- **Terminated is a fence.** Further non-read commands for that employee are
  denied `invalid-transition`; reads keep working.
- **Attendance transitions.** A second clock-in while one is open, and a
  clock-out with nothing open, are both `invalid-transition`.
- **Leave overlap.** Approving a range that overlaps an already-**approved** leave
  of the same employee is denied `conflict`. Adjacent (touching, non-overlapping)
  ranges approve fine.
- **No wall-clock reads.** Every epoch is caller-supplied, which is what makes
  the payroll oracle in the spec reproducible.
- **No module-global mutable state**; filtering is pure Simple over `store_rows`.
- **Closed reason set reused as-is** — this vertical added no new denial reason.

## Evidence

- Spec: `test/03_system/app/enterprise/hcm_vertical_spec.spl` (8 examples), which
  checks the export against a **hand-computed absolute oracle**, not values
  derived from the code under test.
- Generated doc: `doc/06_spec/03_system/app/enterprise/hcm_vertical_spec.md`.
- Cross-OS: `src/app/enterprise/hcm_probe_main.spl` is covered by
  `sh scripts/check/check-enterprise-cross-os.shs` (host + `x86_64-unknown-simpleos`).

See also: `doc/07_guide/lib/database/enterprise_store.md`,
`doc/07_guide/app/enterprise/booking.md`.
