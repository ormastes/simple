# Enterprise Expense — claims, category caps, tiered approval limits

Expense vertical of the Simple Enterprise Suite. Module:
`src/lib/nogc_sync_mut/enterprise_expense/expense.spl`. Spec:
`test/01_unit/lib/nogc_sync_mut/enterprise_expense_spec.spl`. Probe:
`src/app/enterprise/expense_probe_main.spl`.

It follows the same shape as every other vertical in the suite: the FROZEN
`enterprise_sale/foundation.spl` contracts, the guarded-command sequence
documented in `guarded_command_contract.md`, records/audit through the
`enterprise_store` facade (this module never imports `std.common.crypto.sha256`),
and integer minor units everywhere — no floats.

## Storage model

Two insert-only tables; nothing is ever updated in place, so the state and the
audit trail are the same rows.

| table | columns | fold |
|---|---|---|
| `expense_caps` | `tenant_id, category, cap_cents, set_by` | `expense_cap_cents` — latest row wins, `-1` = uncapped |
| `expense_events` | `tenant_id, claim_id, event, actor_id, category, amount_cents, reason` | `expense_status` (latest non-`line` event), `expense_claim_total` (sum of `line` events), `expense_claim_submitter`, `expense_reject_reason`, `expense_reimbursed_total` |

Every fold filters on the session's authoritative `tenant_id`, so one tenant can
never read or approve another tenant's claims.

## Lifecycle

```
submit ──> submitted ──approve──> approved ──reimburse──> reimbursed
                   └──reject───> rejected
```

Any transition from a state other than the one shown is denied
`invalid-transition` — in particular, reimbursement is reachable only through
approval, and a second reimbursement of an already-reimbursed claim is refused
even under a fresh idempotency key (pay once).

## Approval tier routing

`expense_required_role(total_cents)` routes on the claim TOTAL, inclusive on the
low side:

| claim total (cents) | required approver role |
|---|---|
| <= 50_000 (\$500)    | `manager`   |
| <= 500_000 (\$5,000) | `finance`   |
| > 500_000           | `executive` |

`expense_tier_rank` makes the roles a ladder (`admin` 4 > `executive` 3 >
`finance` 2 > `manager` 1), so a higher tier may approve anything a lower tier
may. An approver below the required tier is denied `forbidden`.

## Per-category cap

`expense_cap_set` records a per-category spend cap (insert-only, latest wins). A
submitted claim whose total exceeds its category's cap is denied
`invalid-record` at the validation rung, before any effect — no partial claim is
written. A total exactly AT the cap is accepted; a category with no cap is
uncapped.

## Segregation of duties

The approver's (and rejecter's) `actor_id` may never equal the claim's
submitter. Self-approval is denied `forbidden` even when the actor holds a role
that meets the required tier, and even for `admin`. The check sits at the rbac
rung, ahead of the tier check.

## Reason vocabulary

Only members of the frozen closed `reason_set()` are returned. The mapping from
domain failure to reason:

| domain failure | reason |
|---|---|
| category cap exceeded / empty reason text / malformed lines | `invalid-record` |
| approver below required tier, or approving own claim | `forbidden` |
| reimbursing a non-approved claim, re-reimbursing | `invalid-transition` |
| unknown claim id | `not-found` |
| claim id already used | `conflict` |

Free-text detail (e.g. `c-t:requires-finance`, `c-sod:segregation-of-duties`,
`c-over:cap-exceeded`) rides on `CommandResult.detail`, never on `reason`.

## RBAC note

The gate is the LOCAL `expense_role_allows`. The frozen `role_allows` table and
`enterprise_sale/rbac_registry.spl` are deliberately untouched — the registry's
equivalence spec is byte-fenced to the frozen table, and adding an expense grant
there would turn it red.

Lane: `.spipe/simple_enterprise_suite` (W23-FAN, expense).
