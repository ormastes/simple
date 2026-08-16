# Guarded-Command Contract — the one write sequence, every enterprise vertical

Every external mutation in the Simple Enterprise Suite runs ONE frozen
sequence. This document is the canonical statement of it, and
`test/01_unit/lib/nogc_sync_mut/enterprise_conformance_spec.spl` is the
executable gate that enforces it across all nine modules.

The spec proves the contract by **driving the real commands** against a real
store and reading the resulting rows. It contains no source-text or grep
assertions — those are banned as evidence in this repo, and they are also
useless here: the defect this contract exists to prevent is an *ordering*
bug that reads identically in source to a correct implementation.

## 1. Rung order

```
1. session      -> invalid-session
2. rbac         -> forbidden
3. validation   -> invalid-record / not-found / ...
4. idempotency  -> duplicate-key (replay: return the RECORDED result)
5. effects      -> all writes in ONE unit of work
```

## 2. The replay rule (the rule everyone gets wrong)

> **A rung whose predicate reads state that this command's own first
> execution changed must NOT be evaluated for a replayed command.**

Split rung 3 into two kinds:

| kind | example | placement |
|------|---------|-----------|
| **state-independent** (identity/shape) | `not-found` for an unknown PO, `line-not-found`, empty id, qty <= 0, bad signature | BEFORE the idempotency rung, unconditional |
| **state-dependent** (feasibility) | "must still be `created`", "table must be free", "no open punch", "employee must not exist", over-receipt remaining | AFTER replay detection, gated on a fresh command |

Getting this backwards means a replay is answered with a DENIAL
(`invalid-transition`, `conflict`, `table-occupied`, `session-closed`,
`insufficient-stock`, `invalid-record`) for a command that was in fact
**accepted** — the caller retries a succeeded write and is told it failed.

The canonical shape:

```simple
val replayed = idempotency_seen(store, tenant.tenant_id, envelope.idempotency_key)
if not replayed and <state-dependent feasibility>:
    return denied("<closed-set reason>", detail)
if replayed:
    return CommandResult(ok: true, reason: "duplicate-key",
                         detail: idempotency_result(store, tenant.tenant_id, envelope.idempotency_key))
# effects, one uow
```

Note what this does NOT change: the same command issued twice with a
**fresh** idempotency key still hits the feasibility rung and is still
denied. Only a genuine replay is short-circuited.

`enterprise_procurement/procurement.spl` (`proc_receive`,
`proc_invoice_record`) is the reference implementation of this shape.

## 3. The one-UoW rule

The domain rows, the outbox event, the audit record, and the idempotency key
are written between one `uow_begin` and one `uow_commit`. A replay therefore
produces exactly one effect, and a rollback produces none. Atomicity is real
only on an ACID backend; `store_open` probes and records `acid` honestly (see
`enterprise_store/store.spl`).

Admin/setup commands (`sale_add_product`, `sale_receive_stock`,
`booking_create_resource`, `proc_supplier_add`, `channel_register`,
`channel_kill`, `channel_list_product`, `credential_seed`) are a deliberate
sub-shape: session + rbac + validation + write + audit, with **no** envelope,
no idempotency key, and no outbox event. They are not idempotent by
construction and callers must not treat them as such.

## 4. Closed reason set

`enterprise_sale/foundation.spl` owns the set, and `reason_allowed(reason)`
is its **executable** form — the conformance spec asserts membership by
calling that predicate, never by reading prose:

```
accepted | invalid-session | forbidden | invalid-record | duplicate-key |
insufficient-stock | not-found | store-error | conflict | table-occupied |
no-session | session-closed | invalid-transition | unserved-lines |
line-not-found | invalid-credentials
```

Adding a reason requires an ADR plus an edit to `reason_set()`; the spec
pins the list at 16 members so a silent addition fails.

## 5. Tenant scoping

The tenant on the SESSION is the authority; a tenant id inside a payload is
never trusted. Every read a command performs filters by `tenant.tenant_id`
**in pure Simple**, never in SQL — the interpreter's rt_sqlite emulation
ignores WHERE equality, so SQL-side filtering would silently return other
tenants' rows there (see `enterprise_store/store.spl` § Backend honesty).

## 6. Conformance matrix

Audited 2026-08-16 (lane W7-B). Columns:
**a** rung order as implemented ·
**b** all effects in one UoW ·
**c** replay returns the recorded result ·
**d** denials inside the closed set ·
**e** tenant scoping in pure Simple on every read.

`FIXED` = drift found by this audit and repaired in the same change.

| Module | Command | a | b | c | d | e |
|---|---|---|---|---|---|---|
| goods_sale | `sale_place_order` | ok | ok | **W7-A** | ok | ok |
| goods_sale | `sale_pay_order` | ok | ok | **W7-A** | ok | ok |
| goods_sale | `sale_refund_order` | ok | ok | **W7-A** | ok | ok |
| goods_sale | `sale_add_product` / `sale_receive_stock` | admin sub-shape | n/a | n/a | ok | ok |
| booking | `booking_hold` | ok | ok | ok (self-excluded overlap) | ok | ok |
| booking | `booking_confirm` | FIXED | ok | FIXED | ok | ok |
| booking | `booking_cancel` | FIXED | ok | FIXED | ok | ok |
| booking | `booking_no_show` | FIXED | ok | FIXED | ok | ok |
| booking | `booking_create_resource` | admin sub-shape | n/a | n/a | ok | ok |
| restaurant | `table_open_session` | FIXED | ok | FIXED | ok | ok |
| restaurant | `order_add_line` | ok | ok | ok | ok | ok |
| restaurant | `line_transition` (ready/serve/void) | FIXED | ok | FIXED | ok | ok |
| restaurant | `bill_close_session` | FIXED | ok | FIXED | ok | ok |
| payment | `payment_create_intent` | FIXED | ok | FIXED | ok | ok |
| payment | `payment_webhook_receive` | ok | ok | ok (dedupes on `provider_event_id`) | ok | ok |
| hcm | `hcm_hire` | FIXED | ok | FIXED | ok | ok |
| hcm | `hcm_contract_amend` | ok | ok | ok | ok | ok |
| hcm | `hcm_terminate` | FIXED | ok | FIXED | ok | ok |
| hcm | `hcm_clock_in` | FIXED | ok (audit only, no outbox) | FIXED | ok | ok |
| hcm | `hcm_clock_out` | FIXED | ok (audit only, no outbox) | FIXED | ok | ok |
| hcm | `hcm_leave_request` | FIXED | ok | FIXED | ok | ok |
| hcm | `hcm_leave_decide` | FIXED | ok | FIXED | ok | ok |
| procurement | `proc_requisition_create` | ok | ok | ok | ok | ok |
| procurement | `proc_requisition_approve` | FIXED | ok | FIXED | ok | ok |
| procurement | `proc_po_create` | ok | ok | ok (PO creation does not move the req status) | ok | ok |
| procurement | `proc_receive` | ok (reference) | ok | ok (reference) | ok | ok |
| procurement | `proc_invoice_record` | ok (reference) | ok | ok (reference) | ok | ok |
| procurement | `proc_supplier_add` | admin sub-shape | n/a | n/a | ok | ok |
| channel | `channel_import_orders` | ok | ok per order | ok (inbox dedup on external id + sale key) | ok | ok |
| channel | `channel_ack_order` | ok | ok (acks + audit, no outbox) | ok (ack row is the dedup) | ok | ok |
| channel | `channel_register` / `channel_kill` / `channel_list_product` | admin sub-shape | n/a | n/a | ok | ok |
| outbox | `outbox_dispatch_batch` | worker, not a guarded command | ok (dispatch + audit) | ok (dispatch row is the dedup) | n/a | ok |
| session | `session_issue` | credential-guarded, not session-guarded | ok (row + audit, no outbox) | n/a (issuance is not replayable) | ok (`invalid-credentials`) | ok |
| session | `credential_seed` | admin sub-shape | n/a | n/a | ok | ok |

### Notes on the non-drift entries

- `booking_hold`'s overlap check excludes the candidate booking itself, so it
  is already replay-stable: after acceptance the invariant "total overlapping
  qty <= capacity" holds, and excluding self keeps it holding.
- `hcm_leave_decide`'s overlap check likewise excludes the leave under
  decision. Its *status* rung was the drift, not the overlap rung.
- `session_issue` denies with `invalid-credentials` for BOTH an unknown actor
  and a wrong secret — deliberately generic, so there is no user-enumeration
  channel. This audit legitimised that reason by adding it to the closed set
  rather than weakening the denial.

## 7. Open item for lane W7-A

`enterprise_sale/goods_sale.spl` carries the same defect in three commands
and is owned by lane W7-A while this audit ran, so it was **not edited
here**:

- `sale_place_order` — `sale_available_stock(...) < qty` is evaluated before
  replay detection. The order's own `reserve` movement decreased that stock,
  so a replay can be denied `insufficient-stock` for an order that was
  accepted. (This is the originally reported defect.)
- `sale_pay_order` — `sale_order_status(...) != "created"` before replay
  detection. After payment the status is `paid`, so a replay is denied
  `invalid-record`.
- `sale_refund_order` — same shape: after the refund the status is
  `refunded`, so a replay is denied `invalid-record`.

`sale_pay_order` and `sale_refund_order` were **not** in the original report
and are additional findings from this audit.

When W7-A lands, add three replay rows to the conformance spec — a
`goods_sale` example asserting `duplicate-key` plus an unchanged effect
fingerprint for place/pay/refund — and change the three `W7-A` cells in the
matrix above to `ok`. The spec's deliberate scope gap is documented in its
own docstring.
