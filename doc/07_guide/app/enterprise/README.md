# Enterprise Suite — Contract Surface, Verticals, and Coherence

This is the index and coherence overview for the Simple Enterprise Suite. The
suite is a set of multi-tenant business **verticals** that all consume ONE
frozen contract layer and one durable store. Per-vertical detail lives in the
sibling pages (`booking.md`, `restaurant.md`, `payment.md`, …); this page is the
map, the invariants, and the verification story.

Lane state: `.spipe/simple_enterprise_suite/state.md`.
Freshness owner: lane W19-C (interface-hardening + doc-freshness gate).

---

## 1. The frozen contract surface

`src/lib/nogc_sync_mut/enterprise_sale/foundation.spl` is **FROZEN** — changes
require an ADR + compatibility review. It defines:

| Contract | Shape | Rule |
|---|---|---|
| `TenantContext` / `ActorContext` / `SessionContext` | identity + tenancy | The tenant on the **session** is authority; a tenant id inside a payload is never trusted. |
| `CommandEnvelope` | request id, idempotency key, action, opaque payload | Every external mutation is one envelope. |
| `CommandResult` | `ok`, `reason`, `detail` | `reason` is a member of the **closed set** below; nothing else. |
| `Money` | `amount_cents: i64` + currency | Integer minor units, never floats. |
| `session_valid` | session active ∧ tenant matches authority ∧ actor matches ∧ token non-empty | Rung 1 of every guarded write. |
| `role_allows` | data-driven role→action policy | Rung 2. Registry-driven RBAC (`rbac_registry.spl`) is the same policy, table-form. |
| `reason_set()` / `reason_allowed()` | the closed reason set, and its **executable** membership oracle | Specs assert membership by CALLING `reason_allowed`, never by grepping prose. |

**The closed reason set (16 members):**
`accepted`, `invalid-session`, `forbidden`, `invalid-record`, `duplicate-key`,
`insufficient-stock`, `not-found`, `store-error`, `conflict`, `table-occupied`,
`no-session`, `session-closed`, `invalid-transition`, `unserved-lines`,
`line-not-found`, `invalid-credentials`.

---

## 2. The guarded-command sequence (the one contract every vertical copies)

Every external mutation runs the SAME five rungs in the SAME order, inside one
unit of work:

```
session  ->  rbac  ->  domain validation  ->  idempotency  ->  effects
```

1. **session** — `session_valid(session, tenant, who)`; else `invalid-session`.
2. **rbac** — `role_allows(who.role, action)` (or the registry); else `forbidden`.
3. **validation** — domain preconditions; `invalid-record` / `not-found` /
   `insufficient-stock` / `invalid-transition` / etc.
4. **idempotency** — `idempotency_seen`; a replay of the same key returns the
   RECORDED result as `duplicate-key`, never a re-evaluation of now-changed
   state. State-dependent rungs must sit behind `if not replayed:`; identity
   checks (`not-found`) stay unconditional.
5. **effects** — durable writes + outbox row + audit row, one UoW, committed
   atomically.

Detail and the drift class this prevents:
`guarded_command_contract.md`, `replay_and_state_dependent_validation.md`.

---

## 3. Vertical catalog (current tree, HEAD 2026-08-17)

| Vertical | Module | Guarded actions (RBAC role) |
|---|---|---|
| Goods sale | `enterprise_sale/goods_sale.spl` | catalog/stock admin, `sale.order.place/pay/refund` (sales) |
| Booking | `enterprise_booking/booking.spl` | `booking.hold/confirm/cancel/no_show` (booking) |
| Restaurant | `enterprise_restaurant/restaurant.spl` | table open, add line, kitchen ready, serve, bill close |
| Payment | `enterprise_payment/payment.spl` | `payment.intent.create`, `payment.webhook.receive` (payments) |
| HCM | `enterprise_hcm/hcm.spl` | hire/amend/terminate, clock in/out, leave request/decide |
| Procurement | `enterprise_procurement/procurement.spl` | requisition → PO → receive → invoice (procurement) |
| Finance | `enterprise_finance/finance.spl` + `finance_async.spl` | `finance.period.close`, `finance.journal.post`; reports are pure reads |
| Outbox worker | `enterprise_outbox/outbox_worker.spl` | background exactly-once dispatch (no session rung; driven by store rows) |
| Channel hub | `enterprise_channel/channel_hub.spl` | external marketplace adapters, inbox dedup, checkpoints (channel.admin) |
| Session | `enterprise_session/{session,throttle}.spl` | credential seed (guarded) + issuance (unauthenticated, non-enumerating) |

**Landing in parallel, NOT yet in this tree:** CRM and fulfillment verticals are
being authored by other lanes and are absent at this HEAD. Inventory and
finance-reporting are surfaced *within* goods-sale/procurement (stock ledger) and
finance (trial balance / AR / AP), not as separate modules yet. When CRM /
fulfillment land they MUST consume the same frozen `foundation` contract, run
the five-rung sequence, and route hashing through the facade — add their rows to
the matrix in §5 and to the conformance spec's sweep.

---

## 4. The durable-store model

`src/lib/nogc_sync_mut/enterprise_store/`:

- `store.spl` — migrations, unit-of-work (`uow_begin`/`uow_rollback`),
  idempotency table, outbox rows, tenant filtering, `StoreFaults` seam.
- `records.spl` — row helpers + the finance period-lock seam
  (`journal_post_allowed`). Sale/restaurant journal posting are thin wrappers,
  so both inherit the finance lock.
- `file_backend.spl` — `SPLSTORE1` backend used when sqlite is unavailable
  (including SimpleOS).
- `audit_hash.spl` — the **cross-OS SHA-256 facade** (`audit_sha256_hex`) and
  the audit chain (`audit_verify_chain`).

Every effect writes an outbox row and an audit row; the audit row is
`sha256(prev_hash | tenant | actor | action | detail)`, chained per tenant.

---

## 5. Coherence matrix (vertical × invariant) — W19-C audit, HEAD 2026-08-17

Audited by reading the code. `PASS` = verified; `N/A` = rung not applicable to
that module's shape; `VIOLATION` = concrete finding (owner + fix in §6).

| Vertical | A. Closed reason set | B. Five-rung sequence | C. Cross-OS hashing facade |
|---|---|---|---|
| goods_sale | PASS | PASS | N/A (no hashing; audit via store facade) |
| booking | PASS | PASS | N/A |
| restaurant | PASS | PASS | N/A |
| payment | PASS | PASS | **VIOLATION — W19-C-1** |
| hcm | PASS | PASS | N/A |
| procurement | PASS | PASS | N/A |
| finance | PASS | PASS | N/A |
| outbox worker | PASS | N/A (background dispatcher; exactly-once via outbox rows) | N/A |
| channel hub | PASS | PASS | N/A |
| session | PASS | PASS (issuance is the deliberate unauthenticated path) | PASS (routes via `audit_sha256_hex`) |
| store (audit chain) | — | — | PASS (`audit_hash.audit_sha256_hex`) |

**A. Closed reason set** — every `denied(...)` literal and every direct
`CommandResult(...)` construction across the suite uses a member of
`reason_set()`; no out-of-set reason exists. `duplicate-key` is emitted as a
direct `CommandResult` (the recorded-result replay path); `channel_hub`'s
`ImportReport.import_denied` is a *different* report type, not a `CommandResult`.

**B. Five-rung sequence** — `session_valid` precedes `role_allows`, which
precedes domain validation, which precedes `idempotency_seen`, in every guarded
command of every vertical. Verified line-ordered per file.

**C. Cross-OS hashing facade** — audit/credential hashing must route through
`audit_sha256_hex`, NOT `std.common.crypto.sha256` directly. The store and the
session vertical comply. Payment does not (§6).

---

## 6. Findings

### W19-C-1 — payment vertical bypasses the SHA-256 facade (open; owner: payment lane)

`src/lib/nogc_sync_mut/enterprise_payment/payment.spl:59` imports
`std.common.crypto.sha256.{sha256_text}` and `:78` (`provider_sign`, used by
`provider_verify` / `provider_verify_webhook`) calls it directly. This is the
exact cross-OS invariant the facade exists to enforce: `sha256_text` drags
slice / `[v; n]` `CollectionOps` into the compile closure that standalone-SMF
(SimpleOS) codegen rejects (`audit_hash.spl` header). Consequence: the payment
vertical will not build standalone-SMF. It does **not** corrupt the audit chain
— payment's own audit rows still route through the store facade — so the impact
is build-portability, not data integrity.

**Fix (payment lane, not W19-C):** replace the import with
`std.nogc_sync_mut.enterprise_store.audit_hash.{audit_sha256_hex}` and call
`audit_sha256_hex` in `provider_sign`. The facade is digest-identical to
`sha256_text` (pinned by the conformance spec), so the swap is provably
signature-preserving — existing webhook signatures stay valid.

---

## 7. Verification guards

| Guard | What it proves | Where |
|---|---|---|
| **Guarded-command conformance** | replay → `duplicate-key` with one effect; closed reason set; tenant scoping — by DRIVING real flows | `test/01_unit/lib/nogc_sync_mut/enterprise_conformance_spec.spl` |
| **Interface conformance** (W19-C) | closed reason set (with reproduce-first bite) + cross-OS facade digest-identity, at the contract layer | `test/01_unit/lib/nogc_sync_mut/enterprise_interface_conformance_spec.spl` |
| **RBAC registry equivalence** | the data-driven registry equals `role_allows` | `test/01_unit/lib/nogc_sync_mut/enterprise_rbac_registry_equivalence_spec.spl` |
| **Store app / store** | durable-store behavior, backends, faults | `store_app.md`, `enterprise_store/` specs |

None of these use grep/source-text as evidence: membership is asserted by
CALLING `reason_allowed`, the sequence by driving commands and reading rows, the
facade by known-answer vectors and digest-equality against `sha256_text`. The
interface spec's **reproduce-first bite**: `reason_allowed("__spec_bogus_reason__")`
and the case/underscore variants must be `false`; widen the set to admit any of
them and that scenario goes red.
