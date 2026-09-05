# Enterprise Payment — Provider Boundary Guide

Module: `std.enterprise_payment` (`src/lib/nogc_sync_mut/enterprise_payment/payment.spl`)
Lane: `.spipe/simple_enterprise_suite` W5-B — design
`doc/01_research/app/enterprise/simple_enterprise_suite_full_design_2026-08-14.md` §7.1, §7.2, §10.2.

## PCI posture — hosted provider assumed, no card data

Card entry happens on the payment provider's hosted page. **No PAN, CVV, or
any card data ever transits or is stored by this system** — the store holds
only intent ids, provider references, event kinds, statuses, and
provider_event_ids. Webhook payloads are opaque text used solely for
signature verification and are never persisted.

## Signature scheme — explicitly a stand-in

`PaymentProvider` verifies `sha256(shared_secret + "|" + payload)` via the
repo's own `std.common.crypto.sha256`. This is an HMAC-style shared-secret
stand-in for real provider SDK verification (e.g. Stripe's HMAC-SHA256
`t=..,v1=..` scheme). Swapping in a real provider replaces only this
composition seam. **It is not PCI-DSS evidence** — the PCI posture rests on
the hosted-provider assumption above, not on this check.

## Lifecycle

```
payment_create_intent  -> pending      (caller receives provider_ref)
webhook authorized     -> authorized   (from pending)
webhook captured       -> captured     (from pending|authorized) + sale_pay_order in the SAME uow
webhook failed         -> failed       (from pending|authorized; order untouched)
```

- Event rows are insert-only; status is derived from the event stream.
- Guarded sequence copied from goods_sale: session -> rbac -> validation ->
  idempotency -> effects in one unit of work. For webhooks the
  provider_event_id dedupe runs before the transition rung, so a replayed
  webhook returns the recorded result (`duplicate-key`) with exactly one
  effect.
- Bad signature: `invalid-record`, no state change of any kind.
- Provider interaction (redirect/SDK/hosted page) is outside this module.

## Reconciliation (§7.2)

`payment_reconcile(store, tenant_id, now, ttl_seconds)` returns a
`PaymentReconcileReport` with three divergence classes:
`pending_over_ttl`, `captured_without_paid_order`,
`paid_order_without_captured_intent`.

## Spec

`test/03_system/app/enterprise/payment_boundary_spec.spl` (7 scenarios,
generated doc under `doc/06_spec/`). Verified red-first on the signature
check: with verification disabled the bad-signature scenario fails.
