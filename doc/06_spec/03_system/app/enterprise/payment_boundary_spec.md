# Payment Provider Boundary — intents, verified webhooks, reconciliation

> System scenarios for `std.enterprise_payment` (lane `.spipe/simple_enterprise_suite` W5-B): a clerk sells a product, a payments operator creates a payment intent (getting a provider_ref for the hosted provider flow), and provider webhooks — signature-verified and deduplicated by provider_event_id — drive the intent through pending -> authorized -> captured, with the order becoming paid in the SAME unit of work as the capture.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Payment Provider Boundary — intents, verified webhooks, reconciliation

System scenarios for `std.enterprise_payment` (lane `.spipe/simple_enterprise_suite` W5-B): a clerk sells a product, a payments operator creates a payment intent (getting a provider_ref for the hosted provider flow), and provider webhooks — signature-verified and deduplicated by provider_event_id — drive the intent through pending -> authorized -> captured, with the order becoming paid in the SAME unit of work as the capture.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/01_research/app/enterprise/simple_enterprise_suite_full_design_2026-08-14.md §7.1, §7.2, §10.2 |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/03_system/app/enterprise/payment_boundary_spec.spl` |
| Updated | 2026-08-16 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

System scenarios for `std.enterprise_payment` (lane
`.spipe/simple_enterprise_suite` W5-B): a clerk sells a product, a payments
operator creates a payment intent (getting a provider_ref for the hosted
provider flow), and provider webhooks — signature-verified and deduplicated
by provider_event_id — drive the intent through
pending -> authorized -> captured, with the order becoming paid in the SAME
unit of work as the capture.

## Proven here

- happy path: create -> authorized -> captured; order paid atomically;
  journal stays balanced; audit chain verifies;
- bad signature: rejected `invalid-record`, NO state change of any kind;
- duplicate provider_event_id: replay returns the recorded result with
  exactly one effect (event count, order status unchanged);
- failed webhook: intent failed, order still unpaid and payable;
- reconciliation (§7.2): pending-over-ttl, captured-intent-without-paid-order
  and paid-order-without-captured-intent, seeded via direct store writes;
- tenant isolation: tenant B cannot drive tenant A's provider_ref;
- restart survival: statuses derive identically from a reopened store.

## Troubleshooting

- `invalid-record` from a webhook: check the signature is
  sha256(secret + "|" + payload) over the SAME payload text, and that the
  transition is legal for the intent's current status.
- The signature scheme is a stand-in for provider SDK verification — see
  the module docstring; no card data ever transits these tests.

**Requirements:** N/A
**Plan:** N/A
**Design:** doc/01_research/app/enterprise/simple_enterprise_suite_full_design_2026-08-14.md §7.1, §7.2, §10.2
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W5-B).

## Scenarios

### payment boundary — hosted-provider happy path

#### creates an intent, authorizes, captures, and pays the order atomically

- Create a pending intent for the created order
   - Expected: payment_intent_status(store, "tenant-a", "intent-1") equals `pending`
   - Expected: payment_intent_ref(store, "tenant-a", "intent-1") equals `ref`
- Provider webhook: authorized
   - Expected: auth.reason equals `accepted`
   - Expected: payment_intent_status(store, "tenant-a", "intent-1") equals `authorized`
   - Expected: sale_order_status(store, "tenant-a", "order-100") equals `created`
- Provider webhook: captured — intent captured AND order paid together
   - Expected: cap.reason equals `accepted`
   - Expected: payment_intent_status(store, "tenant-a", "intent-1") equals `captured`
   - Expected: sale_order_status(store, "tenant-a", "order-100") equals `paid`
- Audit chain still verifies


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a pending intent for the created order")
val store = fresh_store("happy")
val ref = create_pending(store, "int-key-1")
expect(ref.len() > 0).to_be(true)
expect(payment_intent_status(store, "tenant-a", "intent-1")).to_equal("pending")
expect(payment_intent_ref(store, "tenant-a", "intent-1")).to_equal(ref)

step("Provider webhook: authorized")
val auth = signed_webhook(store, ref, "authorized", "evt-1")
expect(auth.reason).to_equal("accepted")
expect(payment_intent_status(store, "tenant-a", "intent-1")).to_equal("authorized")
expect(sale_order_status(store, "tenant-a", "order-100")).to_equal("created")

step("Provider webhook: captured — intent captured AND order paid together")
val cap = signed_webhook(store, ref, "captured", "evt-2")
expect(cap.reason).to_equal("accepted")
expect(payment_intent_status(store, "tenant-a", "intent-1")).to_equal("captured")
expect(sale_order_status(store, "tenant-a", "order-100")).to_equal("paid")
expect(sale_journal_balanced(store, "tenant-a")).to_be(true)

step("Audit chain still verifies")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

### payment boundary — signature verification

#### rejects a bad signature with invalid-record and NO state change

- Send a captured webhook with a wrong signature
   - Expected: r.reason equals `invalid-record`
- No state changed: intent still pending, order unpaid, no new events
   - Expected: payment_intent_status(store, "tenant-a", "intent-1") equals `pending`
   - Expected: sale_order_status(store, "tenant-a", "order-100") equals `created`
   - Expected: intent_event_count(store, "tenant-a") equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("badsig")
val ref = create_pending(store, "int-key-1")
val before = intent_event_count(store, "tenant-a")
step("Send a captured webhook with a wrong signature")
val r = webhook(store, ref, "captured", "evt-bad", "{\"kind\":\"captured\"}", "not-a-valid-signature")
expect(r.ok).to_be(false)
expect(r.reason).to_equal("invalid-record")
step("No state changed: intent still pending, order unpaid, no new events")
expect(payment_intent_status(store, "tenant-a", "intent-1")).to_equal("pending")
expect(sale_order_status(store, "tenant-a", "order-100")).to_equal("created")
expect(intent_event_count(store, "tenant-a")).to_equal(before)
store_close(store)
```

</details>

### payment boundary — webhook deduplication

#### replays a provider_event_id with exactly one effect

- First captured webhook lands
   - Expected: first.reason equals `accepted`
- Replaying the SAME provider_event_id returns the recorded result
   - Expected: replay.reason equals `duplicate-key`
- Exactly one effect: same event count, order still paid once
   - Expected: intent_event_count(store, "tenant-a") equals `after_first`
   - Expected: payment_intent_status(store, "tenant-a", "intent-1") equals `captured`
   - Expected: sale_order_status(store, "tenant-a", "order-100") equals `paid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("dedupe")
val ref = create_pending(store, "int-key-1")
step("First captured webhook lands")
val first = signed_webhook(store, ref, "captured", "evt-cap")
expect(first.reason).to_equal("accepted")
val after_first = intent_event_count(store, "tenant-a")
step("Replaying the SAME provider_event_id returns the recorded result")
val replay = signed_webhook(store, ref, "captured", "evt-cap")
expect(replay.ok).to_be(true)
expect(replay.reason).to_equal("duplicate-key")
step("Exactly one effect: same event count, order still paid once")
expect(intent_event_count(store, "tenant-a")).to_equal(after_first)
expect(payment_intent_status(store, "tenant-a", "intent-1")).to_equal("captured")
expect(sale_order_status(store, "tenant-a", "order-100")).to_equal("paid")
expect(sale_journal_balanced(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

### payment boundary — failed webhook

#### fails the intent and leaves the order untouched

- Provider webhook: failed
   - Expected: r.reason equals `accepted`
   - Expected: payment_intent_status(store, "tenant-a", "intent-1") equals `failed`
- Order untouched and journal balanced
   - Expected: sale_order_status(store, "tenant-a", "order-100") equals `created`
- A failed intent accepts no further capture
   - Expected: cap.reason equals `invalid-record`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("failed")
val ref = create_pending(store, "int-key-1")
step("Provider webhook: failed")
val r = signed_webhook(store, ref, "failed", "evt-f")
expect(r.reason).to_equal("accepted")
expect(payment_intent_status(store, "tenant-a", "intent-1")).to_equal("failed")
step("Order untouched and journal balanced")
expect(sale_order_status(store, "tenant-a", "order-100")).to_equal("created")
expect(sale_journal_balanced(store, "tenant-a")).to_be(true)
step("A failed intent accepts no further capture")
val cap = signed_webhook(store, ref, "captured", "evt-late")
expect(cap.reason).to_equal("invalid-record")
store_close(store)
```

</details>

### payment boundary — reconciliation (§7.2)

#### flags stale pending intents and seeded intent/order divergence

- Clean state reconciles clean (short clock, long ttl)
   - Expected: clean.pending_over_ttl.len() equals `0`
   - Expected: clean.captured_without_paid_order.len() equals `0`
   - Expected: clean.paid_order_without_captured_intent.len() equals `0`
- Pending intent over TTL is flagged
   - Expected: stale.pending_over_ttl.len() equals `1`
   - Expected: stale.pending_over_ttl[0] equals `intent-1`
- Seed corruption directly: a captured event without paying the order
- Seed corruption directly: a paid order with no captured intent
   - Expected: div.captured_without_paid_order.len() equals `1`
   - Expected: div.captured_without_paid_order[0] equals `intent-1`
   - Expected: div.paid_order_without_captured_intent.len() equals `1`
   - Expected: div.paid_order_without_captured_intent[0] equals `order-777`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("reconcile")
val ref = create_pending(store, "int-key-1")
step("Clean state reconciles clean (short clock, long ttl)")
val clean = payment_reconcile(store, "tenant-a", 1500, 3600)
expect(clean.pending_over_ttl.len()).to_equal(0)
expect(clean.captured_without_paid_order.len()).to_equal(0)
expect(clean.paid_order_without_captured_intent.len()).to_equal(0)
step("Pending intent over TTL is flagged")
val stale = payment_reconcile(store, "tenant-a", 999999, 3600)
expect(stale.pending_over_ttl.len()).to_equal(1)
expect(stale.pending_over_ttl[0]).to_equal("intent-1")
step("Seed corruption directly: a captured event without paying the order")
store_insert_row(store,
    "INSERT INTO payment_intent_events (tenant_id, intent_id, order_id, event, provider_ref, detail, at) VALUES (?, ?, ?, ?, ?, ?, ?)",
    ["tenant-a", "intent-1", "order-100", "captured", ref, "seeded", "1500"])
step("Seed corruption directly: a paid order with no captured intent")
store_insert_row(store,
    "INSERT INTO order_events (tenant_id, order_id, event, detail) VALUES (?, ?, ?, ?)",
    ["tenant-a", "order-777", "created", ""])
store_insert_row(store,
    "INSERT INTO order_events (tenant_id, order_id, event, detail) VALUES (?, ?, ?, ?)",
    ["tenant-a", "order-777", "paid", ""])
val div = payment_reconcile(store, "tenant-a", 1500, 3600)
expect(div.captured_without_paid_order.len()).to_equal(1)
expect(div.captured_without_paid_order[0]).to_equal("intent-1")
expect(div.paid_order_without_captured_intent.len()).to_equal(1)
expect(div.paid_order_without_captured_intent[0]).to_equal("order-777")
store_close(store)
```

</details>

### payment boundary — tenant isolation

#### tenant B cannot drive tenant A's provider_ref

- Tenant B sends a correctly signed capture for tenant A's ref
   - Expected: r.reason equals `not-found`
- Tenant A's intent and order are untouched
   - Expected: payment_intent_status(store, "tenant-a", "intent-1") equals `pending`
   - Expected: sale_order_status(store, "tenant-a", "order-100") equals `created`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("tenants")
val ref = create_pending(store, "int-key-1")
step("Tenant B sends a correctly signed capture for tenant A's ref")
val tb = tenant_b()
val op_b = pay_op("pay-b")
val payload = "{\"ref\":\"" + ref + "\"}"
val r = payment_webhook_receive(store, session_for(op_b, tb), tb, op_b,
    envelope("wh-x", "payment.webhook.receive", payload),
    provider(), ref, "captured", provider_sign(provider(), payload), "evt-x", 2000)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("not-found")
step("Tenant A's intent and order are untouched")
expect(payment_intent_status(store, "tenant-a", "intent-1")).to_equal("pending")
expect(sale_order_status(store, "tenant-a", "order-100")).to_equal("created")
store_close(store)
```

</details>

### payment boundary — restart survival

#### derives identical statuses from a reopened store

- Reopen the same database file
   - Expected: payment_intent_status(store2, "tenant-a", "intent-1") equals `captured`
   - Expected: sale_order_status(store2, "tenant-a", "order-100") equals `paid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("restart")
val ref = create_pending(store, "int-key-1")
signed_webhook(store, ref, "captured", "evt-1")
store_close(store)
step("Reopen the same database file")
val store2 = store_open(db_path("restart"))
expect(payment_intent_status(store2, "tenant-a", "intent-1")).to_equal("captured")
expect(sale_order_status(store2, "tenant-a", "order-100")).to_equal("paid")
expect(sale_journal_balanced(store2, "tenant-a")).to_be(true)
expect(audit_verify_chain(store2, "tenant-a")).to_be(true)
store_close(store2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/01_research/app/enterprise/simple_enterprise_suite_full_design_2026-08-14.md §7.1, §7.2, §10.2`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>
