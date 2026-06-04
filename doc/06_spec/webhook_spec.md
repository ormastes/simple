# Webhook Specification

> 1. expect  map stripe event

<!-- sdn-diagram:id=webhook_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webhook_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webhook_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webhook_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Webhook Specification

## Scenarios

### Webhook handler — payment event dispatch

### Stripe event mapping

#### maps payment_intent.succeeded to PaymentCaptured

1. expect  map stripe event


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect _map_stripe_event("payment_intent.succeeded") == WebhookEventType.PaymentCaptured
```

</details>

#### maps payment_intent.payment_failed to PaymentFailed

1. expect  map stripe event


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect _map_stripe_event("payment_intent.payment_failed") == WebhookEventType.PaymentFailed
```

</details>

#### maps charge.refunded to PaymentRefunded

1. expect  map stripe event


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect _map_stripe_event("charge.refunded") == WebhookEventType.PaymentRefunded
```

</details>

#### maps charge.dispute.created to PaymentDisputed

1. expect  map stripe event


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect _map_stripe_event("charge.dispute.created") == WebhookEventType.PaymentDisputed
```

</details>

#### maps unknown event to UnknownEvent

1. expect  map stripe event


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect _map_stripe_event("some.unknown.event") == WebhookEventType.UnknownEvent
```

</details>

### PayPal event mapping

#### maps PAYMENT.CAPTURE.COMPLETED to PaymentCaptured

1. expect  map paypal event


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect _map_paypal_event("PAYMENT.CAPTURE.COMPLETED") == WebhookEventType.PaymentCaptured
```

</details>

#### maps CHECKOUT.ORDER.APPROVED to PaymentAuthorized

1. expect  map paypal event


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect _map_paypal_event("CHECKOUT.ORDER.APPROVED") == WebhookEventType.PaymentAuthorized
```

</details>

#### maps PAYMENT.CAPTURE.REFUNDED to PaymentRefunded

1. expect  map paypal event


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect _map_paypal_event("PAYMENT.CAPTURE.REFUNDED") == WebhookEventType.PaymentRefunded
```

</details>

### BTCPay event mapping

#### maps InvoiceSettled to InvoicePaid

1. expect  map btcpay event


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect _map_btcpay_event("InvoiceSettled") == WebhookEventType.InvoicePaid
```

</details>

#### maps InvoiceExpired to InvoiceExpired

1. expect  map btcpay event


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect _map_btcpay_event("InvoiceExpired") == WebhookEventType.InvoiceExpired
```

</details>

#### maps InvoiceProcessing to PaymentAuthorized

1. expect  map btcpay event


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect _map_btcpay_event("InvoiceProcessing") == WebhookEventType.PaymentAuthorized
```

</details>

#### maps InvoiceInvalid to PaymentFailed

1. expect  map btcpay event


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect _map_btcpay_event("InvoiceInvalid") == WebhookEventType.PaymentFailed
```

</details>

### webhook config

#### creates empty config

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = new_webhook_config()
expect cfg.stripe_signing_secret == ""
expect cfg.paypal_webhook_id == ""
expect cfg.btcpay_secret == ""
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `/tmp/simple-payment/test/webhook_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Webhook handler — payment event dispatch
- Stripe event mapping
- PayPal event mapping
- BTCPay event mapping
- webhook config

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
