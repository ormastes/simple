# Local Gateway Specification

> <details>

<!-- sdn-diagram:id=local_gateway_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=local_gateway_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

local_gateway_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=local_gateway_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Local Gateway Specification

## Scenarios

### LocalGateway — self-contained payment processor

### authorize

#### authorizes valid token and amount

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_local_gateway()
val req = AuthorizeRequest { token: "tok_local_1111_1000", amount: Amount { cents: 5000, currency: "USD" }, merchant_ref: "order-1", idempotency_key: "idem-1" }
val result = local_authorize(gw, req)
expect result.success == true
expect result.status == PaymentStatus.Authorized
expect result.transaction_id != ""
```

</details>

#### rejects empty token

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_local_gateway()
val req = AuthorizeRequest { token: "", amount: Amount { cents: 1000, currency: "USD" }, merchant_ref: "x", idempotency_key: "x" }
val result = local_authorize(gw, req)
expect result.success == false
```

</details>

#### rejects zero amount

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_local_gateway()
val req = AuthorizeRequest { token: "tok_valid", amount: Amount { cents: 0, currency: "USD" }, merchant_ref: "x", idempotency_key: "x" }
val result = local_authorize(gw, req)
expect result.success == false
```

</details>

### test card decline simulation

#### declines tok_visa_declined

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_local_gateway()
val req = AuthorizeRequest { token: "tok_visa_declined", amount: Amount { cents: 1000, currency: "USD" }, merchant_ref: "decline-test", idempotency_key: "dec-1" }
val result = local_authorize(gw, req)
expect result.success == false
expect result.error_message == "card_declined"
```

</details>

#### returns insufficient_funds for test token

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_local_gateway()
val req = ChargeRequest { token: "tok_visa_insufficient", amount: Amount { cents: 1000, currency: "USD" }, merchant_ref: "insuf-test", idempotency_key: "insuf-1" }
val result = local_charge(gw, req)
expect result.success == false
expect result.error_message == "insufficient_funds"
```

</details>

#### returns expired_card for test token

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_local_gateway()
val req = ChargeRequest { token: "tok_visa_expired", amount: Amount { cents: 1000, currency: "USD" }, merchant_ref: "exp-test", idempotency_key: "exp-1" }
val result = local_charge(gw, req)
expect result.success == false
expect result.error_message == "expired_card"
```

</details>

### charge (authorize + capture)

#### charges valid token

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_local_gateway()
val req = ChargeRequest { token: "tok_local_1111_1000", amount: Amount { cents: 2500, currency: "EUR" }, merchant_ref: "order-2", idempotency_key: "idem-2" }
val result = local_charge(gw, req)
expect result.success == true
expect result.status == PaymentStatus.Captured
```

</details>

### refund

#### refunds with valid transaction

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_local_gateway()
val req = RefundRequest { transaction_id: "txn_local_1000", amount: Amount { cents: 500, currency: "USD" }, reason: "customer request" }
val result = local_refund(gw, req)
expect result.success == true
expect result.status == PaymentStatus.Refunded
```

</details>

#### rejects refund with zero amount

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_local_gateway()
val req = RefundRequest { transaction_id: "txn_local_1000", amount: Amount { cents: 0, currency: "USD" }, reason: "test" }
val result = local_refund(gw, req)
expect result.success == false
```

</details>

### void

#### voids an authorized transaction

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_local_gateway()
val req = VoidRequest { transaction_id: "txn_local_1000", reason: "order canceled" }
val result = local_void(gw, req)
expect result.success == true
expect result.status == PaymentStatus.Voided
```

</details>

### tokenize

#### tokenizes valid Visa card

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_local_gateway()
val req = TokenizeRequest { card_number: "4111111111111111", expiry_month: 12, expiry_year: 2028, cardholder_name: "Test User" }
val result = local_tokenize(gw, req)
expect result.success == true
expect result.token != ""
```

</details>

#### rejects invalid card number

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_local_gateway()
val req = TokenizeRequest { card_number: "1234567890123456", expiry_month: 12, expiry_year: 2028, cardholder_name: "Bad Card" }
val result = local_tokenize(gw, req)
expect result.success == false
```

</details>

#### rejects expired card

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_local_gateway()
val req = TokenizeRequest { card_number: "4111111111111111", expiry_month: 1, expiry_year: 2020, cardholder_name: "Expired" }
val result = local_tokenize(gw, req)
expect result.success == false
```

</details>

### connector registry with local + btcpay

#### registers multiple connectors and routes by priority

1. entries push

2. entries push

3. entries push

4. expect entries length


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var entries = []
entries.push("local")
entries.push("btcpay")
entries.push("stripe")
expect entries.length() == 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `/tmp/simple-payment/test/local_gateway_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LocalGateway — self-contained payment processor
- authorize
- test card decline simulation
- charge (authorize + capture)
- refund
- void
- tokenize
- connector registry with local + btcpay

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
