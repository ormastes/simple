# Gateway Specification

> <details>

<!-- sdn-diagram:id=gateway_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gateway_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gateway_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gateway_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gateway Specification

## Scenarios

### Gateway — payment connector abstraction

### authorize

#### returns Authorized status on valid token and amount

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_mock_gateway()
val req = AuthorizeRequest { token: "tok_test_visa_1234", amount: Amount { cents: 1000, currency: "USD" }, merchant_ref: "order-001", idempotency_key: "idem-001" }
val result = _gw_authorize(gw, req)
expect result.success == true
expect result.status == PaymentStatus.Authorized
expect result.transaction_id != ""
```

</details>

#### returns Failed on invalid token

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_mock_gateway()
val req = AuthorizeRequest { token: "", amount: Amount { cents: 1000, currency: "USD" }, merchant_ref: "order-002", idempotency_key: "idem-002" }
val result = _gw_authorize(gw, req)
expect result.success == false
expect result.status == PaymentStatus.Failed
```

</details>

#### rejects negative amounts

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_mock_gateway()
val req = AuthorizeRequest { token: "tok_test_visa_1234", amount: Amount { cents: -100, currency: "USD" }, merchant_ref: "order-003", idempotency_key: "idem-003" }
val result = _gw_authorize(gw, req)
expect result.success == false
```

</details>

### capture

#### captures a previously authorized transaction

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_mock_gateway()
val auth_req = AuthorizeRequest { token: "tok_test_visa_1234", amount: Amount { cents: 2000, currency: "USD" }, merchant_ref: "order-010", idempotency_key: "idem-010" }
val auth = _gw_authorize(gw, auth_req)
val cap_req = CaptureRequest { transaction_id: auth.transaction_id, amount: Amount { cents: 2000, currency: "USD" } }
val result = _gw_capture(gw, cap_req)
expect result.success == true
expect result.status == PaymentStatus.Captured
```

</details>

### charge

#### authorize + capture in one step

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_mock_gateway()
val req = ChargeRequest { token: "tok_test_mc_5678", amount: Amount { cents: 5000, currency: "EUR" }, merchant_ref: "order-020", idempotency_key: "idem-020" }
val result = _gw_charge(gw, req)
expect result.success == true
expect result.status == PaymentStatus.Captured
```

</details>

### refund

#### refunds a captured transaction

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_mock_gateway()
val req = RefundRequest { transaction_id: "txn_captured_001", amount: Amount { cents: 1000, currency: "USD" }, reason: "customer request" }
val result = _gw_refund(gw, req)
expect result.success == true
expect result.status == PaymentStatus.Refunded
```

</details>

### void

#### voids an authorized but uncaptured transaction

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_mock_gateway()
val req = VoidRequest { transaction_id: "txn_auth_001", reason: "order canceled" }
val result = _gw_void(gw, req)
expect result.success == true
expect result.status == PaymentStatus.Voided
```

</details>

### tokenize

#### returns opaque token from card data

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_mock_gateway()
val req = TokenizeRequest { card_number: "4111111111111111", expiry_month: 12, expiry_year: 2028, cardholder_name: "Test User" }
val result = _gw_tokenize(gw, req)
expect result.success == true
expect result.token != ""
```

</details>

### failing gateway

#### returns failure on all operations when in fail mode

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_failing_mock_gateway()
val req = ChargeRequest { token: "tok_test", amount: Amount { cents: 100, currency: "USD" }, merchant_ref: "order-fail", idempotency_key: "idem-fail" }
val result = _gw_charge(gw, req)
expect result.success == false
expect result.status == PaymentStatus.Failed
```

</details>

### idempotency

#### same gateway returns same txn prefix for same id

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gw = new_mock_gateway()
val req = ChargeRequest { token: "tok_test_visa_1234", amount: Amount { cents: 1000, currency: "USD" }, merchant_ref: "order-idem", idempotency_key: "idem-same" }
val r1 = _gw_charge(gw, req)
val r2 = _gw_charge(gw, req)
expect r1.transaction_id == r2.transaction_id
```

</details>

### connector registry

#### registers and lists connectors

1. var reg = new connector registry

2. reg = reg register

3. reg = reg register

4. expect names length


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = new_connector_registry()
reg = reg_register(reg, "stripe", 1)
reg = reg_register(reg, "paypal", 2)
val names = reg_list(reg)
expect names.length() == 2
```

</details>

#### routes to highest priority connector

1. var reg = new connector registry

2. reg = reg register

3. reg = reg register


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = new_connector_registry()
reg = reg_register(reg, "stripe", 1)
reg = reg_register(reg, "paypal", 2)
val chosen = reg_route(reg, Amount { cents: 1000, currency: "USD" })
expect chosen == "stripe"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `/tmp/simple-payment/test/gateway_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Gateway — payment connector abstraction
- authorize
- capture
- charge
- refund
- void
- tokenize
- failing gateway
- idempotency
- connector registry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
