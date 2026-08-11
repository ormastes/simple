# Agent Specification

> 1. expect validate agent request

<!-- sdn-diagram:id=agent_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=agent_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

agent_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=agent_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Agent Specification

## Scenarios

### Agent payment tool — LLM-safe interface

### validate_agent_request

#### rejects request with raw card number in token field

1. expect validate agent request


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = PaymentToolRequest { action: "charge", token: "4111111111111111", amount_cents: 1000, currency: "USD" }
expect validate_agent_request(req) == false
```

</details>

#### accepts request with opaque vault token

1. expect validate agent request


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = PaymentToolRequest { action: "charge", token: "tok_abc123def456", amount_cents: 1000, currency: "USD" }
expect validate_agent_request(req) == true
```

</details>

#### rejects empty token

1. expect validate agent request


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = PaymentToolRequest { action: "charge", token: "", amount_cents: 1000, currency: "USD" }
expect validate_agent_request(req) == false
```

</details>

#### rejects request with CVV-like data

1. expect validate agent request


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = PaymentToolRequest { action: "charge", token: "123", amount_cents: 1000, currency: "USD" }
expect validate_agent_request(req) == false
```

</details>

### handle_payment_tool

#### charges with valid opaque token

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = PaymentToolRequest { action: "charge", token: "tok_test_123", amount_cents: 2000, currency: "USD" }
val result = handle_payment_tool(req)
expect result.success == true
```

</details>

#### refunds with valid token

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = PaymentToolRequest { action: "refund", token: "tok_test_123", amount_cents: 500, currency: "USD" }
val result = handle_payment_tool(req)
expect result.success == true
```

</details>

### list_payment_methods_for_agent

#### returns empty list when no methods stored

1. expect methods length


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val methods = list_payment_methods_for_agent()
expect methods.length() == 0
```

</details>

### security guardrails

#### agent never receives raw PAN in any response

1. expect result message contains

2. expect result message contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = PaymentToolRequest { action: "list", token: "", amount_cents: 0, currency: "" }
val result = handle_payment_tool(req)
expect result.message.contains("4111") == false
expect result.message.contains("5500") == false
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `/tmp/simple-payment/test/agent_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Agent payment tool — LLM-safe interface
- validate_agent_request
- handle_payment_tool
- list_payment_methods_for_agent
- security guardrails

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
