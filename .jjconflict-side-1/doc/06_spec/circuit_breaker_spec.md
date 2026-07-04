# Circuit Breaker Specification

> <details>

<!-- sdn-diagram:id=circuit_breaker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=circuit_breaker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

circuit_breaker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=circuit_breaker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Circuit Breaker Specification

## Scenarios

### Circuit breaker — gateway failure protection

### initial state

#### starts in Closed state

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = new_circuit_breaker("stripe", 3, 2)
expect cb.state == CircuitState.Closed
```

</details>

#### allows requests when closed

1. expect circuit allow request


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = new_circuit_breaker("stripe", 3, 2)
expect circuit_allow_request(cb) == true
```

</details>

### trip to Open

#### stays Closed below failure threshold

1. var cb = new circuit breaker

2. cb = circuit record failure

3. cb = circuit record failure


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cb = new_circuit_breaker("stripe", 3, 2)
cb = circuit_record_failure(cb, 100)
cb = circuit_record_failure(cb, 101)
expect cb.state == CircuitState.Closed
expect cb.failure_count == 2
```

</details>

#### opens after reaching failure threshold

1. var cb = new circuit breaker

2. cb = circuit record failure

3. cb = circuit record failure

4. cb = circuit record failure

5. expect circuit allow request


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cb = new_circuit_breaker("stripe", 3, 2)
cb = circuit_record_failure(cb, 100)
cb = circuit_record_failure(cb, 101)
cb = circuit_record_failure(cb, 102)
expect cb.state == CircuitState.Open
expect circuit_allow_request(cb) == false
```

</details>

### recovery to HalfOpen

#### transitions to HalfOpen after cooldown

1. var cb = new circuit breaker

2. cb = circuit record failure

3. cb = circuit record failure

4. cb = circuit try half open

5. expect circuit allow request


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cb = new_circuit_breaker("paypal", 2, 2)
cb = circuit_record_failure(cb, 100)
cb = circuit_record_failure(cb, 101)
expect cb.state == CircuitState.Open
cb = circuit_try_half_open(cb, 200, 60)
expect cb.state == CircuitState.HalfOpen
expect circuit_allow_request(cb) == true
```

</details>

#### stays Open before cooldown expires

1. var cb = new circuit breaker

2. cb = circuit record failure

3. cb = circuit record failure

4. cb = circuit try half open


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cb = new_circuit_breaker("paypal", 2, 2)
cb = circuit_record_failure(cb, 100)
cb = circuit_record_failure(cb, 101)
cb = circuit_try_half_open(cb, 130, 60)
expect cb.state == CircuitState.Open
```

</details>

### HalfOpen to Closed

#### closes after enough successes in HalfOpen

1. var cb = new circuit breaker

2. cb = circuit record failure

3. cb = circuit record failure

4. cb = circuit try half open

5. cb = circuit record success

6. cb = circuit record success


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cb = new_circuit_breaker("btcpay", 2, 2)
cb = circuit_record_failure(cb, 100)
cb = circuit_record_failure(cb, 101)
cb = circuit_try_half_open(cb, 200, 60)
expect cb.state == CircuitState.HalfOpen
cb = circuit_record_success(cb)
expect cb.state == CircuitState.HalfOpen
cb = circuit_record_success(cb)
expect cb.state == CircuitState.Closed
```

</details>

#### resets failure count on close

1. var cb = new circuit breaker

2. cb = circuit record failure

3. cb = circuit record failure

4. cb = circuit try half open

5. cb = circuit record success


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cb = new_circuit_breaker("local", 2, 1)
cb = circuit_record_failure(cb, 100)
cb = circuit_record_failure(cb, 101)
cb = circuit_try_half_open(cb, 200, 60)
cb = circuit_record_success(cb)
expect cb.state == CircuitState.Closed
expect cb.failure_count == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `/tmp/simple-payment/test/circuit_breaker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Circuit breaker — gateway failure protection
- initial state
- trip to Open
- recovery to HalfOpen
- HalfOpen to Closed

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
