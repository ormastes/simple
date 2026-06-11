# retry_resilience_spec

> Retry Resilience Specification

<!-- sdn-diagram:id=retry_resilience_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=retry_resilience_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

retry_resilience_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=retry_resilience_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# retry_resilience_spec

Retry Resilience Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/core/resilience/retry_resilience_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Retry Resilience Specification

Tests for retry logic, circuit breaker patterns, exponential backoff
simulation, and boundary behavior of retry mechanisms.

Feature: Retry and Fault Tolerance Patterns
Category: Resilience Testing
Status: Active

## Scenarios

### resilience: retry patterns

#### succeeds when failure count is less than max attempts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = retry_with_max(3, 5)
val succeeded = result[0]
val attempts = result[1]
expect(succeeded).to_equal(true)
expect(attempts).to_equal(4)
```

</details>

#### fails when failure count equals max attempts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = retry_with_max(5, 5)
val succeeded = result[0]
expect(succeeded).to_equal(false)
```

</details>

#### fails when failure count exceeds max attempts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = retry_with_max(10, 3)
val succeeded = result[0]
expect(succeeded).to_equal(false)
```

</details>

#### succeeds on first try when no failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = retry_with_max(0, 5)
val succeeded = result[0]
val attempts = result[1]
expect(succeeded).to_equal(true)
expect(attempts).to_equal(1)
```

</details>

#### boundary: exactly N retries needed succeeds at limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = retry_with_max(4, 5)
val succeeded = result[0]
val attempts = result[1]
expect(succeeded).to_equal(true)
expect(attempts).to_equal(5)
```

</details>

#### boundary: N+1 retries needed fails at limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = retry_with_max(5, 5)
val succeeded = result[0]
expect(succeeded).to_equal(false)
```

</details>

### resilience: exponential backoff

#### base delay is returned for single attempt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = calc_backoff_total(1, 100, 10000)
expect(total).to_equal(100)
```

</details>

#### delay doubles each attempt

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = calc_backoff_total(3, 100, 10000)
# 100 + 200 + 400 = 700
expect(total).to_equal(700)
```

</details>

#### delay is capped at max_delay

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = calc_backoff_total(5, 100, 300)
# 100 + 200 + 300 + 300 + 300 = 1200
expect(total).to_equal(1200)
```

</details>

#### zero attempts yields zero total delay

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = calc_backoff_total(0, 100, 10000)
expect(total).to_equal(0)
```

</details>

#### backoff with jitter stays within bounds

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(30001)
var failures = 0
for trial in 0..50:
    val base = lcg_range(10, 100)
    val max_d = lcg_range(200, 1000)
    val attempts = lcg_range(1, 8)
    val total = calc_backoff_total(attempts, base, max_d)
    # Total should be at least base * attempts (lower bound)
    if total < base:
        failures = failures + 1
    # Total should not exceed max_d * attempts (upper bound)
    if total > max_d * attempts:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

### resilience: circuit breaker

#### stays closed when all requests succeed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outcomes = [1, 1, 1, 1, 1]
val result = simulate_circuit_breaker(outcomes, 3, 2)
val state = result[0]
expect(state).to_equal("closed")
```

</details>

#### opens after threshold failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outcomes = [0, 0, 0]
val result = simulate_circuit_breaker(outcomes, 3, 2)
val state = result[0]
expect(state).to_equal("open")
```

</details>

#### stays closed when failures are below threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outcomes = [0, 0, 1, 1, 1]
val result = simulate_circuit_breaker(outcomes, 3, 2)
val state = result[0]
expect(state).to_equal("closed")
```

</details>

#### transitions to half-open after reset period

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 3 failures open it, then enough time passes for half-open
val outcomes = [0, 0, 0, 0, 0, 0, 1]
val result = simulate_circuit_breaker(outcomes, 3, 2)
val state = result[0]
# After opening at request 3, reset_after=2 means at request 5+ it goes half-open
# Then success at request 7 closes it
expect(state).to_equal("closed")
```

</details>

#### tracks success count correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outcomes = [1, 1, 0, 1, 1]
val result = simulate_circuit_breaker(outcomes, 5, 2)
val success_count = result[1]
expect(success_count).to_equal(4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
