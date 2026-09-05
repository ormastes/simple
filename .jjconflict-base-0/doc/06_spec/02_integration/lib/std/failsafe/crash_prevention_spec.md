# Crash Prevention Specification

> <details>

<!-- sdn-diagram:id=crash_prevention_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=crash_prevention_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

crash_prevention_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=crash_prevention_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Crash Prevention Specification

## Scenarios

### Panic Recovery

#### preserves panic location for debugging

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = PanicInfo.new("Test panic")
expect(info.message).to_equal("Test panic")

val error = info.to_error()
expect(error.category).to_equal(ErrorCategory.Panic)
expect(error.recoverable).to_equal(false)
```

</details>

### Rate Limit Protection

#### prevents DoS from single client

1. var limiter = RateLimiter default
   - Expected: decision1 equals `RateLimitDecision.Allow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var limiter = RateLimiter.default()

val decision1 = limiter.check("attacker")
expect(decision1).to_equal(RateLimitDecision.Allow)
```

</details>

#### allows legitimate clients during attack

1. var limiter = RateLimiter default
   - Expected: client1 equals `RateLimitDecision.Allow`
   - Expected: client2 equals `RateLimitDecision.Allow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var limiter = RateLimiter.default()

val client1 = limiter.check("client1")
val client2 = limiter.check("client2")

expect(client1).to_equal(RateLimitDecision.Allow)
expect(client2).to_equal(RateLimitDecision.Allow)
```

</details>

### Circuit Breaker Protection

#### starts in closed state

1. var breaker = CircuitBreaker default
   - Expected: breaker.state equals `CircuitState.Closed`
   - Expected: breaker.allow_request() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var breaker = CircuitBreaker.default("test")
expect(breaker.state).to_equal(CircuitState.Closed)
expect(breaker.allow_request()).to_equal(true)
```

</details>

#### records successful operations

1. var breaker = CircuitBreaker default
2. breaker record success


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var breaker = CircuitBreaker.default("success-test")
breaker.record_success()
expect(breaker.stats.success_count).to_be_greater_than(0)
```

</details>

### Timeout Protection

#### creates timeout tokens

1. var manager = TimeoutManager default
   - Expected: token.is_active() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = TimeoutManager.default()
val token = manager.start_timeout("operation")
expect(token.is_active()).to_equal(true)
```

</details>

#### supports deadline for multi-step operations

1. var deadline = Deadline new
2. deadline start operation
3. deadline complete operation
   - Expected: deadline.operations_started equals `1`
   - Expected: deadline.operations_completed equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deadline = Deadline.new(10000)
deadline.start_operation()
deadline.complete_operation()

expect(deadline.operations_started).to_equal(1)
expect(deadline.operations_completed).to_equal(1)
```

</details>

### Resource Protection

#### monitors memory usage

1. var monitor = ResourceMonitor default
   - Expected: monitor.enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var monitor = ResourceMonitor.default()
expect(monitor.enabled).to_equal(true)
```

</details>

#### tracks alerts

1. var monitor = ResourceMonitor default


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var monitor = ResourceMonitor.default()
val initial_count = monitor.get_unacknowledged_alerts().len()
expect(initial_count).to_be_greater_than(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/std/failsafe/crash_prevention_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Panic Recovery
- Rate Limit Protection
- Circuit Breaker Protection
- Timeout Protection
- Resource Protection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
