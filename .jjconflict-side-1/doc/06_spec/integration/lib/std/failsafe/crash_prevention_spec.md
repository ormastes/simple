# Crash Prevention Specification

> Tests covering Panic Recovery, Rate Limit Protection, Circuit Breaker Protection, Timeout Protection, Resource Protection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Crash Prevention Specification

## Scenarios

### Panic Recovery

#### preserves panic location for debugging

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves panic location for debugging
   - Expected: info.message equals `Test panic`
   - Expected: error.category equals `ErrorCategory.Panic`
   - Expected: error.recoverable is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves panic location for debugging")
val info = PanicInfo.new("Test panic")
expect(info.message).to_equal("Test panic")

val error = info.to_error()
expect(error.category).to_equal(ErrorCategory.Panic)
expect(error.recoverable).to_equal(false)
```

</details>

### Rate Limit Protection

#### prevents DoS from single client

- prevents DoS from single client
   - Expected: decision1 equals `RateLimitDecision.Allow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("prevents DoS from single client")
var limiter = RateLimiter.default()

val decision1 = limiter.check("attacker")
expect(decision1).to_equal(RateLimitDecision.Allow)
```

</details>

#### allows legitimate clients during attack

- allows legitimate clients during attack
   - Expected: client1 equals `RateLimitDecision.Allow`
   - Expected: client2 equals `RateLimitDecision.Allow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("allows legitimate clients during attack")
var limiter = RateLimiter.default()

val client1 = limiter.check("client1")
val client2 = limiter.check("client2")

expect(client1).to_equal(RateLimitDecision.Allow)
expect(client2).to_equal(RateLimitDecision.Allow)
```

</details>

### Circuit Breaker Protection

#### starts in closed state

- starts in closed state
   - Expected: breaker.state equals `CircuitState.Closed`
   - Expected: breaker.allow_request() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("starts in closed state")
var breaker = CircuitBreaker.default("test")
expect(breaker.state).to_equal(CircuitState.Closed)
expect(breaker.allow_request()).to_equal(true)
```

</details>

#### records successful operations

- records successful operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("records successful operations")
var breaker = CircuitBreaker.default("success-test")
breaker.record_success()
expect(breaker.stats.success_count).to_be_greater_than(0)
```

</details>

### Timeout Protection

#### creates timeout tokens

- creates timeout tokens
   - Expected: token.is_active() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates timeout tokens")
var manager = TimeoutManager.default()
val token = manager.start_timeout("operation")
expect(token.is_active()).to_equal(true)
```

</details>

#### supports deadline for multi-step operations

- supports deadline for multi-step operations
   - Expected: deadline.operations_started equals `1`
   - Expected: deadline.operations_completed equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports deadline for multi-step operations")
var deadline = Deadline.new(10000)
deadline.start_operation()
deadline.complete_operation()

expect(deadline.operations_started).to_equal(1)
expect(deadline.operations_completed).to_equal(1)
```

</details>

### Resource Protection

#### monitors memory usage

- monitors memory usage
   - Expected: monitor.enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("monitors memory usage")
var monitor = ResourceMonitor.default()
expect(monitor.enabled).to_equal(true)
```

</details>

#### tracks alerts

- tracks alerts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tracks alerts")
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
| Source | `test/integration/lib/std/failsafe/crash_prevention_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Panic Recovery, Rate Limit Protection, Circuit Breaker Protection, Timeout Protection, Resource Protection.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `415667012fd8162bb7711d94c5aec6e2ec980cae57b27620afa46e7e72c78b51`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `415667012fd8162bb7711d94c5aec6e2ec980cae57b27620afa46e7e72c78b51`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `415667012fd8162bb7711d94c5aec6e2ec980cae57b27620afa46e7e72c78b51`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/lib/std/failsafe/crash_prevention_spec.spl
mirror: doc/06_spec/integration/lib/std/failsafe/crash_prevention_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/lib/std/failsafe/crash_prevention_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/lib/std/failsafe/crash_prevention_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/lib/std/failsafe/crash_prevention_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/lib/std/failsafe/crash_prevention_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves panic location for debugging' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/std/failsafe/crash_prevention_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prevents DoS from single client' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/std/failsafe/crash_prevention_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows legitimate clients during attack' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
