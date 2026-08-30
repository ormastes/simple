# Kernel Thread Primitives Specification

> Tests covering kernel_thread primitives — M1, AC-3: kevent — kernel event object, AC-3: kfutex — futex-like wait/wake, AC-3: kernel_thread — TLS segment (FS.base).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kernel Thread Primitives Specification

## Scenarios

### kernel_thread primitives — M1

### AC-3: kevent — kernel event object

#### AC-3: kevent_create with auto_reset=false returns a valid handle

- AC-3: kevent_create with auto_reset=false returns a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: kevent_create with auto_reset=false returns a valid handle")
val h = kevent_create(false)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: kevent_create with auto_reset=true returns a valid handle

- AC-3: kevent_create with auto_reset=true returns a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = kevent_create(true)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: kevent_create returns distinct handles for separate calls

- AC-3: kevent_create returns distinct handles for separate calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: kevent_create returns distinct handles for separate calls")
val h1 = kevent_create(false)
val h2 = kevent_create(false)
expect(h1).to_not_equal(h2)
```

</details>

#### AC-3: kevent_set is callable without error on a valid handle

- AC-3: kevent_set is callable without error on a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: kevent_set is callable without error on a valid handle")
val h = kevent_create(false)
kevent_set(h)
# If we reach here, set did not panic
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: kevent_reset is callable without error on a valid handle

- AC-3: kevent_reset is callable without error on a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: kevent_reset is callable without error on a valid handle")
val h = kevent_create(false)
kevent_set(h)
kevent_reset(h)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: kevent_wait with timeout_ns=0 returns immediately with WaitResult value

- AC-3: kevent_wait with timeout_ns=0 returns immediately with WaitResult value
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: kevent_wait with timeout_ns=0 returns immediately with WaitResult value")
val h = kevent_create(false)
kevent_set(h)
# Wait on a set event with 0 timeout: expect signaled
val result = kevent_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### AC-3: kevent_wait on unset event with timeout_ns=0 returns timeout

- AC-3: kevent_wait on unset event with timeout_ns=0 returns timeout
   - Expected: result equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: kevent_wait on unset event with timeout_ns=0 returns timeout")
val h = kevent_create(false)
# Event is not set; timeout immediately
val result = kevent_wait(h, 0)
expect(result).to_equal("timeout")
```

</details>

#### AC-3: auto-reset kevent_wait resets the handle after signaled

- AC-3: auto-reset kevent_wait resets the handle after signaled
   - Expected: r1 equals `signaled`
   - Expected: r2 equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: auto-reset kevent_wait resets the handle after signaled")
val h = kevent_create(true)
kevent_set(h)
val r1 = kevent_wait(h, 0)
expect(r1).to_equal("signaled")
# Second wait on auto-reset event: should be timeout (reset already happened)
val r2 = kevent_wait(h, 0)
expect(r2).to_equal("timeout")
```

</details>

### AC-3: kfutex — futex-like wait/wake

#### AC-3: kfutex_wake with count=1 returns the number of woken waiters

- AC-3: kfutex_wake with count=1 returns the number of woken waiters
   - Expected: woken equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: kfutex_wake with count=1 returns the number of woken waiters")
# No waiters: wake returns 0
val addr: u32 = 0
val woken = kfutex_wake(addr, 1)
expect(woken).to_equal(0)
```

</details>

#### AC-3: kfutex_wait with mismatched expected returns immediately

- AC-3: kfutex_wait with mismatched expected returns immediately
   - Expected: result equals `aborted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: kfutex_wait with mismatched expected returns immediately")
# If *addr != expected, futex returns immediately with WaitResult.aborted
val addr: u32 = 0
val result = kfutex_wait(addr, 99, 0)
expect(result).to_equal("aborted")
```

</details>

#### AC-3: kfutex_wait with matching expected and timeout_ns=0 returns timeout

- AC-3: kfutex_wait with matching expected and timeout_ns=0 returns timeout
   - Expected: result equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: kfutex_wait with matching expected and timeout_ns=0 returns timeout")
val addr: u32 = 42
val result = kfutex_wait(addr, 42, 0)
expect(result).to_equal("timeout")
```

</details>

### AC-3: kernel_thread — TLS segment (FS.base)

#### AC-3: kernel_thread_tls_set and tls_get round-trip a value

- AC-3: kernel_thread_tls_set and tls_get round-trip a value
   - Expected: got equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: kernel_thread_tls_set and tls_get round-trip a value")
# key=1 (arbitrary), store a sentinel pattern
kernel_thread_tls_set(1, 0xDEADBEEF)
val got = kernel_thread_tls_get(1)
expect(got).to_equal(0xDEADBEEF)
```

</details>

#### AC-3: kernel_thread_tls_get for unset key returns null (0)

- AC-3: kernel_thread_tls_get for unset key returns null (0)
   - Expected: got equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: kernel_thread_tls_get for unset key returns null (0)")
val got = kernel_thread_tls_get(255)
expect(got).to_equal(0)
```

</details>

#### AC-3: kernel_thread_tls_set with key=0 stores and retrieves

- AC-3: kernel_thread_tls_set with key=0 stores and retrieves
   - Expected: got equals `0x1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: kernel_thread_tls_set with key=0 stores and retrieves")
kernel_thread_tls_set(0, 0x1234)
val got = kernel_thread_tls_get(0)
expect(got).to_equal(0x1234)
```

</details>

#### AC-3: kernel_thread_create returns a positive Tid

- AC-3: kernel_thread_create returns a positive Tid


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: kernel_thread_create returns a positive Tid")
# We supply a no-op entry function and stack_size=4096
fn noop_entry() -> void:
    val _ = 0
val tid = kernel_thread_create(noop_entry, 4096)
expect(tid).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/wine/kernel_thread_primitives_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering kernel_thread primitives — M1, AC-3: kevent — kernel event object, AC-3: kfutex — futex-like wait/wake, AC-3: kernel_thread — TLS segment (FS.base).
- kernel_thread primitives — M1
- AC-3: kevent — kernel event object
- AC-3: kfutex — futex-like wait/wake
- AC-3: kernel_thread — TLS segment (FS.base)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `63117a4313986cf7c321cb93827df466f9ef3a86c251df38d45b23bedbfc9d60`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `63117a4313986cf7c321cb93827df466f9ef3a86c251df38d45b23bedbfc9d60`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `63117a4313986cf7c321cb93827df466f9ef3a86c251df38d45b23bedbfc9d60`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/kernel/wine/kernel_thread_primitives_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/wine/kernel_thread_primitives_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/os/kernel/wine/kernel_thread_primitives_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/wine/kernel_thread_primitives_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/wine/kernel_thread_primitives_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/wine/kernel_thread_primitives_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/kernel/wine/kernel_thread_primitives_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: kevent_create with auto_reset=false returns a valid handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/wine/kernel_thread_primitives_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: kevent_create with auto_reset=true returns a valid handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/wine/kernel_thread_primitives_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: kevent_create returns distinct handles for separate calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
