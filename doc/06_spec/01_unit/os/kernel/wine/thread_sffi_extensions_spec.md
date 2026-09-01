# Thread Sffi Extensions Specification

> Tests covering thread_sffi extensions — TLS keys, semaphore, event-wait, AC-3: tls_key_alloc / set / get — per-thread storage, AC-3: semaphore — create / post / wait, AC-3: event_wait — create / set / reset / wait.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Thread Sffi Extensions Specification

## Scenarios

### thread_sffi extensions — TLS keys, semaphore, event-wait

### AC-3: tls_key_alloc / set / get — per-thread storage

#### AC-3: tls_key_alloc returns a positive key

- AC-3: tls_key_alloc returns a positive key


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: tls_key_alloc returns a positive key")
fn no_destructor(p: *void) -> void:
    val _ = 0
val key = tls_key_alloc(no_destructor)
expect(key).to_be_greater_than(0)
```

</details>

#### AC-3: consecutive tls_key_alloc calls return distinct keys

- AC-3: consecutive tls_key_alloc calls return distinct keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: consecutive tls_key_alloc calls return distinct keys")
fn no_destructor(p: *void) -> void:
    val _ = 0
val k1 = tls_key_alloc(no_destructor)
val k2 = tls_key_alloc(no_destructor)
expect(k1 == k2).to_equal(false)
```

</details>

#### AC-3: tls_key_set and tls_key_get round-trip a value

- AC-3: tls_key_set and tls_key_get round-trip a value
   - Expected: got equals `0xABCD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: tls_key_set and tls_key_get round-trip a value")
fn no_destructor(p: *void) -> void:
    val _ = 0
val key = tls_key_alloc(no_destructor)
tls_key_set(key, 0xABCD)
val got = tls_key_get(key)
expect(got).to_equal(0xABCD)
```

</details>

#### AC-3: tls_key_get on unused key returns null (0)

- AC-3: tls_key_get on unused key returns null (0)
   - Expected: got equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: tls_key_get on unused key returns null (0)")
fn no_destructor(p: *void) -> void:
    val _ = 0
val key = tls_key_alloc(no_destructor)
val got = tls_key_get(key)
expect(got).to_equal(0)
```

</details>

#### AC-3: tls_key_set overwrite updates the stored value

- AC-3: tls_key_set overwrite updates the stored value
   - Expected: got equals `0x22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: tls_key_set overwrite updates the stored value")
fn no_destructor(p: *void) -> void:
    val _ = 0
val key = tls_key_alloc(no_destructor)
tls_key_set(key, 0x11)
tls_key_set(key, 0x22)
val got = tls_key_get(key)
expect(got).to_equal(0x22)
```

</details>

### AC-3: semaphore — create / post / wait

#### AC-3: semaphore_create with initial=0 returns a valid handle

- AC-3: semaphore_create with initial=0 returns a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: semaphore_create with initial=0 returns a valid handle")
val h = semaphore_create(0)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: semaphore_create with initial=1 returns a valid handle

- AC-3: semaphore_create with initial=1 returns a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = semaphore_create(1)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: semaphore_create returns distinct handles

- AC-3: semaphore_create returns distinct handles


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: semaphore_create returns distinct handles")
val h1 = semaphore_create(0)
val h2 = semaphore_create(0)
expect(h1 == h2).to_equal(false)
```

</details>

#### AC-3: semaphore_wait with initial=1 and timeout_ns=0 returns signaled

- AC-3: semaphore_wait with initial=1 and timeout_ns=0 returns signaled
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: semaphore_wait with initial=1 and timeout_ns=0 returns signaled")
val h = semaphore_create(1)
val result = semaphore_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### AC-3: semaphore_wait on zero-count semaphore with timeout_ns=0 returns timeout

- AC-3: semaphore_wait on zero-count semaphore with timeout_ns=0 returns timeout
   - Expected: result equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: semaphore_wait on zero-count semaphore with timeout_ns=0 returns timeout")
val h = semaphore_create(0)
val result = semaphore_wait(h, 0)
expect(result).to_equal("timeout")
```

</details>

#### AC-3: semaphore_post followed by semaphore_wait returns signaled

- AC-3: semaphore_post followed by semaphore_wait returns signaled
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: semaphore_post followed by semaphore_wait returns signaled")
val h = semaphore_create(0)
semaphore_post(h)
val result = semaphore_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### AC-3: semaphore count decrements after successful wait

- AC-3: semaphore count decrements after successful wait
   - Expected: r1 equals `signaled`
   - Expected: r2 equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: semaphore count decrements after successful wait")
val h = semaphore_create(1)
val r1 = semaphore_wait(h, 0)
expect(r1).to_equal("signaled")
# Count is now 0; next wait should timeout
val r2 = semaphore_wait(h, 0)
expect(r2).to_equal("timeout")
```

</details>

### AC-3: event_wait — create / set / reset / wait

#### AC-3: event_wait_create with manual_reset=false returns a valid handle

- AC-3: event_wait_create with manual_reset=false returns a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: event_wait_create with manual_reset=false returns a valid handle")
val h = event_wait_create(false)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: event_wait_create with manual_reset=true returns a valid handle

- AC-3: event_wait_create with manual_reset=true returns a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = event_wait_create(true)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: event_wait_wait on unset event with timeout_ns=0 returns timeout

- AC-3: event_wait_wait on unset event with timeout_ns=0 returns timeout
   - Expected: result equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: event_wait_wait on unset event with timeout_ns=0 returns timeout")
val h = event_wait_create(false)
val result = event_wait_wait(h, 0)
expect(result).to_equal("timeout")
```

</details>

#### AC-3: event_wait_set then event_wait_wait returns signaled

- AC-3: event_wait_set then event_wait_wait returns signaled
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: event_wait_set then event_wait_wait returns signaled")
val h = event_wait_create(false)
event_wait_set(h)
val result = event_wait_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### AC-3: manual-reset event remains set after first wait

- AC-3: manual-reset event remains set after first wait
   - Expected: r1 equals `signaled`
   - Expected: r2 equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: manual-reset event remains set after first wait")
val h = event_wait_create(true)
event_wait_set(h)
val r1 = event_wait_wait(h, 0)
expect(r1).to_equal("signaled")
val r2 = event_wait_wait(h, 0)
expect(r2).to_equal("signaled")
```

</details>

#### AC-3: auto-reset event is consumed after first wait

- AC-3: auto-reset event is consumed after first wait
   - Expected: r1 equals `signaled`
   - Expected: r2 equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: auto-reset event is consumed after first wait")
val h = event_wait_create(false)
event_wait_set(h)
val r1 = event_wait_wait(h, 0)
expect(r1).to_equal("signaled")
val r2 = event_wait_wait(h, 0)
expect(r2).to_equal("timeout")
```

</details>

#### AC-3: event_wait_reset on set event causes next wait to timeout

- AC-3: event_wait_reset on set event causes next wait to timeout
   - Expected: result equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-3: event_wait_reset on set event causes next wait to timeout")
val h = event_wait_create(true)
event_wait_set(h)
event_wait_reset(h)
val result = event_wait_wait(h, 0)
expect(result).to_equal("timeout")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/wine/thread_sffi_extensions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering thread_sffi extensions — TLS keys, semaphore, event-wait, AC-3: tls_key_alloc / set / get — per-thread storage, AC-3: semaphore — create / post / wait, AC-3: event_wait — create / set / reset / wait.
- thread_sffi extensions — TLS keys, semaphore, event-wait
- AC-3: tls_key_alloc / set / get — per-thread storage
- AC-3: semaphore — create / post / wait
- AC-3: event_wait — create / set / reset / wait

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-3).`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5117fc3db23fc782881b8e0a81f716d9c4248ef5e19d8ce7578d2be58ecd3311`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5117fc3db23fc782881b8e0a81f716d9c4248ef5e19d8ce7578d2be58ecd3311`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5117fc3db23fc782881b8e0a81f716d9c4248ef5e19d8ce7578d2be58ecd3311`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/kernel/wine/thread_sffi_extensions_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/wine/thread_sffi_extensions_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/os/kernel/wine/thread_sffi_extensions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/wine/thread_sffi_extensions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/wine/thread_sffi_extensions_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/wine/thread_sffi_extensions_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/kernel/wine/thread_sffi_extensions_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: tls_key_alloc returns a positive key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/wine/thread_sffi_extensions_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: consecutive tls_key_alloc calls return distinct keys' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/wine/thread_sffi_extensions_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: tls_key_set and tls_key_get round-trip a value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
