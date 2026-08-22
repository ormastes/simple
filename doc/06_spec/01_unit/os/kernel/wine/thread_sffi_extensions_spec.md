# thread_sffi_extensions_spec

> Verifies the thread sffi extensions behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# thread_sffi_extensions_spec

Verifies the thread sffi extensions behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/wine/thread_sffi_extensions_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the thread sffi extensions behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### thread_sffi extensions — TLS keys, semaphore, event-wait

### AC-3: tls_key_alloc / set / get — per-thread storage

#### AC-3: tls_key_alloc returns a positive key

- Verify: AC-3: tls_key_alloc returns a positive key


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: tls_key_alloc returns a positive key")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
fn no_destructor(p: *void) -> void:
    val _ = 0
val key = tls_key_alloc(no_destructor)
expect(key).to_be_greater_than(0)
```

</details>

#### AC-3: consecutive tls_key_alloc calls return distinct keys

- Verify: AC-3: consecutive tls_key_alloc calls return distinct keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: consecutive tls_key_alloc calls return distinct keys")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
fn no_destructor(p: *void) -> void:
    val _ = 0
val k1 = tls_key_alloc(no_destructor)
val k2 = tls_key_alloc(no_destructor)
expect(k1).to_not_equal(k2)
```

</details>

#### AC-3: tls_key_set and tls_key_get round-trip a value

- Verify: AC-3: tls_key_set and tls_key_get round-trip a value
   - Expected: got equals `0xABCD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: tls_key_set and tls_key_get round-trip a value")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
fn no_destructor(p: *void) -> void:
    val _ = 0
val key = tls_key_alloc(no_destructor)
tls_key_set(key, 0xABCD)
val got = tls_key_get(key)
expect(got).to_equal(0xABCD)
```

</details>

#### AC-3: tls_key_get on unused key returns null (0)

- Verify: AC-3: tls_key_get on unused key returns null (0)
   - Expected: got equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: tls_key_get on unused key returns null (0)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
fn no_destructor(p: *void) -> void:
    val _ = 0
val key = tls_key_alloc(no_destructor)
val got = tls_key_get(key)
expect(got).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-3: tls_key_set overwrite updates the stored value

- Verify: AC-3: tls_key_set overwrite updates the stored value
   - Expected: got equals `0x22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: tls_key_set overwrite updates the stored value")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: AC-3: semaphore_create with initial=0 returns a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: semaphore_create with initial=0 returns a valid handle")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = semaphore_create(0)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: semaphore_create with initial=1 returns a valid handle

- Verify: AC-3: semaphore_create with initial=1 returns a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: semaphore_create with initial=1 returns a valid handle")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = semaphore_create(1)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: semaphore_create returns distinct handles

- Verify: AC-3: semaphore_create returns distinct handles


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: semaphore_create returns distinct handles")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h1 = semaphore_create(0)
val h2 = semaphore_create(0)
expect(h1).to_not_equal(h2)
```

</details>

#### AC-3: semaphore_wait with initial=1 and timeout_ns=0 returns signaled

- Verify: AC-3: semaphore_wait with initial=1 and timeout_ns=0 returns signaled
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: semaphore_wait with initial=1 and timeout_ns=0 returns signaled")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = semaphore_create(1)
val result = semaphore_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### AC-3: semaphore_wait on zero-count semaphore with timeout_ns=0 returns timeout

- Verify: AC-3: semaphore_wait on zero-count semaphore with timeout_ns=0 returns timeout
   - Expected: result equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: semaphore_wait on zero-count semaphore with timeout_ns=0 returns timeout")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = semaphore_create(0)
val result = semaphore_wait(h, 0)
expect(result).to_equal("timeout")
```

</details>

#### AC-3: semaphore_post followed by semaphore_wait returns signaled

- Verify: AC-3: semaphore_post followed by semaphore_wait returns signaled
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: semaphore_post followed by semaphore_wait returns signaled")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = semaphore_create(0)
semaphore_post(h)
val result = semaphore_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### AC-3: semaphore count decrements after successful wait

- Verify: AC-3: semaphore count decrements after successful wait
   - Expected: r1 equals `signaled`
   - Expected: r2 equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: semaphore count decrements after successful wait")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: AC-3: event_wait_create with manual_reset=false returns a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: event_wait_create with manual_reset=false returns a valid handle")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = event_wait_create(false)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: event_wait_create with manual_reset=true returns a valid handle

- Verify: AC-3: event_wait_create with manual_reset=true returns a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: event_wait_create with manual_reset=true returns a valid handle")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = event_wait_create(true)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: event_wait_wait on unset event with timeout_ns=0 returns timeout

- Verify: AC-3: event_wait_wait on unset event with timeout_ns=0 returns timeout
   - Expected: result equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: event_wait_wait on unset event with timeout_ns=0 returns timeout")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = event_wait_create(false)
val result = event_wait_wait(h, 0)
expect(result).to_equal("timeout")
```

</details>

#### AC-3: event_wait_set then event_wait_wait returns signaled

- Verify: AC-3: event_wait_set then event_wait_wait returns signaled
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: event_wait_set then event_wait_wait returns signaled")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = event_wait_create(false)
event_wait_set(h)
val result = event_wait_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### AC-3: manual-reset event remains set after first wait

- Verify: AC-3: manual-reset event remains set after first wait
   - Expected: r1 equals `signaled`
   - Expected: r2 equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: manual-reset event remains set after first wait")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = event_wait_create(true)
event_wait_set(h)
val r1 = event_wait_wait(h, 0)
expect(r1).to_equal("signaled")
val r2 = event_wait_wait(h, 0)
expect(r2).to_equal("signaled")
```

</details>

#### AC-3: auto-reset event is consumed after first wait

- Verify: AC-3: auto-reset event is consumed after first wait
   - Expected: r1 equals `signaled`
   - Expected: r2 equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: auto-reset event is consumed after first wait")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = event_wait_create(false)
event_wait_set(h)
val r1 = event_wait_wait(h, 0)
expect(r1).to_equal("signaled")
val r2 = event_wait_wait(h, 0)
expect(r2).to_equal("timeout")
```

</details>

#### AC-3: event_wait_reset on set event causes next wait to timeout

- Verify: AC-3: event_wait_reset on set event causes next wait to timeout
   - Expected: result equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: event_wait_reset on set event causes next wait to timeout")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = event_wait_create(true)
event_wait_set(h)
event_wait_reset(h)
val result = event_wait_wait(h, 0)
expect(result).to_equal("timeout")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1e87fb4ee9ee30db570f59ee37e51ac6c860356e544c8377c8d50a126e454884`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1e87fb4ee9ee30db570f59ee37e51ac6c860356e544c8377c8d50a126e454884`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1e87fb4ee9ee30db570f59ee37e51ac6c860356e544c8377c8d50a126e454884`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/kernel/wine/thread_sffi_extensions_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/wine/thread_sffi_extensions_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/wine/thread_sffi_extensions_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/kernel/wine/thread_sffi_extensions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/wine/thread_sffi_extensions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
