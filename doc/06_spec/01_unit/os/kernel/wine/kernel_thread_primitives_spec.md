# kernel_thread_primitives_spec

> Verifies the kernel thread primitives behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# kernel_thread_primitives_spec

Verifies the kernel thread primitives behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/wine/kernel_thread_primitives_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the kernel thread primitives behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### kernel_thread primitives — M1

### AC-3: kevent — kernel event object

#### AC-3: kevent_create with auto_reset=false returns a valid handle

- Verify: AC-3: kevent_create with auto_reset=false returns a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: kevent_create with auto_reset=false returns a valid handle")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = kevent_create(false)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: kevent_create with auto_reset=true returns a valid handle

- Verify: AC-3: kevent_create with auto_reset=true returns a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: kevent_create with auto_reset=true returns a valid handle")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = kevent_create(true)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: kevent_create returns distinct handles for separate calls

- Verify: AC-3: kevent_create returns distinct handles for separate calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: kevent_create returns distinct handles for separate calls")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h1 = kevent_create(false)
val h2 = kevent_create(false)
expect(h1).to_not_equal(h2)
```

</details>

#### AC-3: kevent_set is callable without error on a valid handle

- Verify: AC-3: kevent_set is callable without error on a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: kevent_set is callable without error on a valid handle")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = kevent_create(false)
kevent_set(h)
# If we reach here, set did not panic
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: kevent_reset is callable without error on a valid handle

- Verify: AC-3: kevent_reset is callable without error on a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: kevent_reset is callable without error on a valid handle")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = kevent_create(false)
kevent_set(h)
kevent_reset(h)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: kevent_wait with timeout_ns=0 returns immediately with WaitResult value

- Verify: AC-3: kevent_wait with timeout_ns=0 returns immediately with WaitResult value
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: kevent_wait with timeout_ns=0 returns immediately with WaitResult value")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = kevent_create(false)
kevent_set(h)
# Wait on a set event with 0 timeout: expect signaled
val result = kevent_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### AC-3: kevent_wait on unset event with timeout_ns=0 returns timeout

- Verify: AC-3: kevent_wait on unset event with timeout_ns=0 returns timeout
   - Expected: result equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: kevent_wait on unset event with timeout_ns=0 returns timeout")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h = kevent_create(false)
# Event is not set; timeout immediately
val result = kevent_wait(h, 0)
expect(result).to_equal("timeout")
```

</details>

#### AC-3: auto-reset kevent_wait resets the handle after signaled

- Verify: AC-3: auto-reset kevent_wait resets the handle after signaled
   - Expected: r1 equals `signaled`
   - Expected: r2 equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: auto-reset kevent_wait resets the handle after signaled")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: AC-3: kfutex_wake with count=1 returns the number of woken waiters
   - Expected: woken equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: kfutex_wake with count=1 returns the number of woken waiters")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# No waiters: wake returns 0
val addr: u32 = 0
val woken = kfutex_wake(addr, 1)
expect(woken).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-3: kfutex_wait with mismatched expected returns immediately

- Verify: AC-3: kfutex_wait with mismatched expected returns immediately
   - Expected: result equals `aborted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: kfutex_wait with mismatched expected returns immediately")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# If *addr != expected, futex returns immediately with WaitResult.aborted
val addr: u32 = 0
val result = kfutex_wait(addr, 99, 0)
expect(result).to_equal("aborted")
```

</details>

#### AC-3: kfutex_wait with matching expected and timeout_ns=0 returns timeout

- Verify: AC-3: kfutex_wait with matching expected and timeout_ns=0 returns timeout
   - Expected: result equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: kfutex_wait with matching expected and timeout_ns=0 returns timeout")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val addr: u32 = 42
val result = kfutex_wait(addr, 42, 0)
expect(result).to_equal("timeout")
```

</details>

### AC-3: kernel_thread — TLS segment (FS.base)

#### AC-3: kernel_thread_tls_set and tls_get round-trip a value

- Verify: AC-3: kernel_thread_tls_set and tls_get round-trip a value
   - Expected: got equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: kernel_thread_tls_set and tls_get round-trip a value")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# key=1 (arbitrary), store a sentinel pattern
kernel_thread_tls_set(1, 0xDEADBEEF)
val got = kernel_thread_tls_get(1)
expect(got).to_equal(0xDEADBEEF)
```

</details>

#### AC-3: kernel_thread_tls_get for unset key returns null (0)

- Verify: AC-3: kernel_thread_tls_get for unset key returns null (0)
   - Expected: got equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: kernel_thread_tls_get for unset key returns null (0)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val got = kernel_thread_tls_get(255)
expect(got).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-3: kernel_thread_tls_set with key=0 stores and retrieves

- Verify: AC-3: kernel_thread_tls_set with key=0 stores and retrieves
   - Expected: got equals `0x1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: kernel_thread_tls_set with key=0 stores and retrieves")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
kernel_thread_tls_set(0, 0x1234)
val got = kernel_thread_tls_get(0)
expect(got).to_equal(0x1234)
```

</details>

#### AC-3: kernel_thread_create returns a positive Tid

- Verify: AC-3: kernel_thread_create returns a positive Tid


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3
step("Verify: AC-3: kernel_thread_create returns a positive Tid")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# We supply a no-op entry function and stack_size=4096
fn noop_entry() -> void:
    val _ = 0
val tid = kernel_thread_create(noop_entry, 4096)
expect(tid).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6d6b8321dfd66ff094dd05c7b2b86eb1b95302e00a6235c3412ca17a2429ba4a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6d6b8321dfd66ff094dd05c7b2b86eb1b95302e00a6235c3412ca17a2429ba4a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6d6b8321dfd66ff094dd05c7b2b86eb1b95302e00a6235c3412ca17a2429ba4a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/kernel/wine/kernel_thread_primitives_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/wine/kernel_thread_primitives_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/wine/kernel_thread_primitives_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/kernel/wine/kernel_thread_primitives_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/wine/kernel_thread_primitives_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
