# spm_port_spec

> Verifies the spm port behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spm_port_spec

Verifies the spm port behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/spm_port_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the spm port behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### spm_port

#### starts unregistered

- Verify: starts unregistered
   - Expected: spm_port_is_registered() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-IPC_SPM_PORT-001
step("Verify: starts unregistered")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
spm_port_reset()
expect(spm_port_is_registered()).to_equal(false)
```

</details>

#### register accepts a task id

- Verify: register accepts a task id
   - Expected: ok is true
   - Expected: spm_port_is_registered() is true
   - Expected: spm_port_registered_task() equals `42 as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-IPC_SPM_PORT-001
step("Verify: register accepts a task id")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
spm_port_reset()
val ok = spm_port_register(42 as u64)
expect(ok).to_equal(true)
expect(spm_port_is_registered()).to_equal(true)
expect(spm_port_registered_task()).to_equal(42 as u64)
```

</details>

#### register is idempotent for the same task

- Verify: register is idempotent for the same task
   - Expected: again is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-IPC_SPM_PORT-001
step("Verify: register is idempotent for the same task")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
spm_port_reset()
spm_port_register(7 as u64)
val again = spm_port_register(7 as u64)
expect(again).to_equal(true)
```

</details>

#### register rejects a second distinct task

- Verify: register rejects a second distinct task
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-IPC_SPM_PORT-001
step("Verify: register rejects a second distinct task")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
spm_port_reset()
spm_port_register(7 as u64)
val ok = spm_port_register(8 as u64)
expect(ok).to_equal(false)
```

</details>

#### listen on empty inbox returns empty bytes

- Verify: listen on empty inbox returns empty bytes
   - Expected: r.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-IPC_SPM_PORT-001
step("Verify: listen on empty inbox returns empty bytes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
spm_port_reset()
val r = spm_port_listen()
expect(r.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### send enqueues a request

- Verify: send enqueues a request
   - Expected: got.len() equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-IPC_SPM_PORT-001
step("Verify: send enqueues a request")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
spm_port_reset()
val req: [u8] = [1 as u8, 2 as u8, 3 as u8]
spm_port_send(req)
val got = spm_port_listen()
expect(got.len()).to_equal(3)  # oracle: pinned constant asserted by this scenario
```

</details>

#### send returns the last stashed response

- Verify: send returns the last stashed response
   - Expected: r.len() equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-IPC_SPM_PORT-001
step("Verify: send returns the last stashed response")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
spm_port_reset()
val resp: [u8] = [9 as u8, 9 as u8]
spm_port_post_response(resp)
val req: [u8] = [1 as u8]
val r = spm_port_send(req)
expect(r.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

#### FIFO: first in first out

- Verify: FIFO: first in first out
   - Expected: first.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: second.len() equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-IPC_SPM_PORT-001
step("Verify: FIFO: first in first out")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
spm_port_reset()
val a: [u8] = [1 as u8]
val b: [u8] = [2 as u8, 2 as u8]
spm_port_send(a)
spm_port_send(b)
val first = spm_port_listen()
val second = spm_port_listen()
expect(first.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(second.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

#### listen drains the inbox

- Verify: listen drains the inbox
   - Expected: again.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-IPC_SPM_PORT-001
step("Verify: listen drains the inbox")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
spm_port_reset()
spm_port_send([1 as u8])
spm_port_listen()
val again = spm_port_listen()
expect(again.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### reset clears state

- Verify: reset clears state
   - Expected: spm_port_is_registered() is false
   - Expected: spm_port_listen().len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-IPC_SPM_PORT-001
step("Verify: reset clears state")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
spm_port_register(1 as u64)
spm_port_send([1 as u8])
spm_port_reset()
expect(spm_port_is_registered()).to_equal(false)
expect(spm_port_listen().len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `da43263446b3cd60bdb928b8ec1be889433488625198d28747d3e1b053a50e17`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da43263446b3cd60bdb928b8ec1be889433488625198d28747d3e1b053a50e17`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da43263446b3cd60bdb928b8ec1be889433488625198d28747d3e1b053a50e17`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/kernel/ipc/spm_port_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/ipc/spm_port_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/ipc/spm_port_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/kernel/ipc/spm_port_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/ipc/spm_port_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
