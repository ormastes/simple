# Spm Port Specification

> Tests covering spm_port.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spm Port Specification

## Scenarios

### spm_port

#### starts unregistered

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### register accepts a task id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
val ok = spm_port_register(42 as u64)
expect(ok).to_equal(true)
expect(spm_port_is_registered()).to_equal(true)
expect(spm_port_registered_task()).to_equal(42 as u64)
```

</details>

#### register is idempotent for the same task

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
spm_port_register(7 as u64)
val again = spm_port_register(7 as u64)
expect(again).to_equal(true)
```

</details>

#### register rejects a second distinct task

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
spm_port_register(7 as u64)
val ok = spm_port_register(8 as u64)
expect(ok).to_equal(false)
```

</details>

#### listen on empty inbox returns empty bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
val r = spm_port_listen()
expect(r.len()).to_equal(0)
```

</details>

#### send enqueues a request

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
val req: [u8] = [1 as u8, 2 as u8, 3 as u8]
spm_port_send(req)
val got = spm_port_listen()
expect(got.len()).to_equal(3)
```

</details>

#### send returns the last stashed response

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
val resp: [u8] = [9 as u8, 9 as u8]
spm_port_post_response(resp)
val req: [u8] = [1 as u8]
val r = spm_port_send(req)
expect(r.len()).to_equal(2)
```

</details>

#### FIFO: first in first out

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
val a: [u8] = [1 as u8]
val b: [u8] = [2 as u8, 2 as u8]
spm_port_send(a)
spm_port_send(b)
val first = spm_port_listen()
val second = spm_port_listen()
expect(first.len()).to_equal(1)
expect(second.len()).to_equal(2)
```

</details>

#### listen drains the inbox

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
spm_port_send([1 as u8])
spm_port_listen()
val again = spm_port_listen()
expect(again.len()).to_equal(0)
```

</details>

#### reset clears state

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_register(1 as u64)
spm_port_send([1 as u8])
spm_port_reset()
expect(spm_port_is_registered()).to_equal(false)
expect(spm_port_listen().len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/ipc/spm_port_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering spm_port.
- spm_port

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `77fb094c8233ed40f47ba86a703c75e0fad6c6f36002a03a6983a6e1c6ec178e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `77fb094c8233ed40f47ba86a703c75e0fad6c6f36002a03a6983a6e1c6ec178e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `77fb094c8233ed40f47ba86a703c75e0fad6c6f36002a03a6983a6e1c6ec178e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/unit/os/kernel/ipc/spm_port_spec.spl
mirror: doc/06_spec/unit/os/kernel/ipc/spm_port_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/ipc/spm_port_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/ipc/spm_port_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/ipc/spm_port_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/os/kernel/ipc/spm_port_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/ipc/spm_port_spec.spl:13:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'starts unregistered' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/os/kernel/ipc/spm_port_spec.spl:19:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'register accepts a task id' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/os/kernel/ipc/spm_port_spec.spl:26:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'register is idempotent for the same task' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/os/kernel/ipc/spm_port_spec.spl:32:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'register rejects a second distinct task' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
