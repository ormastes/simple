# Manual Mode Specification

> Tests covering Manual Mode Execution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Manual Mode Specification

## Scenarios

### Manual Mode Execution

#### is in manual mode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is in manual mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is in manual mode")
val mode = async_mode()
expect mode == "manual"
```

</details>

#### futures are pending until polled

- futures are pending until polled


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("futures are pending until polled")
val f = future(42)
# In manual mode, future doesn't execute until polled
val completed = poll_future(f)
expect completed
expect await f == 42
```

</details>

#### polling multiple futures individually

- polling multiple futures individually


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("polling multiple futures individually")
val f1 = future(10)
val f2 = future(20)
# Poll each future
poll_future(f1)
poll_future(f2)
expect await f1 == 10
expect await f2 == 20
```

</details>

#### await auto-polls in manual mode

- await auto-polls in manual mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("await auto-polls in manual mode")
val f = future(100)
# await should auto-poll if needed
expect await f == 100
```

</details>

#### resolved futures work in manual mode

- resolved futures work in manual mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolved futures work in manual mode")
val f = resolved(42)
expect is_ready(f)
expect await f == 42
```

</details>

#### futures with captures in manual mode

- futures with captures in manual mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("futures with captures in manual mode")
val base = 40
val f = future(base + 2)
poll_future(f)
expect await f == 42
```

</details>

#### computation in manual mode

- computation in manual mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computation in manual mode")
val f = future(10 + 20 + 30)
poll_future(f)
expect await f == 60
```

</details>

#### multiple captures in manual mode

- multiple captures in manual mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple captures in manual mode")
val a = 10
val b = 20
val c = 12
val f = future(a + b + c)
poll_future(f)
expect await f == 42
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/manual_mode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Manual Mode Execution.
- Manual Mode Execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `5cbd5e128ffb496341e5e043f8da7f4d02a7f2837d5e16f6330a9107ccb50a2f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5cbd5e128ffb496341e5e043f8da7f4d02a7f2837d5e16f6330a9107ccb50a2f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5cbd5e128ffb496341e5e043f8da7f4d02a7f2837d5e16f6330a9107ccb50a2f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/std/manual_mode_spec.spl
mirror: doc/06_spec/01_unit/std/manual_mode_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/manual_mode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/manual_mode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/manual_mode_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is in manual mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/manual_mode_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'futures are pending until polled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/manual_mode_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'polling multiple futures individually' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
