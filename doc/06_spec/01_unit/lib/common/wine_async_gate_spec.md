# Wine Async Gate Specification

> Tests covering Wine async substrate gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Async Gate Specification

## Scenarios

### Wine async substrate gate

#### reports missing nogc future support first

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports missing nogc future support first
   - Expected: wine_async_gate("poll waker io-driver") equals `missing-nogc-future`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports missing nogc future support first")
expect(wine_async_gate("poll waker io-driver")).to_equal("missing-nogc-future")
```

</details>

#### accepts the full nogc async readiness set

- accepts the full nogc async readiness set
   - Expected: wine_async_gate(features) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the full nogc async readiness set")
val features = "nogc-future poll waker io-driver submit-open submit-read submit-write submit-close " +
    "submit-timeout poll-completion event-loop register-fd deregister-fd wake noalloc-capability"
expect(wine_async_gate(features)).to_equal("ready")
```

</details>

#### requires completion-driver file operations

- requires completion-driver file operations
   - Expected: wine_async_io_gate(features) equals `missing-poll-completion`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires completion-driver file operations")
val features = "io-driver submit-open submit-read submit-write submit-close submit-timeout"
expect(wine_async_io_gate(features)).to_equal("missing-poll-completion")
```

</details>

<details>
<summary>Advanced: requires event loop registration and wake support</summary>

#### requires event loop registration and wake support

- requires event loop registration and wake support
   - Expected: wine_async_event_loop_gate(features) equals `missing-deregister-fd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires event loop registration and wake support")
val features = "event-loop register-fd waker"
expect(wine_async_event_loop_gate(features)).to_equal("missing-deregister-fd")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_async_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine async substrate gate.
- Wine async substrate gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `4db8feba2a59fb6195a039fe115ca89bd66d72914b28eaa2266869c7779dc93b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4db8feba2a59fb6195a039fe115ca89bd66d72914b28eaa2266869c7779dc93b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4db8feba2a59fb6195a039fe115ca89bd66d72914b28eaa2266869c7779dc93b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/wine_async_gate_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_async_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_async_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_async_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_async_gate_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports missing nogc future support first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_async_gate_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the full nogc async readiness set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_async_gate_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires completion-driver file operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
