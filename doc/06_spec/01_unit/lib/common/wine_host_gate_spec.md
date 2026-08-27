# Wine Host Gate Specification

> Tests covering Wine host substrate gate, overall host features, specific service gates.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Host Gate Specification

## Scenarios

### Wine host substrate gate

### overall host features

#### lists POSIX, thread, loader, and service features

- lists POSIX, thread, loader, and service features
   - Expected: required[0] equals `fd-table`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists POSIX, thread, loader, and service features")
val required = wine_host_required_features()
expect(required.len()).to_be_greater_than(20)
expect(required[0]).to_equal("fd-table")
```

</details>

#### reports the first missing host feature

- reports the first missing host feature
   - Expected: state equals `missing-fs-attrs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the first missing host feature")
val state = wine_host_gate("fd-table stdio pipes sockets poll-wait timers errno cwd-env-argv spawn fs-paths")
expect(state).to_equal("missing-fs-attrs")
```

</details>

### specific service gates

#### requires real pthread, TLS, synchronization, and fault attribution

- requires real pthread, TLS, synchronization, and fault attribution
   - Expected: state equals `missing-thread-fault`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires real pthread, TLS, synchronization, and fault attribution")
val state = wine_thread_gate("pthread tls mutex condvar semaphore event")
expect(state).to_equal("missing-thread-fault")
```

</details>

#### requires POSIX-shaped fd, wait, timer, env, and spawn services

- requires POSIX-shaped fd, wait, timer, env, and spawn services
   - Expected: state equals `missing-spawn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires POSIX-shaped fd, wait, timer, env, and spawn services")
val state = wine_posix_gate("fd-table stdio pipes sockets poll-wait timers errno cwd-env-argv")
expect(state).to_equal("missing-spawn")
```

</details>

#### requires dynamic loading and structured loader behavior

- requires dynamic loading and structured loader behavior
   - Expected: state equals `missing-loader-errors`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires dynamic loading and structured loader behavior")
val state = wine_dynamic_gate("dynload symbol-lookup relocation")
expect(state).to_equal("missing-loader-errors")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_host_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine host substrate gate, overall host features, specific service gates.
- Wine host substrate gate
- overall host features
- specific service gates

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `4ff819f7b1b2db11d6561c3c09894d564e2ac536df08304e890272a604dc0d08`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4ff819f7b1b2db11d6561c3c09894d564e2ac536df08304e890272a604dc0d08`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4ff819f7b1b2db11d6561c3c09894d564e2ac536df08304e890272a604dc0d08`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/wine_host_gate_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_host_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_host_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_host_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_host_gate_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists POSIX, thread, loader, and service features' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_host_gate_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the first missing host feature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_host_gate_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires real pthread, TLS, synchronization, and fault attribution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
