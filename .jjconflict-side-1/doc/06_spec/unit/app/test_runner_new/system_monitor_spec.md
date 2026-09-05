# System Monitor Specification

> Tests covering System Monitor.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# System Monitor Specification

## Scenarios

### System Monitor

#### detects platform flags as booleans

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects platform flags as booleans
   - Expected: linux == true or linux == false is true
   - Expected: macos == true or macos == false is true
   - Expected: windows == true or windows == false is true
   - Expected: freebsd == true or freebsd == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects platform flags as booleans")
val linux = is_linux()
val macos = is_macos()
val windows = is_windows()
val freebsd = is_freebsd()

expect(linux == true or linux == false).to_equal(true)
expect(macos == true or macos == false).to_equal(true)
expect(windows == true or windows == false).to_equal(true)
expect(freebsd == true or freebsd == false).to_equal(true)
```

</details>

#### returns non-negative system resource metrics

- returns non-negative system resource metrics
   - Expected: res.cpu_percent >= 0.0 is true
   - Expected: res.memory_percent >= 0.0 is true
   - Expected: res.memory_used_mb >= 0 is true
   - Expected: res.memory_total_mb >= 0 is true
   - Expected: res.memory_used_mb <= res.memory_total_mb is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-negative system resource metrics")
val res = get_system_resources()

expect(res.cpu_percent >= 0.0).to_equal(true)
expect(res.memory_percent >= 0.0).to_equal(true)
expect(res.memory_used_mb >= 0).to_equal(true)
expect(res.memory_total_mb >= 0).to_equal(true)

if res.memory_total_mb > 0:
    expect(res.memory_used_mb <= res.memory_total_mb).to_equal(true)
```

</details>

#### returns cpu and memory percentages directly

- returns cpu and memory percentages directly
   - Expected: cpu >= 0.0 is true
   - Expected: memory >= 0.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns cpu and memory percentages directly")
val cpu = get_system_cpu_percent()
val memory = get_system_memory_percent()

expect(cpu >= 0.0).to_equal(true)
expect(memory >= 0.0).to_equal(true)
```

</details>

#### only reports threshold violations when both limits are exceeded

- only reports threshold violations when both limits are exceeded
   - Expected: safe is false
   - Expected: safe_reason equals ``
   - Expected: violated is true
   - Expected: violated_reason != "" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only reports threshold violations when both limits are exceeded")
val (safe, safe_reason) = system_exceeds_threshold(101.0, 101.0)
val (violated, violated_reason) = system_exceeds_threshold(-1.0, -1.0)

expect(safe).to_equal(false)
expect(safe_reason).to_equal("")
expect(violated).to_equal(true)
expect(violated_reason != "").to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/test_runner_new/system_monitor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering System Monitor.
- System Monitor

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

- Canonical SPipe generation for source `12031db5655223f44f5dd4eada570a3bbffdeea2091c9b2b1b7e66de41009bd7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `12031db5655223f44f5dd4eada570a3bbffdeea2091c9b2b1b7e66de41009bd7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `12031db5655223f44f5dd4eada570a3bbffdeea2091c9b2b1b7e66de41009bd7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/test_runner_new/system_monitor_spec.spl
mirror: doc/06_spec/unit/app/test_runner_new/system_monitor_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_runner_new/system_monitor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_runner_new/system_monitor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_runner_new/system_monitor_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects platform flags as booleans' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/system_monitor_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns non-negative system resource metrics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/system_monitor_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns cpu and memory percentages directly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
