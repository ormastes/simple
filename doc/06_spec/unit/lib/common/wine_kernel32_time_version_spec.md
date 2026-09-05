# Wine Kernel32 Time Version Specification

> Tests covering Wine KERNEL32 time and version bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Time Version Specification

## Scenarios

### Wine KERNEL32 time and version bridge

#### executes a bounded time and version sequence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes a bounded time and version sequence
   - Expected: result.ok is true
   - Expected: result.tick_count_ms equals `1234`
   - Expected: result.performance_counter equals `987654321`
   - Expected: result.performance_frequency equals `10000000`
   - Expected: result.version_text equals `6.1.7601`
   - Expected: result.platform_id equals `VER_PLATFORM_WIN32_NT`
   - Expected: result.operations equals `GetTickCount QueryPerformanceCounter QueryPerformanceFrequency GetVersion Get... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a bounded time and version sequence")
val result = wine_kernel32_execute_time_version(
    ["GetTickCount", "QueryPerformanceCounter", "QueryPerformanceFrequency", "GetVersion", "GetVersionExW"],
    wine_kernel32_time_version_clock_default()
)

expect(result.ok).to_equal(true)
expect(result.tick_count_ms).to_equal(1234)
expect(result.performance_counter).to_equal(987654321)
expect(result.performance_frequency).to_equal(10000000)
expect(result.version_text).to_equal("6.1.7601")
expect(result.platform_id).to_equal("VER_PLATFORM_WIN32_NT")
expect(result.operations).to_equal("GetTickCount QueryPerformanceCounter QueryPerformanceFrequency GetVersion GetVersionExW")
```

</details>

#### keeps time/version dispatch ordered and bounded

- keeps time/version dispatch ordered and bounded
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-time-version-sequence-expected:GetTickCount`
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps time/version dispatch ordered and bounded")
val out_of_order = wine_kernel32_execute_time_version(
    ["QueryPerformanceCounter", "GetTickCount", "QueryPerformanceFrequency", "GetVersion", "GetVersionExW"],
    wine_kernel32_time_version_clock_default()
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-time-version-sequence-expected:GetTickCount")

val wrong_family = wine_kernel32_execute_time_version(
    ["GetTickCount", "QueryPerformanceCounter", "QueryPerformanceFrequency", "GetVersion", "HeapAlloc"],
    wine_kernel32_time_version_clock_default()
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects invalid clock inputs

- rejects invalid clock inputs
   - Expected: result.ok is false
   - Expected: result.error equals `QueryPerformanceFrequency:invalid-frequency`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid clock inputs")
val clock = WineKernel32TimeVersionClock(
    tick_count_ms: 1,
    performance_counter: 2,
    performance_frequency: 0,
    version_major: 6,
    version_minor: 1,
    version_build: 7601,
    platform_id: "VER_PLATFORM_WIN32_NT"
)
val result = wine_kernel32_execute_time_version(
    ["GetTickCount", "QueryPerformanceCounter", "QueryPerformanceFrequency", "GetVersion", "GetVersionExW"],
    clock
)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("QueryPerformanceFrequency:invalid-frequency")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_kernel32_time_version_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine KERNEL32 time and version bridge.
- Wine KERNEL32 time and version bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `998ca45b296b61c8cf40895da780d04535339483a2ff07c7dc586ad8c5bbfefe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `998ca45b296b61c8cf40895da780d04535339483a2ff07c7dc586ad8c5bbfefe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `998ca45b296b61c8cf40895da780d04535339483a2ff07c7dc586ad8c5bbfefe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/wine_kernel32_time_version_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_kernel32_time_version_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_kernel32_time_version_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_kernel32_time_version_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_kernel32_time_version_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_kernel32_time_version_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a bounded time and version sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_kernel32_time_version_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps time/version dispatch ordered and bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_kernel32_time_version_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid clock inputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
