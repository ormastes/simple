# Wine Ntdll System Info Specification

> Tests covering Wine NTDLL system information bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Ntdll System Info Specification

## Scenarios

### Wine NTDLL system information bridge

#### executes a bounded NtQuerySystemInformation sequence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes a bounded NtQuerySystemInformation sequence
   - Expected: result.ok is true
   - Expected: result.page_size equals `4096`
   - Expected: result.allocation_granularity equals `65536`
   - Expected: result.processor_count equals `4`
   - Expected: result.timer_resolution_100ns equals `156250`
   - Expected: result.system_root equals `C:\\windows`
   - Expected: result.classes equals `SystemBasicInformation SystemProcessorInformation SystemTimeOfDayInformation`
   - Expected: result.operations equals `NtQuerySystemInformation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a bounded NtQuerySystemInformation sequence")
val result = wine_ntdll_execute_system_info(["NtQuerySystemInformation"], _classes(), wine_ntdll_system_info_default())

expect(result.ok).to_equal(true)
expect(result.page_size).to_equal(4096)
expect(result.allocation_granularity).to_equal(65536)
expect(result.processor_count).to_equal(4)
expect(result.timer_resolution_100ns).to_equal(156250)
expect(result.system_root).to_equal("C:\\windows")
expect(result.classes).to_equal("SystemBasicInformation SystemProcessorInformation SystemTimeOfDayInformation")
expect(result.operations).to_equal("NtQuerySystemInformation")
```

</details>

#### keeps system information dispatch and classes bounded

- keeps system information dispatch and classes bounded
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:NtCreateFile`
   - Expected: wrong_class.ok is false
   - Expected: wrong_class.error equals `ntdll-system-info-class-expected:SystemBasicInformation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps system information dispatch and classes bounded")
val wrong_family = wine_ntdll_execute_system_info(["NtCreateFile"], _classes(), wine_ntdll_system_info_default())
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:NtCreateFile")

val wrong_class = wine_ntdll_execute_system_info(["NtQuerySystemInformation"], ["SystemProcessorInformation", "SystemBasicInformation", "SystemTimeOfDayInformation"], wine_ntdll_system_info_default())
expect(wrong_class.ok).to_equal(false)
expect(wrong_class.error).to_equal("ntdll-system-info-class-expected:SystemBasicInformation")
```

</details>

#### rejects invalid system information facts

- rejects invalid system information facts
   - Expected: result.ok is false
   - Expected: result.error equals `NtQuerySystemInformation:invalid-processor-count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid system information facts")
val invalid = WineNtdllSystemInfo(
    page_size: 4096,
    allocation_granularity: 65536,
    processor_count: 0,
    timer_resolution_100ns: 156250,
    system_root: "C:\\windows"
)
val result = wine_ntdll_execute_system_info(["NtQuerySystemInformation"], _classes(), invalid)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("NtQuerySystemInformation:invalid-processor-count")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_ntdll_system_info_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine NTDLL system information bridge.
- Wine NTDLL system information bridge

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

- Canonical SPipe generation for source `b725d04a694e4038d81c498bda34c0b15d066104446e18bf69146421f36647d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b725d04a694e4038d81c498bda34c0b15d066104446e18bf69146421f36647d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b725d04a694e4038d81c498bda34c0b15d066104446e18bf69146421f36647d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/wine_ntdll_system_info_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_ntdll_system_info_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_ntdll_system_info_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_ntdll_system_info_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_ntdll_system_info_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_ntdll_system_info_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a bounded NtQuerySystemInformation sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_ntdll_system_info_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps system information dispatch and classes bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_ntdll_system_info_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid system information facts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
