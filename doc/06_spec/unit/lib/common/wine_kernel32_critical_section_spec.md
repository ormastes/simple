# Wine Kernel32 Critical Section Specification

> Tests covering Wine KERNEL32 critical-section bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Critical Section Specification

## Scenarios

### Wine KERNEL32 critical-section bridge

#### executes a bounded initialize, enter, leave, and delete sequence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes a bounded initialize, enter, leave, and delete sequence
   - Expected: result.ok is true
   - Expected: result.handle equals `0x300`
   - Expected: result.table.sections.len() equals `0`
   - Expected: result.operations equals `InitializeCriticalSection EnterCriticalSection LeaveCriticalSection DeleteCri... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a bounded initialize, enter, leave, and delete sequence")
val result = wine_kernel32_execute_critical_section(
    ["InitializeCriticalSection", "EnterCriticalSection", "LeaveCriticalSection", "DeleteCriticalSection"],
    wine_kernel32_critical_section_table_new(),
    "loader-lock"
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x300)
expect(result.table.sections.len()).to_equal(0)
expect(result.operations).to_equal("InitializeCriticalSection EnterCriticalSection LeaveCriticalSection DeleteCriticalSection")
```

</details>

#### keeps critical-section dispatch ordered and bounded

- keeps critical-section dispatch ordered and bounded
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-critical-section-sequence-expected:InitializeCriticalSection`
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps critical-section dispatch ordered and bounded")
val out_of_order = wine_kernel32_execute_critical_section(
    ["EnterCriticalSection", "InitializeCriticalSection", "LeaveCriticalSection", "DeleteCriticalSection"],
    wine_kernel32_critical_section_table_new(),
    "loader-lock"
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-critical-section-sequence-expected:InitializeCriticalSection")

val wrong_family = wine_kernel32_execute_critical_section(
    ["InitializeCriticalSection", "EnterCriticalSection", "LeaveCriticalSection", "HeapAlloc"],
    wine_kernel32_critical_section_table_new(),
    "loader-lock"
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects unnamed critical sections in the bounded startup path

- rejects unnamed critical sections in the bounded startup path
   - Expected: result.ok is false
   - Expected: result.error equals `InitializeCriticalSection:invalid-name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unnamed critical sections in the bounded startup path")
val result = wine_kernel32_execute_critical_section(
    ["InitializeCriticalSection", "EnterCriticalSection", "LeaveCriticalSection", "DeleteCriticalSection"],
    wine_kernel32_critical_section_table_new(),
    ""
)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("InitializeCriticalSection:invalid-name")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_kernel32_critical_section_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine KERNEL32 critical-section bridge.
- Wine KERNEL32 critical-section bridge

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

- Canonical SPipe generation for source `b3c5bc901336740a78e02f92b2868fd017c2c6f83b9e0c3460ded66b38245741`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b3c5bc901336740a78e02f92b2868fd017c2c6f83b9e0c3460ded66b38245741`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b3c5bc901336740a78e02f92b2868fd017c2c6f83b9e0c3460ded66b38245741`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/common/wine_kernel32_critical_section_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_kernel32_critical_section_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_kernel32_critical_section_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_kernel32_critical_section_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_kernel32_critical_section_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_kernel32_critical_section_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a bounded initialize, enter, leave, and delete sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_kernel32_critical_section_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps critical-section dispatch ordered and bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_kernel32_critical_section_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unnamed critical sections in the bounded startup path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
