# Wine Kernel32 Startup Info Specification

> Tests covering Wine KERNEL32 startup info bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Startup Info Specification

## Scenarios

### Wine KERNEL32 startup info bridge

#### executes bounded startup info and standard handle discovery

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes bounded startup info and standard handle discovery
   - Expected: result.ok is true
   - Expected: result.show_window equals `1`
   - Expected: result.std_input equals `-10`
   - Expected: result.std_output equals `-11`
   - Expected: result.std_error equals `-12`
   - Expected: result.desktop equals `winsta0\\default`
   - Expected: result.operations equals `GetStartupInfoW GetStdHandle GetStdHandle GetStdHandle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes bounded startup info and standard handle discovery")
val result = wine_kernel32_execute_startup_info(
    ["GetStartupInfoW", "GetStdHandle", "GetStdHandle", "GetStdHandle"],
    wine_kernel32_startup_info_default()
)

expect(result.ok).to_equal(true)
expect(result.show_window).to_equal(1)
expect(result.std_input).to_equal(-10)
expect(result.std_output).to_equal(-11)
expect(result.std_error).to_equal(-12)
expect(result.desktop).to_equal("winsta0\\default")
expect(result.operations).to_equal("GetStartupInfoW GetStdHandle GetStdHandle GetStdHandle")
```

</details>

#### keeps startup info dispatch ordered and bounded

- keeps startup info dispatch ordered and bounded
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-startup-info-sequence-expected:GetStartupInfoW`
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps startup info dispatch ordered and bounded")
val out_of_order = wine_kernel32_execute_startup_info(
    ["GetStdHandle", "GetStartupInfoW", "GetStdHandle", "GetStdHandle"],
    wine_kernel32_startup_info_default()
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-startup-info-sequence-expected:GetStartupInfoW")

val wrong_family = wine_kernel32_execute_startup_info(
    ["GetStartupInfoW", "GetStdHandle", "GetStdHandle", "HeapAlloc"],
    wine_kernel32_startup_info_default()
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects invalid standard handle models

- rejects invalid standard handle models
   - Expected: result.ok is false
   - Expected: result.error equals `GetStdHandle:invalid-stdout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid standard handle models")
val info = WineKernel32StartupInfo(show_window: 1, std_input: -10, std_output: 99, std_error: -12, desktop: "winsta0\\default", title: "SimpleOS Wine")
val result = wine_kernel32_execute_startup_info(
    ["GetStartupInfoW", "GetStdHandle", "GetStdHandle", "GetStdHandle"],
    info
)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("GetStdHandle:invalid-stdout")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_kernel32_startup_info_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine KERNEL32 startup info bridge.
- Wine KERNEL32 startup info bridge

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

- Canonical SPipe generation for source `073d6a5062801361a7997569f74545425de5ce76eb014100358e8dc347d1f510`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `073d6a5062801361a7997569f74545425de5ce76eb014100358e8dc347d1f510`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `073d6a5062801361a7997569f74545425de5ce76eb014100358e8dc347d1f510`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/wine_kernel32_startup_info_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_kernel32_startup_info_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_kernel32_startup_info_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_kernel32_startup_info_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_kernel32_startup_info_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_kernel32_startup_info_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes bounded startup info and standard handle discovery' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_kernel32_startup_info_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps startup info dispatch ordered and bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_kernel32_startup_info_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid standard handle models' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
