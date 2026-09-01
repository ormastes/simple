# Wine Kernel32 Error State Specification

> Tests covering Wine KERNEL32 error-state bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Error State Specification

## Scenarios

### Wine KERNEL32 error-state bridge

#### sets, gets, and formats a bounded last-error code

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sets, gets, and formats a bounded last-error code
   - Expected: result.ok is true
   - Expected: result.code equals `87`
   - Expected: result.state.symbol equals `ERROR_INVALID_PARAMETER`
   - Expected: result.message equals `The parameter is incorrect.`
   - Expected: result.operations equals `SetLastError GetLastError FormatMessageW`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sets, gets, and formats a bounded last-error code")
val result = wine_kernel32_execute_error_state(
    ["SetLastError", "GetLastError", "FormatMessageW"],
    wine_kernel32_error_state_new(),
    87
)

expect(result.ok).to_equal(true)
expect(result.code).to_equal(87)
expect(result.state.symbol).to_equal("ERROR_INVALID_PARAMETER")
expect(result.message).to_equal("The parameter is incorrect.")
expect(result.operations).to_equal("SetLastError GetLastError FormatMessageW")
```

</details>

#### exposes direct error-state helpers

- exposes direct error-state helpers
   - Expected: fetched.ok is true
   - Expected: fetched.code equals `2`
   - Expected: fetched.message equals `ERROR_FILE_NOT_FOUND`
   - Expected: formatted.message equals `The system cannot find the file specified.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes direct error-state helpers")
val updated = wine_kernel32_set_last_error(wine_kernel32_error_state_new(), 2)
val fetched = wine_kernel32_get_last_error(updated)
val formatted = wine_kernel32_format_message_w(updated, fetched.code)

expect(fetched.ok).to_equal(true)
expect(fetched.code).to_equal(2)
expect(fetched.message).to_equal("ERROR_FILE_NOT_FOUND")
expect(formatted.message).to_equal("The system cannot find the file specified.")
```

</details>

#### keeps error-state dispatch ordered and bounded

- keeps error-state dispatch ordered and bounded
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-error-state-sequence-expected:SetLastError`
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps error-state dispatch ordered and bounded")
val out_of_order = wine_kernel32_execute_error_state(
    ["GetLastError", "SetLastError", "FormatMessageW"],
    wine_kernel32_error_state_new(),
    87
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-error-state-sequence-expected:SetLastError")

val wrong_family = wine_kernel32_execute_error_state(
    ["SetLastError", "GetLastError", "HeapAlloc"],
    wine_kernel32_error_state_new(),
    87
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects invalid modeled error codes

- rejects invalid modeled error codes
   - Expected: result.ok is false
   - Expected: result.error equals `SetLastError:invalid-error-code`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid modeled error codes")
val result = wine_kernel32_execute_error_state(
    ["SetLastError", "GetLastError", "FormatMessageW"],
    wine_kernel32_error_state_new(),
    -1
)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("SetLastError:invalid-error-code")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_error_state_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine KERNEL32 error-state bridge.
- Wine KERNEL32 error-state bridge

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `53d2f2a9448214f8dd56cc921d251c336585b3d43aaeb7d51eec034548571c67`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `53d2f2a9448214f8dd56cc921d251c336585b3d43aaeb7d51eec034548571c67`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `53d2f2a9448214f8dd56cc921d251c336585b3d43aaeb7d51eec034548571c67`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/wine_kernel32_error_state_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_kernel32_error_state_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_kernel32_error_state_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_kernel32_error_state_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_kernel32_error_state_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_kernel32_error_state_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets, gets, and formats a bounded last-error code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_kernel32_error_state_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes direct error-state helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_kernel32_error_state_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps error-state dispatch ordered and bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
