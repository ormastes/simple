# Wine Kernel32 Thread Wait Specification

> Tests covering Wine KERNEL32 thread/wait bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Thread Wait Specification

## Scenarios

### Wine KERNEL32 thread/wait bridge

#### executes a bounded CreateThread, WaitForSingleObject, and GetLastError sequence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes a bounded CreateThread, WaitForSingleObject, and GetLastError sequence
   - Expected: result.ok is true
   - Expected: result.handle equals `0x80`
   - Expected: result.wait_status equals `WAIT_OBJECT_0`
   - Expected: result.exit_code equals `7`
   - Expected: result.last_error equals `OK`
   - Expected: result.operations equals `CreateThread WaitForSingleObject GetLastError`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a bounded CreateThread, WaitForSingleObject, and GetLastError sequence")
val result = wine_kernel32_execute_thread_wait(
    ["CreateThread", "WaitForSingleObject", "GetLastError"],
    wine_nt_thread_table_new(_all_thread_apis()),
    "main",
    7,
    1000
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x80)
expect(result.wait_status).to_equal("WAIT_OBJECT_0")
expect(result.exit_code).to_equal(7)
expect(result.last_error).to_equal("OK")
expect(result.operations).to_equal("CreateThread WaitForSingleObject GetLastError")
```

</details>

#### keeps thread/wait dispatch ordered and bounded

- keeps thread/wait dispatch ordered and bounded
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-thread-wait-sequence-expected:CreateThread`
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapFree`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps thread/wait dispatch ordered and bounded")
val out_of_order = wine_kernel32_execute_thread_wait(
    ["WaitForSingleObject", "CreateThread", "GetLastError"],
    wine_nt_thread_table_new(_all_thread_apis()),
    "main",
    0,
    1000
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-thread-wait-sequence-expected:CreateThread")

val wrong_family = wine_kernel32_execute_thread_wait(
    ["CreateThread", "WaitForSingleObject", "HeapFree"],
    wine_nt_thread_table_new(_all_thread_apis()),
    "main",
    0,
    1000
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapFree")
```

</details>

#### propagates thread readiness and CreateThread errors

- propagates thread readiness and CreateThread errors
   - Expected: blocked.ok is false
   - Expected: blocked.error equals `CreateThread:missing-api-thread-detach`
   - Expected: invalid.ok is false
   - Expected: invalid.error equals `CreateThread:invalid-entrypoint`
   - Expected: invalid.last_error equals `ERROR_INVALID_PARAMETER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates thread readiness and CreateThread errors")
val blocked = wine_kernel32_execute_thread_wait(
    ["CreateThread", "WaitForSingleObject", "GetLastError"],
    wine_nt_thread_table_new("thread-create thread-join"),
    "main",
    0,
    1000
)
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("CreateThread:missing-api-thread-detach")

val invalid = wine_kernel32_execute_thread_wait(
    ["CreateThread", "WaitForSingleObject", "GetLastError"],
    wine_nt_thread_table_new(_all_thread_apis()),
    "",
    0,
    1000
)
expect(invalid.ok).to_equal(false)
expect(invalid.error).to_equal("CreateThread:invalid-entrypoint")
expect(invalid.last_error).to_equal("ERROR_INVALID_PARAMETER")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_kernel32_thread_wait_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine KERNEL32 thread/wait bridge.
- Wine KERNEL32 thread/wait bridge

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

- Canonical SPipe generation for source `a429e785d549631e621d2ade32a38cd669e89f9bf21c1acf9568b177e2e986dd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a429e785d549631e621d2ade32a38cd669e89f9bf21c1acf9568b177e2e986dd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a429e785d549631e621d2ade32a38cd669e89f9bf21c1acf9568b177e2e986dd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/common/wine_kernel32_thread_wait_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_kernel32_thread_wait_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_kernel32_thread_wait_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_kernel32_thread_wait_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_kernel32_thread_wait_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_kernel32_thread_wait_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a bounded CreateThread, WaitForSingleObject, and GetLastError sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_kernel32_thread_wait_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps thread/wait dispatch ordered and bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_kernel32_thread_wait_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates thread readiness and CreateThread errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
