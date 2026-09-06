# Wine Kernel32 Process Identity Specification

> Tests covering Wine KERNEL32 process identity bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Process Identity Specification

## Scenarios

### Wine KERNEL32 process identity bridge

#### executes bounded process and thread identity calls

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes bounded process and thread identity calls
   - Expected: result.ok is true
   - Expected: result.process_id equals `0x40`
   - Expected: result.thread_id equals `0x80`
   - Expected: result.process_handle equals `-1`
   - Expected: result.thread_handle equals `-2`
   - Expected: result.operations equals `GetCurrentProcessId GetCurrentThreadId GetCurrentProcess GetCurrentThread`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executes bounded process and thread identity calls")
val result = wine_kernel32_execute_process_identity(
    ["GetCurrentProcessId", "GetCurrentThreadId", "GetCurrentProcess", "GetCurrentThread"],
    wine_kernel32_process_identity_default()
)

expect(result.ok).to_equal(true)
expect(result.process_id).to_equal(0x40)
expect(result.thread_id).to_equal(0x80)
expect(result.process_handle).to_equal(-1)
expect(result.thread_handle).to_equal(-2)
expect(result.operations).to_equal("GetCurrentProcessId GetCurrentThreadId GetCurrentProcess GetCurrentThread")
```

</details>

#### keeps identity dispatch ordered and bounded

- keeps identity dispatch ordered and bounded
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-process-identity-sequence-expected:GetCurrentProcessId`
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps identity dispatch ordered and bounded")
val out_of_order = wine_kernel32_execute_process_identity(
    ["GetCurrentThreadId", "GetCurrentProcessId", "GetCurrentProcess", "GetCurrentThread"],
    wine_kernel32_process_identity_default()
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-process-identity-sequence-expected:GetCurrentProcessId")

val wrong_family = wine_kernel32_execute_process_identity(
    ["GetCurrentProcessId", "GetCurrentThreadId", "GetCurrentProcess", "HeapAlloc"],
    wine_kernel32_process_identity_default()
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects invalid identity values

- rejects invalid identity values
   - Expected: result.ok is false
   - Expected: result.error equals `GetCurrentProcessId:invalid-process-id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid identity values")
val identity = WineKernel32ProcessIdentity(process_id: 0, thread_id: 0x80, process_handle: -1, thread_handle: -2)
val result = wine_kernel32_execute_process_identity(
    ["GetCurrentProcessId", "GetCurrentThreadId", "GetCurrentProcess", "GetCurrentThread"],
    identity
)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("GetCurrentProcessId:invalid-process-id")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_process_identity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine KERNEL32 process identity bridge.
- Wine KERNEL32 process identity bridge

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c4504333c88c30e3c6d05b3af4ab113526b45808c6cc458d56750caf3c1205ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c4504333c88c30e3c6d05b3af4ab113526b45808c6cc458d56750caf3c1205ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c4504333c88c30e3c6d05b3af4ab113526b45808c6cc458d56750caf3c1205ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/wine_kernel32_process_identity_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_kernel32_process_identity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_kernel32_process_identity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_kernel32_process_identity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_kernel32_process_identity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_kernel32_process_identity_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes bounded process and thread identity calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_kernel32_process_identity_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps identity dispatch ordered and bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_kernel32_process_identity_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid identity values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
