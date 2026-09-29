# Loader Exec Memory Specification

> Tests covering Exec memory mapping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Loader Exec Memory Specification

## Scenarios

### Exec memory mapping

#### x86_64 only

#### skips on non-x86_64 hosts

- skips on non-x86_64 hosts


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("skips on non-x86_64 hosts")
expect true
```

</details>

#### maps executable memory and runs a tiny function

- maps executable memory and runs a tiny function
   - Expected: written equals `code.len() as i64`
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("maps executable memory and runs a tiny function")
# Machine code: mov eax, 42; ret
val code: [u8] = [184, 42, 0, 0, 0, 195]

val addr = native_alloc_exec_memory(code.len() as i64)
assert_true(addr > 0)

val written = native_write_exec_memory(addr, code, 0)
expect(written).to_equal(code.len() as i64)

val made_exec = native_make_executable(addr, code.len() as i64)
assert_true(made_exec)

val result = native_call_function_0(addr)
expect(result).to_equal(42)

val freed = native_free_exec_memory(addr, code.len() as i64)
assert_true(freed)
```

</details>

#### fails gracefully on oversized allocation

- fails gracefully on oversized allocation
   - Expected: addr equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails gracefully on oversized allocation")
val huge_size = 1_099_511_627_776i64  # 1 TB
val addr = native_alloc_exec_memory(huge_size)
expect(addr).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/loader_exec_memory_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Exec memory mapping.
- Exec memory mapping

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `55307cb27d0d6b5c446fe4a2ce0c9b1c8981e20cdcb25650b0237fd2b3a68411`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `55307cb27d0d6b5c446fe4a2ce0c9b1c8981e20cdcb25650b0237fd2b3a68411`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `55307cb27d0d6b5c446fe4a2ce0c9b1c8981e20cdcb25650b0237fd2b3a68411`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/app/loader_exec_memory_spec.spl
mirror: doc/06_spec/integration/app/loader_exec_memory_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/loader_exec_memory_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/loader_exec_memory_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/loader_exec_memory_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/loader_exec_memory_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips on non-x86_64 hosts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/loader_exec_memory_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps executable memory and runs a tiny function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/loader_exec_memory_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails gracefully on oversized allocation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
