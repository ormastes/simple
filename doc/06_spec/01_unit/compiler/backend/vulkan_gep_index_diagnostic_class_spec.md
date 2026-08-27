# Vulkan Gep Index Diagnostic Class Specification

> Tests covering Vulkan GEP index diagnostic class.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Gep Index Diagnostic Class Specification

## Scenarios

### Vulkan GEP index diagnostic class

#### positive control: the backend really emits SPIR-V for a legal shared GEP

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- positive control: the backend really emits SPIR-V for a legal shared GEP
   - Expected: ok.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positive control: the backend really emits SPIR-V for a legal shared GEP")
val ok = vk_shared_gep(vk_const(3, vk_u32()), [])
expect(ok.is_ok()).to_equal(true)
val output = ok.unwrap()
expect(output).to_contain("OpEntryPoint")
expect(output).to_contain("OpAccessChain")
```

</details>

#### accepts both integer index kinds SPIR-V can index with

- accepts both integer index kinds SPIR-V can index with
   - Expected: vk_shared_gep(vk_const(3, vk_u32()), []).is_ok() is true
   - Expected: vk_shared_gep(vk_const(3, vk_i64()), []).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts both integer index kinds SPIR-V can index with")
expect(vk_shared_gep(vk_const(3, vk_u32()), []).is_ok()).to_equal(true)
expect(vk_shared_gep(vk_const(3, vk_i64()), []).is_ok()).to_equal(true)
```

</details>

#### rejects a non-U32/I64 index kind with the index-type diagnostic

- rejects a non-U32/I64 index kind with the index-type diagnostic
   - Expected: bad.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a non-U32/I64 index kind with the index-type diagnostic")
val bad = vk_shared_gep(vk_op(2), [vk_temp(2, vk_i32())])
expect(bad.is_err()).to_equal(true)
expect(bad.unwrap_err().message).to_contain("index must be U32")
```

</details>

#### reports the allocation-bound failure before any value-resolution failure

- reports the allocation-bound failure before any value-resolution failure
   - Expected: oob.is_err() is true
   - Expected: unproven.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the allocation-bound failure before any value-resolution failure")
# index 16 is a legal U32 constant but out of range for a 16-element
# allocation: the bound diagnostic must win.
val oob = vk_shared_gep(vk_const(16, vk_u32()), [])
expect(oob.is_err()).to_equal(true)
expect(oob.unwrap_err().message).to_contain("not proven within the allocation")

# an in-range-looking but unproven local index must report the same
# bound diagnostic, not an incidental "operand has no value".
val unproven = vk_shared_gep(vk_op(2), [vk_temp(2, vk_u32())])
expect(unproven.is_err()).to_equal(true)
expect(unproven.unwrap_err().message).to_contain("not proven within the allocation")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/vulkan_gep_index_diagnostic_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Vulkan GEP index diagnostic class.
- Vulkan GEP index diagnostic class

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

- Canonical SPipe generation for source `53ae1f4f6084bd877ed6e7487aa8d3f46b2a9b41e3d8008fbd0687f2da5e1fb2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `53ae1f4f6084bd877ed6e7487aa8d3f46b2a9b41e3d8008fbd0687f2da5e1fb2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `53ae1f4f6084bd877ed6e7487aa8d3f46b2a9b41e3d8008fbd0687f2da5e1fb2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/vulkan_gep_index_diagnostic_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/vulkan_gep_index_diagnostic_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/vulkan_gep_index_diagnostic_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/vulkan_gep_index_diagnostic_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/vulkan_gep_index_diagnostic_class_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'positive control: the backend really emits SPIR-V for a legal shared GEP' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/vulkan_gep_index_diagnostic_class_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts both integer index kinds SPIR-V can index with' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/vulkan_gep_index_diagnostic_class_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a non-U32/I64 index kind with the index-type diagnostic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
