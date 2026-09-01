# C Codegen Adapter Bootstrap Compat Specification

> Tests covering C codegen adapter bootstrap grammar compatibility.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# C Codegen Adapter Bootstrap Compat Specification

## Scenarios

### C codegen adapter bootstrap grammar compatibility

#### declares its unconditional MirToC dependency without statement-form when

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- declares its unconditional MirToC dependency without statement-form when
   - Expected: source does not contain `when not BOOTSTRAP_NO_C:`
   - Expected: source does not contain `BOOTSTRAP_NO_C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declares its unconditional MirToC dependency without statement-form when")
val source = rt_file_read_text("src/compiler/70.backend/backend/c_codegen_adapter.spl") ?? ""

expect(source).to_contain("use compiler.backend.c_backend.\{MirToC\}")
expect(source.contains("when not BOOTSTRAP_NO_C:")).to_equal(false)
expect(source.contains("BOOTSTRAP_NO_C")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/c_codegen_adapter_bootstrap_compat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering C codegen adapter bootstrap grammar compatibility.
- C codegen adapter bootstrap grammar compatibility

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f99f3722500032d8ae06c821fee508482f2e81afb8c6d0810579ab3aa9670306`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f99f3722500032d8ae06c821fee508482f2e81afb8c6d0810579ab3aa9670306`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f99f3722500032d8ae06c821fee508482f2e81afb8c6d0810579ab3aa9670306`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/backend/c_codegen_adapter_bootstrap_compat_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/c_codegen_adapter_bootstrap_compat_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/backend/c_codegen_adapter_bootstrap_compat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/c_codegen_adapter_bootstrap_compat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/c_codegen_adapter_bootstrap_compat_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/backend/c_codegen_adapter_bootstrap_compat_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares its unconditional MirToC dependency without statement-form when' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
