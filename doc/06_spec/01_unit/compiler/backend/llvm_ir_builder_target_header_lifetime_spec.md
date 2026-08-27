# Llvm Ir Builder Target Header Lifetime Specification

> Tests covering LLVM IR builder target header lifetime.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Ir Builder Target Header Lifetime Specification

## Scenarios

### LLVM IR builder target header lifetime

#### reconstructs a local target instead of retaining the composite triple

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reconstructs a local target instead of retaining the composite triple
   - Expected: source does not contain `\n    target: LlvmTargetTriple\n`
   - Expected: source does not contain `self.target.`
   - Expected: source does not contain `header_target.to_text()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reconstructs a local target instead of retaining the composite triple")
val source = file_read("src/compiler/70.backend/backend/llvm_ir_builder.spl")

expect(source).to_contain("val target = LlvmTargetTriple.from_target(llvm_builder_target())")
expect(source).to_contain("val header_target = if mir_target_context_os_from(requested, \"\") == \"baremetal\":")
expect(source).to_contain("var target_triple_text = \"{header_target.arch}-{header_target.vendor}-{header_target.os}\"")
expect(source.contains("\n    target: LlvmTargetTriple\n")).to_equal(false)
expect(source.contains("self.target.")).to_equal(false)
expect(source.contains("header_target.to_text()")).to_equal(false)
```

</details>

#### emits the exact GNU target after the create boundary

- emits the exact GNU target after the create boundary
   - Expected: header does not contain `<invalid-heap:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits the exact GNU target after the create boundary")
val target = LlvmTargetTriple(
    arch: "x86_64", vendor: "unknown", os: "linux", env: Some("gnu")
)
val header = emitted_target_header("x86_64-unknown-linux-gnu", target)

expect(header).to_contain("target datalayout = \"e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128\"")
expect(header).to_contain("target triple = \"x86_64-unknown-linux-gnu\"")
expect(header.contains("<invalid-heap:")).to_equal(false)
```

</details>

#### omits an absent environment without retaining the optional payload

- omits an absent environment without retaining the optional payload
   - Expected: header does not contain `none-"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("omits an absent environment without retaining the optional payload")
val target = LlvmTargetTriple(
    arch: "aarch64", vendor: "unknown", os: "none", env: nil
)
val header = emitted_target_header("aarch64-unknown-none", target)

expect(header).to_contain("target datalayout = \"e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32\"")
expect(header).to_contain("target triple = \"aarch64-unknown-none\"")
expect(header.contains("none-\"")).to_equal(false)
```

</details>

#### preserves the SimpleOS target through header emission

- preserves the SimpleOS target through header emission
   - Expected: header does not contain `<invalid-heap:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves the SimpleOS target through header emission")
val target = LlvmTargetTriple.from_target(CodegenTarget.SimpleOS_X86_64)
val header = emitted_target_header("x86_64-unknown-simpleos", target)

expect(header).to_contain("target datalayout = \"e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128\"")
expect(header).to_contain("target triple = \"x86_64-unknown-simpleos\"")
expect(header.contains("<invalid-heap:")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLVM IR builder target header lifetime.
- LLVM IR builder target header lifetime

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
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e40b145a2babf47a13a432fd7dc4f31947c55406c4b6b080e2fca24512062bb7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e40b145a2babf47a13a432fd7dc4f31947c55406c4b6b080e2fca24512062bb7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e40b145a2babf47a13a432fd7dc4f31947c55406c4b6b080e2fca24512062bb7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reconstructs a local target instead of retaining the composite triple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits the exact GNU target after the create boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'omits an absent environment without retaining the optional payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
