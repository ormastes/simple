# Contract spec: test/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.spl` and a green Results line.

## Scenarios

### LLVM IR builder target header lifetime

#### reconstructs a local target instead of retaining the composite triple

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reconstructs a local target instead of retaining the composite triple


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reconstructs a local target instead of retaining the composite triple")
val source = file_read("src/compiler/70.backend/backend/llvm_ir_builder.spl")

expect(source).to_contain("val target = LlvmTargetTriple.from_target(llvm_builder_target())")
expect(source).to_contain("val header_target = if mir_target_context_os_from(requested, \"\") == \"baremetal\":")
expect(source).to_contain("var target_triple_text = \"{header_target.arch}-{header_target.vendor}-{header_target.os}\"")
expect(source).to_not_contain("\n    target: LlvmTargetTriple\n")        expect(source).to_not_contain("self.target.")        expect(source).to_not_contain("header_target.to_text()")
```

</details>

#### emits the exact GNU target after the create boundary

- emits the exact GNU target after the create boundary


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
expect(header).to_not_contain("<invalid-heap:")
```

</details>

#### omits an absent environment without retaining the optional payload

- omits an absent environment without retaining the optional payload


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
expect(header).to_not_contain("none-\"")
```

</details>

#### preserves the SimpleOS target through header emission

- preserves the SimpleOS target through header emission


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
expect(header).to_not_contain("<invalid-heap:")
```

</details>

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0bcf16734791a453408686e6b30de1c7260432f2991804c984f0f0b55441fcd0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0bcf16734791a453408686e6b30de1c7260432f2991804c984f0f0b55441fcd0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0bcf16734791a453408686e6b30de1c7260432f2991804c984f0f0b55441fcd0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reconstructs a local target instead of retaining the composite triple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits the exact GNU target after the create boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'omits an absent environment without retaining the optional payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
