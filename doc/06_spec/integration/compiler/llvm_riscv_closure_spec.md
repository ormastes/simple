# Llvm Riscv Closure Specification

> Tests covering riscv64 closure, riscv32 closure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Riscv Closure Specification

## Scenarios

### riscv64 closure

#### llvm-lib riscv64 is stable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- llvm-lib riscv64 is stable
   - Expected: level.to_text() equals `stable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("llvm-lib riscv64 is stable")
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.Riscv64)
expect(level.to_text()).to_equal("stable")
```

</details>

#### llvm CLI riscv64 is stable

- llvm CLI riscv64 is stable
   - Expected: level.to_text() equals `stable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("llvm CLI riscv64 is stable")
val level = lookup_support(BackendKind.Llvm, CodegenTarget.Riscv64)
expect(level.to_text()).to_equal("stable")
```

</details>

#### riscv64 levels are final states

- riscv64 levels are final states
   - Expected: lib_level.is_final_state() is true
   - Expected: cli_level.is_final_state() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("riscv64 levels are final states")
val lib_level = lookup_support(BackendKind.LlvmLib, CodegenTarget.Riscv64)
val cli_level = lookup_support(BackendKind.Llvm, CodegenTarget.Riscv64)
expect(lib_level.is_final_state()).to_equal(true)
expect(cli_level.is_final_state()).to_equal(true)
```

</details>

### riscv32 closure

#### llvm-lib riscv32 is unsupported

- llvm-lib riscv32 is unsupported
   - Expected: level.to_text() equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("llvm-lib riscv32 is unsupported")
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.Riscv32)
expect(level.to_text()).to_equal("unsupported")
```

</details>

#### llvm CLI riscv32 is unsupported

- llvm CLI riscv32 is unsupported
   - Expected: level.to_text() equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("llvm CLI riscv32 is unsupported")
val level = lookup_support(BackendKind.Llvm, CodegenTarget.Riscv32)
expect(level.to_text()).to_equal("unsupported")
```

</details>

#### riscv32 unsupported has clear diagnostic

- riscv32 unsupported has clear diagnostic


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("riscv32 unsupported has clear diagnostic")
val matrix = get_support_matrix()
for entry in matrix:
    if entry.target == CodegenTarget.Riscv32:
        expect(entry.known_limits).to_contain("Demoted to unsupported")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/integration/compiler/llvm_riscv_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering riscv64 closure, riscv32 closure.
- riscv64 closure
- riscv32 closure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `5822e9f588774c74dafa571ce137a7141144d1b98cc8647a6f30c92e326b6c0a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5822e9f588774c74dafa571ce137a7141144d1b98cc8647a6f30c92e326b6c0a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5822e9f588774c74dafa571ce137a7141144d1b98cc8647a6f30c92e326b6c0a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/compiler/llvm_riscv_closure_spec.spl
mirror: doc/06_spec/integration/compiler/llvm_riscv_closure_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/llvm_riscv_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/compiler/llvm_riscv_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/llvm_riscv_closure_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'llvm-lib riscv64 is stable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/llvm_riscv_closure_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'llvm CLI riscv64 is stable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/llvm_riscv_closure_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'riscv64 levels are final states' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
