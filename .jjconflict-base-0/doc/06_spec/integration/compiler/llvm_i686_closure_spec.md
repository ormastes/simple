# Llvm I686 Closure Specification

> Tests covering i686 closure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm I686 Closure Specification

## Scenarios

### i686 closure

#### llvm-lib i686 is unsupported

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- llvm-lib i686 is unsupported
   - Expected: level.to_text() equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("llvm-lib i686 is unsupported")
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.X86)
expect(level.to_text()).to_equal("unsupported")
```

</details>

#### llvm CLI i686 is unsupported

- llvm CLI i686 is unsupported
   - Expected: level.to_text() equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("llvm CLI i686 is unsupported")
val level = lookup_support(BackendKind.Llvm, CodegenTarget.X86)
expect(level.to_text()).to_equal("unsupported")
```

</details>

#### i686 level is a final state

- i686 level is a final state
   - Expected: level.is_final_state() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("i686 level is a final state")
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.X86)
expect(level.is_final_state()).to_equal(true)
```

</details>

#### i686 unsupported has clear diagnostic

- i686 unsupported has clear diagnostic


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("i686 unsupported has clear diagnostic")
val matrix = get_support_matrix()
for entry in matrix:
    if entry.target == CodegenTarget.X86:
        expect(entry.known_limits).to_contain("Demoted to unsupported")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/integration/compiler/llvm_i686_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering i686 closure.
- i686 closure

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0dbbf3fc65a5a47be3e181d487452e3694e388b70d381f832cf4f6f3f01c2bc5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0dbbf3fc65a5a47be3e181d487452e3694e388b70d381f832cf4f6f3f01c2bc5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0dbbf3fc65a5a47be3e181d487452e3694e388b70d381f832cf4f6f3f01c2bc5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/compiler/llvm_i686_closure_spec.spl
mirror: doc/06_spec/integration/compiler/llvm_i686_closure_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/llvm_i686_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/compiler/llvm_i686_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/llvm_i686_closure_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'llvm-lib i686 is unsupported' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/llvm_i686_closure_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'llvm CLI i686 is unsupported' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/llvm_i686_closure_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'i686 level is a final state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
