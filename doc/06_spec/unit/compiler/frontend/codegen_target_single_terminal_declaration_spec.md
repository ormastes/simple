# Codegen Target Single Terminal Declaration Specification

> Tests covering CodegenTarget has exactly one terminal declaration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Codegen Target Single Terminal Declaration Specification

## Scenarios

### CodegenTarget has exactly one terminal declaration

#### is declared only in compiler.backend.backend.backend_types

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is declared only in compiler.backend.backend.backend_types
   - Expected: terminal equals `1`
   - Expected: frontend equals `0`
   - Expected: facade equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is declared only in compiler.backend.backend.backend_types")
val terminal = codegen_target_decl_count("src/compiler/70.backend/backend/backend_types.spl")
val frontend = codegen_target_decl_count("src/compiler/10.frontend/core/backend_types.spl")
val facade = codegen_target_decl_count("src/compiler/70.backend/backend_types.spl")
expect(terminal).to_equal(1)
expect(frontend).to_equal(0)
expect(facade).to_equal(0)
```

</details>

#### re-exports the terminal variant set through compiler.core.backend_types

- re-exports the terminal variant set through compiler.core.backend_types
   - Expected: CodegenTarget.CudaPtx.to_text() equals `cuda-ptx`
   - Expected: CodegenTarget.Native.to_text() equals `native`
   - Expected: CodegenTarget.Host.to_text() equals `host`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports the terminal variant set through compiler.core.backend_types")
# A GPU target the deleted 13-variant copy never carried.
expect(CodegenTarget.CudaPtx.to_text()).to_equal("cuda-ptx")
# Ordering witnesses: these two swapped places between the copies.
expect(CodegenTarget.Native.to_text()).to_equal("native")
expect(CodegenTarget.Host.to_text()).to_equal("host")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/frontend/codegen_target_single_terminal_declaration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CodegenTarget has exactly one terminal declaration.
- CodegenTarget has exactly one terminal declaration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `3210d746275cc58083219148596786d5103732cb3e4c40eba7b4aa57806234a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3210d746275cc58083219148596786d5103732cb3e4c40eba7b4aa57806234a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3210d746275cc58083219148596786d5103732cb3e4c40eba7b4aa57806234a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/frontend/codegen_target_single_terminal_declaration_spec.spl
mirror: doc/06_spec/unit/compiler/frontend/codegen_target_single_terminal_declaration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/frontend/codegen_target_single_terminal_declaration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/frontend/codegen_target_single_terminal_declaration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/frontend/codegen_target_single_terminal_declaration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/frontend/codegen_target_single_terminal_declaration_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is declared only in compiler.backend.backend.backend_types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/frontend/codegen_target_single_terminal_declaration_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports the terminal variant set through compiler.core.backend_types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
