# Callable Dependency Route Precedence Contract Specification

> Tests covering callable dependency route precedence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Callable Dependency Route Precedence Contract Specification

## Scenarios

### callable dependency route precedence

#### prefers explicit named routes and retains ambiguity checks within one precedence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- prefers explicit named routes and retains ambiguity checks within one precedence


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("prefers explicit named routes and retains ambiguity checks within one precedence")
val source = file_read("src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl")
expect(source).to_contain("var selected_route_is_named = false")
expect(source).to_contain("if selected_target >= 0 and not selected_route_is_named")
expect(source).to_contain("if selected_target >= 0 and selected_route_is_named")
expect(source).to_contain("selected_route_is_named = true")
expect(source).to_contain("ambiguous explicit callable dependency")
```

</details>

#### keeps HIR ASM field spellings on their source declaration names

- keeps HIR ASM field spellings on their source declaration names
   - Expected: source does not contain `FrontendAsmTargetSpec`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps HIR ASM field spellings on their source declaration names")
val source = file_read("src/compiler/20.hir/hir_definitions.spl")
expect(source).to_contain("use compiler.frontend.parser_types_expr.{AsmTargetSpec, AsmConstraintKind, AsmLocation}")
expect(source).to_contain("AsmAssert(spec: AsmTargetSpec)")
expect(source.contains("FrontendAsmTargetSpec")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/callable_dependency_route_precedence_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering callable dependency route precedence.
- callable dependency route precedence

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4df58043661f60cb8f2e7a472e77ccc8a395192a9280804d46275e51c972475a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4df58043661f60cb8f2e7a472e77ccc8a395192a9280804d46275e51c972475a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4df58043661f60cb8f2e7a472e77ccc8a395192a9280804d46275e51c972475a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/bootstrap/callable_dependency_route_precedence_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/callable_dependency_route_precedence_contract_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/bootstrap/callable_dependency_route_precedence_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/callable_dependency_route_precedence_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/callable_dependency_route_precedence_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/bootstrap/callable_dependency_route_precedence_contract_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefers explicit named routes and retains ambiguity checks within one precedence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/callable_dependency_route_precedence_contract_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps HIR ASM field spellings on their source declaration names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
