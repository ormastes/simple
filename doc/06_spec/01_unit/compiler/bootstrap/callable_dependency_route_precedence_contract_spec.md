# Contract spec: test/01_unit/compiler/bootstrap/callable_dependency_route_precedence_contract_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/bootstrap/callable_dependency_route_precedence_contract_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/callable_dependency_route_precedence_contract_spec.spl` |
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
`bin/simple test test/01_unit/compiler/bootstrap/callable_dependency_route_precedence_contract_spec.spl` and a green Results line.

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
expect(source).to_not_contain("FrontendAsmTargetSpec")
```

</details>

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

- Canonical SPipe generation for source `66c9a188e01173be48c098f863678d6b821a00d98cc65f05d46bfea4759c0f13`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `66c9a188e01173be48c098f863678d6b821a00d98cc65f05d46bfea4759c0f13`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `66c9a188e01173be48c098f863678d6b821a00d98cc65f05d46bfea4759c0f13`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/compiler/bootstrap/callable_dependency_route_precedence_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/callable_dependency_route_precedence_contract_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/bootstrap/callable_dependency_route_precedence_contract_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefers explicit named routes and retains ambiguity checks within one precedence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/callable_dependency_route_precedence_contract_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps HIR ASM field spellings on their source declaration names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
