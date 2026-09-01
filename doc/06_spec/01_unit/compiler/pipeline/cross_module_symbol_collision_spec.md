# Cross Module Symbol Collision Specification

> Tests covering cross-module same-name symbol collision.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cross Module Symbol Collision Specification

## Scenarios

### cross-module same-name symbol collision

#### resolves each module's calls against its own definitions on the interpreter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves each module's calls against its own definitions on the interpreter
- Run the two-module collision probe under SIMPLE_EXECUTION_MODE=interpreter
- The probe must actually have run — a truncated or killed run prints none of these
- A private `_`-prefixed helper must resolve within its own defining module, in both directions
- The same must hold for a PUBLIC free function — the defect is not specific to the `_` prefix
- Differing arity must not collapse either: b_calls_arity() passes one argument and must not reach A's zero-parameter body with the argument silently discarded
- Overall verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves each module's calls against its own definitions on the interpreter")
step("Run the two-module collision probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The probe must actually have run — a truncated or killed run prints none of these")
expect(interp).to_contain("a_private")
expect(interp).to_contain("b_private")

step("A private `_`-prefixed helper must resolve within its own defining module, in both directions")
expect(interp).to_contain("PASS a_private")
expect(interp).to_contain("PASS b_private")

step("The same must hold for a PUBLIC free function — the defect is not specific to the `_` prefix")
expect(interp).to_contain("PASS a_public")
expect(interp).to_contain("PASS b_public")

step("Differing arity must not collapse either: b_calls_arity() passes one argument and must not reach A's zero-parameter body with the argument silently discarded")
expect(interp).to_contain("PASS a_arity")
expect(interp).to_contain("PASS b_arity")

step("Overall verdict")
expect(interp).to_contain("XMOD_COLLISION PROBE: ALL PASS")
```

</details>

#### resolves each module's calls against its own definitions on the cranelift JIT

- resolves each module's calls against its own definitions on the cranelift JIT
- Run the same probe under SIMPLE_EXECUTION_MODE=jit — codegen resolves the same flat registry and is first-import-wins too
- The probe must actually have run
- Every wrapper must reach its own module's definition under the JIT as well
- Overall verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves each module's calls against its own definitions on the cranelift JIT")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit — codegen resolves the same flat registry and is first-import-wins too")
val jit = run_probe_in_mode("jit")

step("The probe must actually have run")
expect(jit).to_contain("a_private")

step("Every wrapper must reach its own module's definition under the JIT as well")
expect(jit).to_contain("PASS a_private")
expect(jit).to_contain("PASS b_private")
expect(jit).to_contain("PASS a_public")
expect(jit).to_contain("PASS b_public")
expect(jit).to_contain("PASS a_arity")
expect(jit).to_contain("PASS b_arity")

step("Overall verdict")
expect(jit).to_contain("XMOD_COLLISION PROBE: ALL PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/pipeline/cross_module_symbol_collision_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering cross-module same-name symbol collision.
- cross-module same-name symbol collision

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

- Canonical SPipe generation for source `6689fdfdeaab43ac318a062750af20b2b4f7d7ff6fb9e3ba2ed64b764e932a7f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6689fdfdeaab43ac318a062750af20b2b4f7d7ff6fb9e3ba2ed64b764e932a7f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6689fdfdeaab43ac318a062750af20b2b4f7d7ff6fb9e3ba2ed64b764e932a7f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/compiler/pipeline/cross_module_symbol_collision_spec.spl
mirror: doc/06_spec/01_unit/compiler/pipeline/cross_module_symbol_collision_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/pipeline/cross_module_symbol_collision_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/pipeline/cross_module_symbol_collision_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/pipeline/cross_module_symbol_collision_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves each module's calls against its own definitions on the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/pipeline/cross_module_symbol_collision_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves each module's calls against its own definitions on the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
