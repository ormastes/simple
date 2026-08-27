# Field Default Container Mutation Specification

> Tests covering container field holding its declared empty default.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Field Default Container Mutation Specification

## Scenarios

### container field holding its declared empty default

#### keeps mutations on the interpreter (control arm)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps mutations on the interpreter (control arm)
- Run the probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter was measured correct on 2026-08-17; a red here means the probe is broken, not the engine
- The probe must actually have executed its checks, not exited early


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps mutations on the interpreter (control arm)")
step("Run the probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter was measured correct on 2026-08-17; a red here means the probe is broken, not the engine")
expect(interp).to_contain("FIELD_DEFAULT_CONTAINER PROBE: ALL PASS")

step("The probe must actually have executed its checks, not exited early")
expect(interp).to_contain("PASS class_default_array_method_push")
```

</details>

#### keeps mutations under the cranelift JIT

- keeps mutations under the cranelift JIT
- Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the bug lives in
- A struct field declared `var arr: [str] = []` must retain a push
- Explicit read-modify-writeback through a local must also land — proving no writeback rule can paper over this
- The canonical accumulator idiom — a class method appending to its own `[]`-defaulted field
- A `{}`-defaulted dict must accept an insert and report len 1, not the -1 sentinel
- No check may have failed


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps mutations under the cranelift JIT")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the bug lives in")
val jit = run_probe_in_mode("jit")

step("A struct field declared `var arr: [str] = []` must retain a push")
expect(jit).to_contain("PASS struct_default_array_push")

step("Explicit read-modify-writeback through a local must also land — proving no writeback rule can paper over this")
expect(jit).to_contain("PASS struct_default_array_explicit_writeback")

step("The canonical accumulator idiom — a class method appending to its own `[]`-defaulted field")
expect(jit).to_contain("PASS class_default_array_method_push")
expect(jit).to_contain("PASS class_default_array_direct_push")

step("A `{}`-defaulted dict must accept an insert and report len 1, not the -1 sentinel")
expect(jit).to_contain("PASS class_default_dict_insert")

step("No check may have failed")
expect(jit).to_contain("FIELD_DEFAULT_CONTAINER PROBE: ALL PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/field_default_container_mutation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering container field holding its declared empty default.
- container field holding its declared empty default

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

- Canonical SPipe generation for source `eb1ab2e2207e717cfcc42dc430758662795865626c128baa9c4703d9de714bb4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb1ab2e2207e717cfcc42dc430758662795865626c128baa9c4703d9de714bb4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb1ab2e2207e717cfcc42dc430758662795865626c128baa9c4703d9de714bb4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/compiler/codegen/field_default_container_mutation_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/field_default_container_mutation_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/field_default_container_mutation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/field_default_container_mutation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/field_default_container_mutation_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps mutations on the interpreter (control arm)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/field_default_container_mutation_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps mutations under the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
