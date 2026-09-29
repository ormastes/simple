# Engine Divergence Mutation Class Specification

> Tests covering engine-divergent container mutation (defect class).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Divergence Mutation Class Specification

## Scenarios

### engine-divergent container mutation (defect class)

#### keeps every mut-parameter container mutation on the interpreter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps every mut-parameter container mutation on the interpreter
   - Expected: shape_lines(out).len() equals `8`
   - Expected: discarded_shapes(out).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("keeps every mut-parameter container mutation on the interpreter")
val out = run_probe_in_mode("interpreter")
expect(out).to_contain("PROBE_DONE")
expect(shape_lines(out).len()).to_equal(8)
expect(discarded_shapes(out).len()).to_equal(0)
```

</details>

#### keeps every mut-parameter container mutation on the jit, and agrees with the interpreter

- keeps every mut-parameter container mutation on the jit, and agrees with the interpreter
   - Expected: shape_lines(jit).len() equals `8`
   - Expected: discarded_shapes(jit).len() equals `0`
   - Expected: shape_lines(jit).join("|") equals `shape_lines(interp).join("|")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("keeps every mut-parameter container mutation on the jit, and agrees with the interpreter")
val jit = run_probe_in_mode("jit")
expect(jit).to_contain("PROBE_DONE")
expect(shape_lines(jit).len()).to_equal(8)
expect(discarded_shapes(jit).len()).to_equal(0)
val interp = run_probe_in_mode("interpreter")
expect(shape_lines(jit).join("|")).to_equal(shape_lines(interp).join("|"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/engine_divergence_mutation_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering engine-divergent container mutation (defect class).
- engine-divergent container mutation (defect class)

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

- `REQ-SSPEC-LANGUAGE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a1a38a4ff2a61345f895404ccc8ba89174e748fb8bdcb7c7bfe3bc362682e799`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a1a38a4ff2a61345f895404ccc8ba89174e748fb8bdcb7c7bfe3bc362682e799`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a1a38a4ff2a61345f895404ccc8ba89174e748fb8bdcb7c7bfe3bc362682e799`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/language/engine_divergence_mutation_class_spec.spl
mirror: doc/06_spec/01_unit/language/engine_divergence_mutation_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/engine_divergence_mutation_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/engine_divergence_mutation_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/engine_divergence_mutation_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/language/engine_divergence_mutation_class_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every mut-parameter container mutation on the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/engine_divergence_mutation_class_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every mut-parameter container mutation on the jit, and agrees with the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
