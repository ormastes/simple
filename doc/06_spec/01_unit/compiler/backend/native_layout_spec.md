# Native Layout Specification

> Tests covering Native Layout.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Layout Specification

## Scenarios

### Native Layout

#### infers startup and cold phases from function names

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- infers startup and cold phases from function names
   - Expected: names_in_phase(plan, LayoutPhase.Startup) equals `["init_runtime"]`
   - Expected: names_in_phase(plan, LayoutPhase.Cold) equals `["error_handler"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers startup and cold phases from function names")
val module = make_module([
    make_function("init_runtime", nil, 1),
    make_function("error_handler", nil, 2)
])

val plan = solve_layout(module, nil)

expect(names_in_phase(plan, LayoutPhase.Startup)).to_equal(["init_runtime"])
expect(names_in_phase(plan, LayoutPhase.Cold)).to_equal(["error_handler"])
```

</details>

#### respects explicit layout phase overrides

- respects explicit layout phase overrides
   - Expected: names_in_phase(plan, LayoutPhase.FirstFrame) equals `["regular_worker"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("respects explicit layout phase overrides")
val module = make_module([
    make_function("regular_worker", LayoutPhase.FirstFrame, 3)
])

val plan = solve_layout(module, nil)

expect(names_in_phase(plan, LayoutPhase.FirstFrame)).to_equal(["regular_worker"])
```

</details>

#### keeps default steady functions in the steady phase

- keeps default steady functions in the steady phase
   - Expected: names_in_phase(plan, LayoutPhase.Steady) equals `["compute"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps default steady functions in the steady phase")
val module = make_module([
    make_function("compute", nil, 4)
])

val plan = solve_layout(module, nil)

expect(names_in_phase(plan, LayoutPhase.Steady)).to_equal(["compute"])
```

</details>

#### orders hottest functions first within a phase

- orders hottest functions first within a phase
   - Expected: names_in_phase(plan, LayoutPhase.Steady) equals `["func_b", "func_c", "func_a"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders hottest functions first within a phase")
val profile = HotnessProfile(
    call_counts: {},
    execution_counts: {
        "func_a": 1000,
        "func_b": 5000,
        "func_c": 3000
    }
)

val module = make_module([
    make_function("func_a", LayoutPhase.Steady, 10),
    make_function("func_b", LayoutPhase.Steady, 11),
    make_function("func_c", LayoutPhase.Steady, 12)
])

val plan = solve_layout(module, profile)

expect(names_in_phase(plan, LayoutPhase.Steady)).to_equal(["func_b", "func_c", "func_a"])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native_layout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Native Layout.
- Native Layout

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3b78292f9b26eccf4d728cc21fbca6f1b097e10f1fef414701c04efdd282b857`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b78292f9b26eccf4d728cc21fbca6f1b097e10f1fef414701c04efdd282b857`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b78292f9b26eccf4d728cc21fbca6f1b097e10f1fef414701c04efdd282b857`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/native_layout_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/native_layout_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/native_layout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/native_layout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/native_layout_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers startup and cold phases from function names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/native_layout_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'respects explicit layout phase overrides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/native_layout_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps default steady functions in the steady phase' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
