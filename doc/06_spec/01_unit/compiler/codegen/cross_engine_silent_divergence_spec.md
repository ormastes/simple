# Cross Engine Silent Divergence Specification

> Tests covering cross-engine silent divergence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cross Engine Silent Divergence Specification

## Scenarios

### cross-engine silent divergence

#### runs the probe at all — guards against a vacuous green

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs the probe at all — guards against a vacuous green
- A probe that never executed would let every other example pass by absence
- Control arm: array-of-array indexing already yields a mutable reference on both engines


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("runs the probe at all — guards against a vacuous green")
step("A probe that never executed would let every other example pass by absence")
val interp = run_probe_in_mode("interpreter")
expect(interp).to_contain("mutate_through_nested_array")
expect(interp).to_contain("CROSS_ENGINE_DIVERGENCE PROBE:")

step("Control arm: array-of-array indexing already yields a mutable reference on both engines")
expect(interp).to_contain("PASS mutate_through_nested_array")
val jit = run_probe_in_mode("jit")
expect(jit).to_contain("PASS mutate_through_nested_array")
```

</details>

#### treats a nil condition as FALSY under the JIT (jit_if_nil_takes_true_branch)

- treats a nil condition as FALSY under the JIT (jit_if_nil_takes_true_branch)
- RT_NIL is the non-zero word 3, so branching on the raw value is unconditionally true
- A bare `if nil:` must take the false branch
- nil passed into a `bool` parameter must also read as false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("treats a nil condition as FALSY under the JIT (jit_if_nil_takes_true_branch)")
step("RT_NIL is the non-zero word 3, so branching on the raw value is unconditionally true")
val jit = run_probe_in_mode("jit")

step("A bare `if nil:` must take the false branch")
expect(jit).to_contain("PASS cond_nil_literal_bare")

step("nil passed into a `bool` parameter must also read as false")
expect(jit).to_contain("PASS cond_nil_through_bool_param")
```

</details>

#### treats a nil condition as FALSY under the interpreter (control arm — already correct)

- treats a nil condition as FALSY under the interpreter (control arm — already correct)
- The interpreter was correct in this row; a red here means the probe regressed, not the engine


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("treats a nil condition as FALSY under the interpreter (control arm — already correct)")
step("The interpreter was correct in this row; a red here means the probe regressed, not the engine")
val interp = run_probe_in_mode("interpreter")
expect(interp).to_contain("PASS cond_nil_literal_bare")
expect(interp).to_contain("PASS cond_nil_through_bool_param")
```

</details>

#### selects the variant arm when matching an Option<enum> under the INTERPRETER

- selects the variant arm when matching an Option<enum> under the INTERPRETER
- RE-ATTRIBUTION: the interpreter takes the wildcard here; the JIT is correct. This is NOT a 50.mir defect.


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("selects the variant arm when matching an Option<enum> under the INTERPRETER")
step("RE-ATTRIBUTION: the interpreter takes the wildcard here; the JIT is correct. This is NOT a 50.mir defect.")
val interp = run_probe_in_mode("interpreter")
expect(interp).to_contain("PASS match_option_enum_variant")
```

</details>

#### selects the variant arm when matching an Option<enum> under the JIT (control arm)

- selects the variant arm when matching an Option<enum> under the JIT (control arm)
- The JIT already reaches Ev.Action — pinned so a fix to the interpreter cannot regress it


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("selects the variant arm when matching an Option<enum> under the JIT (control arm)")
step("The JIT already reaches Ev.Action — pinned so a fix to the interpreter cannot regress it")
val jit = run_probe_in_mode("jit")
expect(jit).to_contain("PASS match_option_enum_variant")
```

</details>

#### persists a mutation reached through an index under the INTERPRETER

- persists a mutation reached through an index under the INTERPRETER
- RE-ATTRIBUTION: `c[k].push(x)` and `a[0].1.push(x)` lose the write on the interpreter; the JIT keeps it
- Dict value: c["k"].push(2) must leave len 2, not 1
- Tuple field: a[0].1.push(2) must leave len 2, not 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("persists a mutation reached through an index under the INTERPRETER")
step("RE-ATTRIBUTION: `c[k].push(x)` and `a[0].1.push(x)` lose the write on the interpreter; the JIT keeps it")
val interp = run_probe_in_mode("interpreter")

step("Dict value: c[\"k\"].push(2) must leave len 2, not 1")
expect(interp).to_contain("PASS mutate_through_dict_value")

step("Tuple field: a[0].1.push(2) must leave len 2, not 1")
expect(interp).to_contain("PASS mutate_through_tuple_field")
```

</details>

#### persists a mutation reached through an index under the JIT (control arm)

- persists a mutation reached through an index under the JIT (control arm)
- The JIT already persists both shapes — pinned so an interpreter fix cannot regress it


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("persists a mutation reached through an index under the JIT (control arm)")
step("The JIT already persists both shapes — pinned so an interpreter fix cannot regress it")
val jit = run_probe_in_mode("jit")
expect(jit).to_contain("PASS mutate_through_dict_value")
expect(jit).to_contain("PASS mutate_through_tuple_field")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/cross_engine_silent_divergence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering cross-engine silent divergence.
- cross-engine silent divergence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `5da83eca63da7e9c471d53f4e367441491e31a00b550fa9ba1522c8c1f1305ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5da83eca63da7e9c471d53f4e367441491e31a00b550fa9ba1522c8c1f1305ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5da83eca63da7e9c471d53f4e367441491e31a00b550fa9ba1522c8c1f1305ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/cross_engine_silent_divergence_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/cross_engine_silent_divergence_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/cross_engine_silent_divergence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/cross_engine_silent_divergence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/cross_engine_silent_divergence_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs the probe at all — guards against a vacuous green' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/cross_engine_silent_divergence_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats a nil condition as FALSY under the JIT (jit_if_nil_takes_true_branch)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/cross_engine_silent_divergence_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats a nil condition as FALSY under the interpreter (control arm — already correct)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
