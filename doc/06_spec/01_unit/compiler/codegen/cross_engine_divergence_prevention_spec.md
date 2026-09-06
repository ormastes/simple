# Cross Engine Divergence Prevention Specification

> Tests covering nil-valued conditions that are not statically Optional, mutation reached through an index.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cross Engine Divergence Prevention Specification

## Scenarios

### nil-valued conditions that are not statically Optional

#### executed the probe — guards against a vacuous green

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executed the probe — guards against a vacuous green
- An unreachable or mis-pathed probe would let every example below pass by absence


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("executed the probe — guards against a vacuous green")
step("An unreachable or mis-pathed probe would let every example below pass by absence")
val interp = run_probe_in_mode("interpreter")
expect(interp).to_contain("DIVERGENCE_PREVENTION PROBE:")
expect(interp).to_contain("condA_bare_nil_literal")
expect(interp).to_contain("mutB_dict_explicit_writeback")
```

</details>

#### branches falsy for every condition form under the JIT

- branches falsy for every condition form under the JIT
- The 50.mir:1886 guard only rewrites conditions whose local has an Optional HIR type; these forms all bypass it
- Bare literal — the one form the filed reproducer covers
- Negation must invert a falsy nil, not a truthy one
- Short-circuit operands funnel back through the same condition path
- A call result is nil at runtime but is not a local carrying an Optional annotation
- `while` shares lower_cond_expr with `if` — a truthy nil spins the loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("branches falsy for every condition form under the JIT")
step("The 50.mir:1886 guard only rewrites conditions whose local has an Optional HIR type; these forms all bypass it")
val jit = run_probe_in_mode("jit")

step("Bare literal — the one form the filed reproducer covers")
expect(jit).to_contain("PASS condA_bare_nil_literal")

step("Negation must invert a falsy nil, not a truthy one")
expect(jit).to_contain("PASS condA_not_nil")

step("Short-circuit operands funnel back through the same condition path")
expect(jit).to_contain("PASS condA_nil_and_true")
expect(jit).to_contain("PASS condA_true_and_nil")
expect(jit).to_contain("PASS condA_nil_or_false")

step("A call result is nil at runtime but is not a local carrying an Optional annotation")
expect(jit).to_contain("PASS condA_call_returning_nil")

step("`while` shares lower_cond_expr with `if` — a truthy nil spins the loop")
expect(jit).to_contain("PASS condA_while_nil")
```

</details>

#### branches falsy for every condition form under the interpreter

- branches falsy for every condition form under the interpreter
- The interpreter is correct for the bare literal and the operator forms
- NEW — not in any filed row: a call returning nil reads TRUTHY here too, so this class is not JIT-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("branches falsy for every condition form under the interpreter")
step("The interpreter is correct for the bare literal and the operator forms")
val interp = run_probe_in_mode("interpreter")
expect(interp).to_contain("PASS condA_bare_nil_literal")
expect(interp).to_contain("PASS condA_not_nil")
expect(interp).to_contain("PASS condA_nil_and_true")
expect(interp).to_contain("PASS condA_true_and_nil")
expect(interp).to_contain("PASS condA_nil_or_false")
expect(interp).to_contain("PASS condA_while_nil")

step("NEW — not in any filed row: a call returning nil reads TRUTHY here too, so this class is not JIT-only")
expect(interp).to_contain("PASS condA_call_returning_nil")
```

</details>

### mutation reached through an index

#### persists the write for every container/element combination under the interpreter

- persists the write for every container/element combination under the interpreter
- Nested arrays — already correct, pinned against regression by a fix elsewhere
- Dict with an array value — text key loses the write, int key does not
- Tuple field reached through an array index
- Struct fields — both persist today; they bound the defect from the passing side
- The documented write-back workaround must keep working — it is the only escape hatch for this class


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("persists the write for every container/element combination under the interpreter")
val interp = run_probe_in_mode("interpreter")

step("Nested arrays — already correct, pinned against regression by a fix elsewhere")
expect(interp).to_contain("PASS mutB_array_of_array")
expect(interp).to_contain("PASS mutB_array_of_array_of_array")

step("Dict with an array value — text key loses the write, int key does not")
expect(interp).to_contain("PASS mutB_dict_text_key_array_value")
expect(interp).to_contain("PASS mutB_dict_int_key_text_array_value")

step("Tuple field reached through an array index")
expect(interp).to_contain("PASS mutB_array_of_tuple_field")

step("Struct fields — both persist today; they bound the defect from the passing side")
expect(interp).to_contain("PASS mutB_array_of_struct_field")
expect(interp).to_contain("PASS mutB_dict_of_struct_field")

step("The documented write-back workaround must keep working — it is the only escape hatch for this class")
expect(interp).to_contain("PASS mutB_dict_explicit_writeback")
```

</details>

#### persists the write for every container/element combination under the JIT

- persists the write for every container/element combination under the JIT
- The JIT passes the whole matrix today — pinned so an interpreter fix cannot regress it


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("persists the write for every container/element combination under the JIT")
step("The JIT passes the whole matrix today — pinned so an interpreter fix cannot regress it")
val jit = run_probe_in_mode("jit")
expect(jit).to_contain("PASS mutB_array_of_array")
expect(jit).to_contain("PASS mutB_dict_text_key_array_value")
expect(jit).to_contain("PASS mutB_dict_int_key_text_array_value")
expect(jit).to_contain("PASS mutB_array_of_tuple_field")
expect(jit).to_contain("PASS mutB_array_of_struct_field")
expect(jit).to_contain("PASS mutB_dict_of_struct_field")
expect(jit).to_contain("PASS mutB_array_of_array_of_array")
expect(jit).to_contain("PASS mutB_dict_explicit_writeback")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/cross_engine_divergence_prevention_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nil-valued conditions that are not statically Optional, mutation reached through an index.
- nil-valued conditions that are not statically Optional
- mutation reached through an index

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `a2efc344da15e89b4b8e09f4b0b65cccc24429a8604854deda3be831d6dcbd15`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a2efc344da15e89b4b8e09f4b0b65cccc24429a8604854deda3be831d6dcbd15`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a2efc344da15e89b4b8e09f4b0b65cccc24429a8604854deda3be831d6dcbd15`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/cross_engine_divergence_prevention_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/cross_engine_divergence_prevention_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/cross_engine_divergence_prevention_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/cross_engine_divergence_prevention_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/cross_engine_divergence_prevention_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executed the probe — guards against a vacuous green' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/cross_engine_divergence_prevention_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'branches falsy for every condition form under the JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/cross_engine_divergence_prevention_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'branches falsy for every condition form under the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
