# Traits Compiles Specification

> Tests covering Traits Compiles.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Traits Compiles Specification

## Scenarios

### Traits Compiles

#### should evaluate compiles query without leaking inner errors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should evaluate compiles query without leaking inner errors
   - Expected: src contains `if tr_query == "compiles"`
   - Expected: src contains `val old_had_error = eval_had_error`
   - Expected: src contains `val old_error_msg = eval_error_msg`
   - Expected: src contains `eval_had_error = false`
   - Expected: src contains `val compiled_ok = not eval_had_error`
   - Expected: src contains `return val_make_bool(compiled_ok)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should evaluate compiles query without leaking inner errors")
val src = traits_source()
expect(src.contains("if tr_query == \"compiles\"")).to_equal(true)
expect(src.contains("val old_had_error = eval_had_error")).to_equal(true)
expect(src.contains("val old_error_msg = eval_error_msg")).to_equal(true)
expect(src.contains("eval_had_error = false")).to_equal(true)
expect(src.contains("val compiled_ok = not eval_had_error")).to_equal(true)
expect(src.contains("return val_make_bool(compiled_ok)")).to_equal(true)
```

</details>

#### should return false when compiles has no expression argument

- should return false when compiles has no expression argument
   - Expected: src contains `if tr_query == "compiles"`
   - Expected: src contains `return val_make_bool(false)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should return false when compiles has no expression argument")
val src = traits_source()
expect(src.contains("if tr_query == \"compiles\"")).to_equal(true)
expect(src.contains("return val_make_bool(false)")).to_equal(true)
```

</details>

#### should expose get_annotations query through must_use registry

- should expose get_annotations query through must_use registry
   - Expected: src contains `if tr_query == "get_annotations"`
   - Expected: src contains `if must_use_is_registered(ann_sym)`
   - Expected: src contains `ann_list.push(val_make_text("must_use"))`
   - Expected: src contains `return val_make_array(ann_list)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should expose get_annotations query through must_use registry")
val src = traits_source()
expect(src.contains("if tr_query == \"get_annotations\"")).to_equal(true)
expect(src.contains("if must_use_is_registered(ann_sym)")).to_equal(true)
expect(src.contains("ann_list.push(val_make_text(\"must_use\"))")).to_equal(true)
expect(src.contains("return val_make_array(ann_list)")).to_equal(true)
```

</details>

#### should expose has_annotation query through must_use registry

- should expose has_annotation query through must_use registry
   - Expected: src contains `if tr_query == "has_annotation"`
   - Expected: src contains `if ha_ann == "must_use"`
   - Expected: src contains `return val_make_bool(must_use_is_registered(ha_sym))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should expose has_annotation query through must_use registry")
val src = traits_source()
expect(src.contains("if tr_query == \"has_annotation\"")).to_equal(true)
expect(src.contains("if ha_ann == \"must_use\"")).to_equal(true)
expect(src.contains("return val_make_bool(must_use_is_registered(ha_sym))")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/traits_compiles_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Traits Compiles.
- Traits Compiles

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

- `REQ-SSPEC-COMPILER_CORE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `af742686bf64341b9ee362f191b85a21fc53a8eff20faedb0e8c8d3f55bb719b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `af742686bf64341b9ee362f191b85a21fc53a8eff20faedb0e8c8d3f55bb719b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `af742686bf64341b9ee362f191b85a21fc53a8eff20faedb0e8c8d3f55bb719b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler_core/traits_compiles_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/traits_compiles_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/traits_compiles_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/traits_compiles_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/traits_compiles_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should evaluate compiles query without leaking inner errors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/traits_compiles_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should evaluate compiles query without leaking inner errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/traits_compiles_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return false when compiles has no expression argument' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/traits_compiles_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should return false when compiles has no expression argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/traits_compiles_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose get_annotations query through must_use registry' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/traits_compiles_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose get_annotations query through must_use registry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/traits_compiles_spec.spl:41:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose has_annotation query through must_use registry' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
