# Bidir Type Check Specification

> Tests covering Bidir Type Check.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bidir Type Check Specification

## Scenarios

### Bidir Type Check

#### keeps bidirectional inference modes available

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps bidirectional inference modes available
   - Expected: source does not contain `enum InferMode`
   - Expected: source does not contain `enum HirType`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("keeps bidirectional inference modes available")
val source = read_bidir_source("src/compiler/30.types/bidirectional_types.spl")

expect(source).to_contain("enum BidirInferMode")
expect(source).to_contain("Synthesize")
expect(source).to_contain("Check")
expect(source).to_contain("enum BidirHirType")
# The whole point of the rename: this island must no longer squat the
# canonical `InferMode` / `HirType` names owned by type_infer_types.spl
# and the canonical HIR. Re-introducing either declaration turns this red.
expect(source.contains("enum InferMode")).to_equal(false)
expect(source.contains("enum HirType")).to_equal(false)
```

</details>

#### keeps bidirectional expression inference entrypoints available

- keeps bidirectional expression inference entrypoints available


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("keeps bidirectional expression inference entrypoints available")
val source = read_bidir_source("src/compiler/30.types/bidirectional_inferencer.spl")

expect(source).to_contain("me infer_expr(expr: BidirHirExpr, mode: BidirInferMode) -> BidirHirType")
expect(source).to_contain("me check_expr(expr: BidirHirExpr, expected: BidirHirType) -> BidirHirType")
```

</details>

#### keeps canonical Check dependencies source-compatible

- keeps canonical Check dependencies source-compatible
   - Expected: inference does not contain `self.unify(inferred, expected).map(())`
   - Expected: trace does not contain `self.level.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("keeps canonical Check dependencies source-compatible")
val inference = read_bidir_source("src/compiler/30.types/type_infer/inference_expr.spl")
val trace = read_bidir_source("src/compiler/80.driver/trace_config.spl")

expect(inference.contains("self.unify(inferred, expected).map(())")).to_equal(false)
expect(inference).to_contain("case Ok(_): Ok(())")
expect(inference).to_contain("case Err(e): Err(e)")
expect(trace.contains("self.level.to_i32()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/bidir_type_check_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Bidir Type Check.
- Bidir Type Check

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER_CORE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cd89b2afd61aa1792717481aacb0a7dcca48bb0d5ff03b07ea71678e61e54b6f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cd89b2afd61aa1792717481aacb0a7dcca48bb0d5ff03b07ea71678e61e54b6f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cd89b2afd61aa1792717481aacb0a7dcca48bb0d5ff03b07ea71678e61e54b6f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler_core/bidir_type_check_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/bidir_type_check_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler_core/bidir_type_check_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/bidir_type_check_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/bidir_type_check_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler_core/bidir_type_check_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler_core/bidir_type_check_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps bidirectional inference modes available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/bidir_type_check_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps bidirectional expression inference entrypoints available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/bidir_type_check_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps canonical Check dependencies source-compatible' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
