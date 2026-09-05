# ast_types_spec

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ast_types_spec

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/frontend/ast_types_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Key Concepts

| Concept | Description |
|---------|-------------|
| make_core_expr | Expression node: (tag, span_id) |
| make_core_stmt | Statement node: (tag, span_id) |
| make_core_decl | Declaration node: (tag, span_id) |
| make_core_arm | Match arm: (pattern, guard, body stmts) |

## Scenarios

### frontend core ast types

#### constructs core nodes carrying their tag and span id

- build one node of each core kind
   - Expected: make_core_expr(3, 7).tag equals `3`
   - Expected: make_core_stmt(11, 21).span_id equals `21`
   - Expected: make_core_decl(5, 9).tag equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("build one node of each core kind")
# tags 3/5 and span ids 7/9/21 are arbitrary distinct probe values;
# the oracle is that the constructor returns the SAME values it was given
expect(make_core_expr(3, 7).tag).to_equal(3)
expect(make_core_stmt(11, 21).span_id).to_equal(21)
expect(make_core_decl(5, 9).tag).to_equal(5)
```

</details>

#### constructs match arms binding pattern, guard and body

- build a core match arm
   - Expected: arm.pattern equals `1`
   - Expected: arm.guard equals `2`
   - Expected: arm.body.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("build a core match arm")
# pattern id 1, guard id 2, body of two statement ids — each field must round-trip
val arm = make_core_arm(1, 2, [3, 4])
expect(arm.pattern).to_equal(1)
expect(arm.guard).to_equal(2)
expect(arm.body.len()).to_equal(2)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e88b72017eead6ae3ae9c931f89d82da43458a5d3f47bb829e9a7be9309f04ed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e88b72017eead6ae3ae9c931f89d82da43458a5d3f47bb829e9a7be9309f04ed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e88b72017eead6ae3ae9c931f89d82da43458a5d3f47bb829e9a7be9309f04ed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/frontend/ast_types_spec.spl
mirror: doc/06_spec/unit/compiler/frontend/ast_types_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/frontend/ast_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/frontend/ast_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/frontend/ast_types_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/compiler/frontend/ast_types_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/frontend/ast_types_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs core nodes carrying their tag and span id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/frontend/ast_types_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs match arms binding pattern, guard and body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
