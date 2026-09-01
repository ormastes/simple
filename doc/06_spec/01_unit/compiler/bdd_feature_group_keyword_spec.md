# Bdd Feature Group Keyword Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bdd Feature Group Keyword Specification

## Scenarios

#### runs examples declared directly inside a feature block

- runs examples declared directly inside a feature block


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs examples declared directly inside a feature block")
expect double(21) to_equal 42
```

</details>

#### registers each block separately, not as one synthetic error

- registers each block separately, not as one synthetic error


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers each block separately, not as one synthetic error")
expect double(0) to_equal 0
```

</details>

#### runs examples nested one level down

- runs examples nested one level down


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs examples nested one level down")
expect double(5) to_equal 10
```

</details>

#### keeps ordinary assertions working at depth

- keeps ordinary assertions working at depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps ordinary assertions working at depth")
val xs = [1, 2, 3]
expect xs.len() to_equal 3
```

</details>

#### context still nests inside a feature

#### mixes Gherkin and RSpec grouping keywords in one tree

- mixes Gherkin and RSpec grouping keywords in one tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mixes Gherkin and RSpec grouping keywords in one tree")
expect double(3) to_equal 6
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bdd_feature_group_keyword_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `33ce34912337d4d632fb4bbcb2d31a29db4f2d9dc5895062ce47defbedd4d05d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `33ce34912337d4d632fb4bbcb2d31a29db4f2d9dc5895062ce47defbedd4d05d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `33ce34912337d4d632fb4bbcb2d31a29db4f2d9dc5895062ce47defbedd4d05d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/compiler/bdd_feature_group_keyword_spec.spl
mirror: doc/06_spec/01_unit/compiler/bdd_feature_group_keyword_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bdd_feature_group_keyword_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bdd_feature_group_keyword_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bdd_feature_group_keyword_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/bdd_feature_group_keyword_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs examples declared directly inside a feature block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bdd_feature_group_keyword_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers each block separately, not as one synthetic error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bdd_feature_group_keyword_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs examples nested one level down' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
