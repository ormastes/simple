# Verified Profile V1 Projection Specification

> Tests covering the `verified` rung projects conservatively onto every V1 site.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Verified Profile V1 Projection Specification

## Scenarios

### the `verified` rung projects conservatively onto every V1 site

#### is the top rung of the canonical ladder

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is the top rung of the canonical ladder
- if this moves, the expectations below are about the wrong name
   - Expected: ladder[ladder.len() - 1] equals `verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is the top rung of the canonical ladder")
step("if this moves, the expectations below are about the wrong name")
val ladder = canonical_profile_names()
expect(ladder[ladder.len() - 1]).to_equal("verified")
```

</details>

#### the schema projects it onto the strongest V1 strictness

- the schema projects it onto the strongest V1 strictness


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the schema projects it onto the strongest V1 strictness")
expect(AssuranceStrictness.from_name("verified"))
    .to_equal(AssuranceStrictness.from_name("critical"))
```

</details>

#### the driver severity projection agrees with the schema, not the default

- the driver severity projection agrees with the schema, not the default


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the driver severity projection agrees with the schema, not the default")
expect(safety_pass_severity_for_name("verified"))
    .to_equal(safety_pass_severity_for_name("critical"))
expect(safety_pass_severity_for_name("verified"))
    .to_equal(SafetyPassSeverity.Deny)
```

</details>

#### the lint projection accepts it and agrees with the schema

- the lint projection accepts it and agrees with the schema
- returning nil here made lint reject the strictest profile
   - Expected: parse_lint_profile("verified") equals `parse_lint_profile("critical")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the lint projection accepts it and agrees with the schema")
step("returning nil here made lint reject the strictest profile")
expect(parse_lint_profile("verified")).to_be_truthy()
expect(parse_lint_profile("verified")).to_equal(parse_lint_profile("critical"))
```

</details>

#### driver severity never DECREASES as the canonical ladder ascends

- driver severity never DECREASES as the canonical ladder ascends
- the fallthrough bug made the top rung weaker than 'robust'


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("driver severity never DECREASES as the canonical ladder ascends")
step("the fallthrough bug made the top rung weaker than 'robust'")
var prev = -1
for name in canonical_profile_names():
    val rank = severity_rank(safety_pass_severity_for_name(name))
    expect(rank).to_be_greater_than_or_equal(prev)
    prev = rank
```

</details>

#### no rung of the ladder is rejected by lint

- no rung of the ladder is rejected by lint
- every canonical name must resolve at every V1 site


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("no rung of the ladder is rejected by lint")
step("every canonical name must resolve at every V1 site")
for name in canonical_profile_names():
    expect(parse_lint_profile(name)).to_be_truthy()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/assurance/verified_profile_v1_projection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering the `verified` rung projects conservatively onto every V1 site.
- the `verified` rung projects conservatively onto every V1 site

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `e736fb39ffc99a533612e9c3306e91d55b651fe32a00b3864a4cf9cca79bdb2c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e736fb39ffc99a533612e9c3306e91d55b651fe32a00b3864a4cf9cca79bdb2c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e736fb39ffc99a533612e9c3306e91d55b651fe32a00b3864a4cf9cca79bdb2c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/assurance/verified_profile_v1_projection_spec.spl
mirror: doc/06_spec/01_unit/compiler/assurance/verified_profile_v1_projection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/assurance/verified_profile_v1_projection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/assurance/verified_profile_v1_projection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/assurance/verified_profile_v1_projection_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is the top rung of the canonical ladder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/verified_profile_v1_projection_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the schema projects it onto the strongest V1 strictness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/verified_profile_v1_projection_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the driver severity projection agrees with the schema, not the default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
