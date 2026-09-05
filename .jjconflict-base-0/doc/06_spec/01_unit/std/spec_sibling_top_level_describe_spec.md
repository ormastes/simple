# Sibling Top-Level `describe` Groups Must All Run

> As a spec author, when I write several `describe` blocks side by side at the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sibling Top-Level `describe` Groups Must All Run

As a spec author, when I write several `describe` blocks side by side at the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/spec_sibling_top_level_describe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As a spec author, when I write several `describe` blocks side by side at the
top level of one file, I need EVERY group's examples to execute. The reported
bug (doc/08_tracking/bug/spec_runner_drops_sibling_top_level_describe_2026-06-28.md)
was that only the LAST sibling group ran while the file was still reported
green -- a hollow-green, silent-wrong-result defect.

Oracle: this file declares exactly 6 examples across 3 sibling top-level
groups. The runner's `Results:` line must report 6 total. A dropped group
shows up as a smaller total, which is the whole point: the count is the
oracle, not the pass/fail of any single example.

## Scenarios

### sibling group A (first)

#### runs example A1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs example A1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs example A1")
assert_equal(1 + 1, 2)
```

</details>

#### runs example A2

- runs example A2


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs example A2")
assert_true("alpha".contains("alp"))
```

</details>

### sibling group B (middle)

#### runs example B1

- runs example B1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs example B1")
assert_equal(2 + 2, 4)
```

</details>

#### runs example B2

- runs example B2


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs example B2")
assert_true("bravo".contains("rav"))
```

</details>

### sibling group C (last)

#### runs example C1

- runs example C1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs example C1")
assert_equal(3 + 3, 6)
```

</details>

#### runs example C2

- runs example C2


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs example C2")
assert_true("charlie".contains("harl"))
```

</details>

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5aed4015602c80780835102d41aa99fe9075e772423d25dc87bf984720979041`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5aed4015602c80780835102d41aa99fe9075e772423d25dc87bf984720979041`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5aed4015602c80780835102d41aa99fe9075e772423d25dc87bf984720979041`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/std/spec_sibling_top_level_describe_spec.spl
mirror: doc/06_spec/01_unit/std/spec_sibling_top_level_describe_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/spec_sibling_top_level_describe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/spec_sibling_top_level_describe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/spec_sibling_top_level_describe_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs example A1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/spec_sibling_top_level_describe_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs example A2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/spec_sibling_top_level_describe_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs example B1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
