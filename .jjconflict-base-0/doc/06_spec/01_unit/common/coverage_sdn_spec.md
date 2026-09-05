# Coverage Sdn Specification

> Tests covering coverage_sdn parse, coverage_sdn merge — real set union, not concatenation, coverage_sdn render — round-trips and recomputes summary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coverage Sdn Specification

## Scenarios

### coverage_sdn parse

#### extracts line and function rows with real counts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts line and function rows with real counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts line and function rows with real counts")
val cov = parse_coverage_sdn(fixture1)
assert_equal(cov.lines.len(), 2)
assert_equal(cov.lines[0].file, "foo.spl")
assert_equal(cov.lines[0].line, 10)
assert_equal(cov.lines[0].hit_count, 3)
assert_equal(cov.functions.len(), 1)
assert_equal(cov.functions[0].name, "foo_fn")
assert_equal(cov.functions[0].call_count, 3)
```

</details>

#### returns zero rows for an artifact with only empty sections

- returns zero rows for an artifact with only empty sections


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns zero rows for an artifact with only empty sections")
val cov = parse_coverage_sdn("# Coverage Report\nversion: 1.0\n\nlines |file, line, hit_count|\n\nfunctions |name, call_count|\n\nsummary:\n    total_files: 0\n")
assert_equal(cov.lines.len(), 0)
assert_equal(cov.functions.len(), 0)
```

</details>

### coverage_sdn merge — real set union, not concatenation

#### sums hit counts for a shared (file, line) key and keeps disjoint keys separate

- sums hit counts for a shared (file, line) key and keeps disjoint keys separate


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sums hit counts for a shared (file, line) key and keeps disjoint keys separate")
val a = parse_coverage_sdn(fixture1)
val b = parse_coverage_sdn(fixture2)
val merged = merge_coverage(a, b)
# union has 3 distinct line rows: foo.spl:10 (shared, summed),
# foo.spl:12 (only in a), bar.spl:5 (only in b) — never 4 rows
# (that would mean it concatenated instead of keying by (file, line)).
assert_equal(merged.lines.len(), 3)
var foo10 = 0
var foo12 = 0
var bar5 = 0
for r in merged.lines:
    if r.file == "foo.spl" and r.line == 10:
        foo10 = r.hit_count
    elif r.file == "foo.spl" and r.line == 12:
        foo12 = r.hit_count
    elif r.file == "bar.spl" and r.line == 5:
        bar5 = r.hit_count
assert_equal(foo10, 5)
assert_equal(foo12, 1)
assert_equal(bar5, 4)
assert_equal(merged.functions.len(), 2)
```

</details>

#### sums true/false counts per decision key across runs

- sums true/false counts per decision key across runs


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sums true/false counts per decision key across runs")
val a = parse_coverage_sdn(decisions_fixture)
val b = parse_coverage_sdn(decisions_fixture2)
val merged = merge_coverage(a, b)
# decision 111 appears in both (summed), 222 only in a, 333 only in b
assert_equal(merged.decisions.len(), 3)
var d111_true = 0
var d111_false = 0
for r in merged.decisions:
    if r.id == "111":
        d111_true = r.true_count
        d111_false = r.false_count
assert_equal(d111_true, 2)
assert_equal(d111_false, 3)
```

</details>

#### merge_many unions an arbitrary list, and an empty list yields empty_coverage

- merge_many unions an arbitrary list, and an empty list yields empty_coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("merge_many unions an arbitrary list, and an empty list yields empty_coverage")
val a = parse_coverage_sdn(fixture1)
val b = parse_coverage_sdn(fixture2)
val merged = merge_many([a, b])
assert_equal(merged.lines.len(), 3)
val nothing = merge_many([])
assert_equal(nothing.lines.len(), 0)
assert_equal(nothing.functions.len(), 0)
```

</details>

### coverage_sdn render — round-trips and recomputes summary

#### renders a union whose summary reflects the merged rows, not a stale total

- renders a union whose summary reflects the merged rows, not a stale total


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a union whose summary reflects the merged rows, not a stale total")
val a = parse_coverage_sdn(fixture1)
val b = parse_coverage_sdn(fixture2)
val merged = merge_coverage(a, b)
val rendered = render_coverage_sdn(merged)
assert_true(rendered.contains("foo.spl, 10, 5"))
assert_true(rendered.contains("bar.spl, 5, 4"))
assert_true(rendered.contains("total_lines: 3"))
assert_true(rendered.contains("total_files: 2"))
# re-parsing the rendered text must reproduce the same row count —
# a real round-trip, not merely "some text got printed"
val reparsed = parse_coverage_sdn(rendered)
assert_equal(reparsed.lines.len(), 3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/coverage_sdn_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering coverage_sdn parse, coverage_sdn merge — real set union, not concatenation, coverage_sdn render — round-trips and recomputes summary.
- coverage_sdn parse
- coverage_sdn merge — real set union, not concatenation
- coverage_sdn render — round-trips and recomputes summary

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

- Canonical SPipe generation for source `f42de7757a6f40efceecefa0e100304a38f19522b8be3ebc38dbf4b4a63b86e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f42de7757a6f40efceecefa0e100304a38f19522b8be3ebc38dbf4b4a63b86e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f42de7757a6f40efceecefa0e100304a38f19522b8be3ebc38dbf4b4a63b86e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/common/coverage_sdn_spec.spl
mirror: doc/06_spec/01_unit/common/coverage_sdn_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/coverage_sdn_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/coverage_sdn_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/coverage_sdn_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts line and function rows with real counts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/coverage_sdn_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns zero rows for an artifact with only empty sections' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/coverage_sdn_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sums hit counts for a shared (file, line) key and keeps disjoint keys separate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
