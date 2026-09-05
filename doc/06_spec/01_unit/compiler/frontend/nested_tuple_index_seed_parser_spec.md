# nested_tuple_index_seed_parser_spec

> Feature: Nested Tuple Index Parsing

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nested_tuple_index_seed_parser_spec

Feature: Nested Tuple Index Parsing

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/nested_tuple_index_seed_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Feature: Nested Tuple Index Parsing
Category: Compiler Frontend
Status: Active

## Scenarios

### nested tuple indexing parses

#### reads a two-level index r.0.1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### reads the other two-level paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ((1, 2), (3, 4))
expect(r.0.0).to_equal(1)
expect(r.1.0).to_equal(3)
expect(r.1.1).to_equal(4)
```

</details>

#### reads a three-level index r.0.1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ((1, (7, 8)), (3, 4))
expect(r.0.1.0).to_equal(7)
expect(r.0.1.1).to_equal(8)
```

</details>

#### still reads a single-level index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = (10, 20)
expect(r.0).to_equal(10)
expect(r.1).to_equal(20)
```

</details>

#### allows a method call after a nested index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ((1, 2), (3, 4))
expect(r.0.1.to_string()).to_equal("2")
```

</details>

### nested tuple index fix does not break real floats

#### keeps a plain float literal a float

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0.1
expect(x > 0.09 and x < 0.11).to_equal(true)
```

</details>

#### keeps a float literal in an expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1.5 + 1.5).to_equal(3.0)
```

</details>

#### keeps exponent-form floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = 1e3
expect(e > 999.0 and e < 1001.0).to_equal(true)
```

</details>

#### keeps a float returned from a call

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((2.0).to_string().starts_with("2")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `b93be953f510d8ccfcad6886334617c4932483154ea969ff058c30f885d31064`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b93be953f510d8ccfcad6886334617c4932483154ea969ff058c30f885d31064`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b93be953f510d8ccfcad6886334617c4932483154ea969ff058c30f885d31064`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/compiler/frontend/nested_tuple_index_seed_parser_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/nested_tuple_index_seed_parser_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/nested_tuple_index_seed_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/nested_tuple_index_seed_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/nested_tuple_index_seed_parser_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/frontend/nested_tuple_index_seed_parser_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/nested_tuple_index_seed_parser_spec.spl:38:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reads a two-level index r.0.1' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/frontend/nested_tuple_index_seed_parser_spec.spl:44:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reads the other two-level paths' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/frontend/nested_tuple_index_seed_parser_spec.spl:50:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reads a three-level index r.0.1.0' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/frontend/nested_tuple_index_seed_parser_spec.spl:55:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'still reads a single-level index' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
