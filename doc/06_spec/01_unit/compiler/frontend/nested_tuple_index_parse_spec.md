# nested_tuple_index_parse_spec

> Purpose: Prove that Nested tuple-index access parses (r.0.1).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nested_tuple_index_parse_spec

Purpose: Prove that Nested tuple-index access parses (r.0.1).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/nested_tuple_index_parse_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Nested tuple-index access parses (r.0.1).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Nested tuple-index access parses (r.0.1)

#### r.0.1 parses as two chained tuple indices, not a float literal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- r.0.1 parses as two chained tuple indices, not a float literal
- Verify: r.0.1 parses as two chained tuple indices, not a float literal
   - Expected: shapes()["nested2"] equals `r.0.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("r.0.1 parses as two chained tuple indices, not a float literal")
step("Verify: r.0.1 parses as two chained tuple indices, not a float literal")
# @req: REQ-COMPILER-FRONTEND-001
expect(shapes()["nested2"]).to_equal("r.0.1")
```

</details>

#### r.0.10 keeps the exact index 10 (an f64 payload could not)

- r.0.10 keeps the exact index 10 (an f64 payload could not)
- Verify: r.0.10 keeps the exact index 10 (an f64 payload could not)
   - Expected: shapes()["wide_index"] equals `r.0.10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("r.0.10 keeps the exact index 10 (an f64 payload could not)")
step("Verify: r.0.10 keeps the exact index 10 (an f64 payload could not)")
expect(shapes()["wide_index"]).to_equal("r.0.10")
```

</details>

#### r.0.1.2 chains three levels

- r.0.1.2 chains three levels
- Verify: r.0.1.2 chains three levels
   - Expected: shapes()["nested3"] equals `r.0.1.2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("r.0.1.2 chains three levels")
step("Verify: r.0.1.2 chains three levels")
expect(shapes()["nested3"]).to_equal("r.0.1.2")
```

</details>

#### r.0.1.2.3 chains four levels

- r.0.1.2.3 chains four levels
- Verify: r.0.1.2.3 chains four levels
   - Expected: shapes()["nested4"] equals `r.0.1.2.3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("r.0.1.2.3 chains four levels")
step("Verify: r.0.1.2.3 chains four levels")
expect(shapes()["nested4"]).to_equal("r.0.1.2.3")
```

</details>

### Regression guard: float literals and single-level access unchanged

#### 1.0 is still a float literal

- 1.0 is still a float literal
- Verify: 1.0 is still a float literal
   - Expected: floats()["one_point_zero"] equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("1.0 is still a float literal")
step("Verify: 1.0 is still a float literal")
expect(floats()["one_point_zero"]).to_equal(1.0)
```

</details>

#### 3.14 is still a float literal

- 3.14 is still a float literal
- Verify: 3.14 is still a float literal
   - Expected: floats()["pi"] equals `3.14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("3.14 is still a float literal")
step("Verify: 3.14 is still a float literal")
expect(floats()["pi"]).to_equal(3.14)
```

</details>

#### 1e5 is still a float literal

- 1e5 is still a float literal
- Verify: 1e5 is still a float literal
   - Expected: floats()["exp5"] equals `100000.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("1e5 is still a float literal")
step("Verify: 1e5 is still a float literal")
expect(floats()["exp5"]).to_equal(100000.0)
```

</details>

#### 0.0 is still a float literal

- 0.0 is still a float literal
- Verify: 0.0 is still a float literal
   - Expected: floats()["zero"] equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("0.0 is still a float literal")
step("Verify: 0.0 is still a float literal")
expect(floats()["zero"]).to_equal(0.0)
```

</details>

#### single-level tuple index x.0 still parses

- single-level tuple index x.0 still parses
- Verify: single-level tuple index x.0 still parses
   - Expected: shapes()["single"] equals `x.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("single-level tuple index x.0 still parses")
step("Verify: single-level tuple index x.0 still parses")
expect(shapes()["single"]).to_equal("x.0")
```

</details>

#### mixed index-then-field r.0.name still parses

- mixed index-then-field r.0.name still parses
- Verify: mixed index-then-field r.0.name still parses
   - Expected: shapes()["index_then_field"] equals `r.0.name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("mixed index-then-field r.0.name still parses")
step("Verify: mixed index-then-field r.0.name still parses")
expect(shapes()["index_then_field"]).to_equal("r.0.name")
```

</details>

#### method call x.method() still parses

- method call x.method() still parses
- Verify: method call x.method() still parses
   - Expected: shapes()["method"] equals `x.method()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("method call x.method() still parses")
step("Verify: method call x.method() still parses")
expect(shapes()["method"]).to_equal("x.method()")
```

</details>

#### field access x.name still parses

- field access x.name still parses
- Verify: field access x.name still parses
   - Expected: shapes()["field"] equals `x.name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("field access x.name still parses")
step("Verify: field access x.name still parses")
expect(shapes()["field"]).to_equal("x.name")
```

</details>

#### range 0..10 is still a range, not a tuple index

- range 0..10 is still a range, not a tuple index
- Verify: range 0..10 is still a range, not a tuple index
   - Expected: shapes()["rng"] equals `range`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("range 0..10 is still a range, not a tuple index")
step("Verify: range 0..10 is still a range, not a tuple index")
expect(shapes()["rng"]).to_equal("range")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-FRONTEND-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `28e0dbcaeb697d60dd42069dadce36ed11ff79582763aa2f1a1d928c3d5f0c51`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `28e0dbcaeb697d60dd42069dadce36ed11ff79582763aa2f1a1d928c3d5f0c51`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `28e0dbcaeb697d60dd42069dadce36ed11ff79582763aa2f1a1d928c3d5f0c51`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/frontend/nested_tuple_index_parse_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/nested_tuple_index_parse_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/nested_tuple_index_parse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/nested_tuple_index_parse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/nested_tuple_index_parse_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/nested_tuple_index_parse_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'r.0.1 parses as two chained tuple indices, not a float literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/nested_tuple_index_parse_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'r.0.10 keeps the exact index 10 (an f64 payload could not)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/nested_tuple_index_parse_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'r.0.1.2 chains three levels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
