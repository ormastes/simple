# Defect Class: Any Comparison Followed by a Bracket Index

> The 2026-06-14 row `parser_array_index_misread_as_generics` was closed after

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Defect Class: Any Comparison Followed by a Bracket Index

The 2026-06-14 row `parser_array_index_misread_as_generics` was closed after

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/comparison_then_bracket_index_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The 2026-06-14 row `parser_array_index_misread_as_generics` was closed after
verifying its single reproducer, which is exactly why a second live instance in
`src/compiler/**` survived the closure. The trigger is not the indexing; it is a
comparison operator immediately to its left, which makes the parser speculate a
`<...>` generic-argument list.

This spec walks the CLASS rather than one site:

  - `a < b[i]`   — the regalloc.spl:158 shape
  - `a <= b[i]`  — the same speculation entered via `<=`
  - `x >= 0 and y < arr[j].field` — the `and`-chained form from the original
    style.spl:559 reproducer, where the index is also field-projected
  - `a < b[c[d]]` — a nested index inside the index

See doc/08_tracking/bug/parser_bracket_index_after_less_than_still_misread_as_generics_2026-08-17.md

## Scenarios

### Comparison followed by a bracket index (defect class)

#### handles `a < b[i]`

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- handles `a < b[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles `a < b[i]`")
val b = [10, 20, 30]
assert_true(5 < b[0])
assert_false(15 < b[0])
```

</details>

#### handles `a <= b[i]`

- handles `a <= b[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles `a <= b[i]`")
val b = [10, 20, 30]
assert_true(10 <= b[0])
assert_false(11 <= b[0])
```

</details>

#### handles the `and`-chained form with a field projection

- handles the `and`-chained form with a field projection


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles the `and`-chained form with a field projection")
# Mirrors: while j >= 0 and current.selector.specificity < matched[j].selector.specificity
val specificity = [100, 200, 300]
val j = 1
val current = 50
assert_true(j >= 0 and current < specificity[j])
assert_false(j >= 0 and 500 < specificity[j])
```

</details>

#### handles a nested index `a < b[c[d]]`

- handles a nested index `a < b[c[d]]`
   - Expected: b[c[d]] equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles a nested index `a < b[c[d]]`")
val b = [10, 20, 30]
val c = [2, 1, 0]
val d = 0
# c[0] is 2, so b[c[d]] is 30.
expect(b[c[d]]).to_equal(30)
assert_true(5 < b[c[d]])
assert_false(35 < b[c[d]])
```

</details>

#### still evaluates a method call on the indexed element

- still evaluates a method call on the indexed element


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still evaluates a method call on the indexed element")
val words = ["ab", "cdef"]
assert_true(1 < words[1].len())
```

</details>

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

- Canonical SPipe generation for source `c230dcd911426ce51a1e5732da48ffc3b3e767ba9db2bb5a275ada040afaa249`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c230dcd911426ce51a1e5732da48ffc3b3e767ba9db2bb5a275ada040afaa249`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c230dcd911426ce51a1e5732da48ffc3b3e767ba9db2bb5a275ada040afaa249`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/parser/comparison_then_bracket_index_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/comparison_then_bracket_index_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/comparison_then_bracket_index_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/comparison_then_bracket_index_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/comparison_then_bracket_index_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/parser/comparison_then_bracket_index_class_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles `a < b[i]`' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/comparison_then_bracket_index_class_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles `a <= b[i]`' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/comparison_then_bracket_index_class_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles the `and`-chained form with a field projection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
