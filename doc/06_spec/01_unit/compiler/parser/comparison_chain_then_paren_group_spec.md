# Defect Class: Comparison Chain Closed by a Parenthesised Group

> `try_skip_ident_generic_args` speculates a generic-argument list whenever an

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Defect Class: Comparison Chain Closed by a Parenthesised Group

`try_skip_ident_generic_args` speculates a generic-argument list whenever an

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/comparison_chain_then_paren_group_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

`try_skip_ident_generic_args` speculates a generic-argument list whenever an
identifier is followed by `<`, and confirms it when a matching `>` is followed
by `(`, `.`, `::` or `{`. Its scan accepted an unbounded run of arguments with
NO separating commas, and `parse_type` accepts a bare keyword or identifier as
a named type. So

    if key_col < 0 or key_col > (max_col - min_col):

scanned as `key_col` `<` [`0`, `or`, `key_col`] `>` `(` — a "confirmed" generic
call — and hard-errored on the recorded const-generic span
("expected a type in generic argument position ... found integer literal")
instead of backtracking into the comparison chain. This is a HARD parse error,
not a warning: every module importing the file failed to load, which is what
took out `src/app/office/sheets/data_ops.spl` and, transitively, the whole
`src/app/cli/main.spl` graph and its `*_log_modes_spec.spl` suites.

A real generic-argument list is `T (, T)*`; the fix requires a comma between
consecutive arguments. This spec walks the CLASS, not the one site:

  - the `data_ops.spl:38` shape, `a < 0 or a > (b - c)`
  - the same shape closed by `.` (method call) and by a `::` path
  - `and`-chained and non-literal left operands
  - positive control: real generic calls must still parse

See doc/08_tracking/bug/parser_comparison_chain_misread_as_generic_args_2026-08-18.md

## Scenarios

### Comparison chain closed by a parenthesised group (defect class)

#### handles the `a < 0 or a > (b - c)` shape

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- handles the `a < 0 or a > (b - c)` shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles the `a < 0 or a > (b - c)` shape")
val a = 5
val b = 10
val c = 2
assert_false(a < 0 or a > (b - c))
assert_true(9 < 0 or 9 > (b - c))
```

</details>

#### handles the same shape with `and`

- handles the same shape with `and`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles the same shape with `and`")
val a = 5
val b = 10
val c = 2
assert_true(a > 0 and a < (b - c))
assert_false(a > 0 and a > (b - c))
```

</details>

#### handles a non-literal left operand

- handles a non-literal left operand


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles a non-literal left operand")
val lo = 1
val a = 5
val b = 10
assert_true(a > lo and a < (b))
```

</details>

#### handles a comparison chain closed by a method call

- handles a comparison chain closed by a method call


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles a comparison chain closed by a method call")
val a = 1
val words = ["ab", "cdef"]
assert_true(a < 0 or a < words[1].len())
```

</details>

#### handles a comparison chain closed by a `::` path

- handles a comparison chain closed by a `::` path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles a comparison chain closed by a `::` path")
val a = 5
assert_true(a < 0 or a < Limits::big())
```

</details>

#### positive control: a real generic call still parses

- positive control: a real generic call still parses
   - Expected: xs.len() equals `0`
   - Expected: d.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("positive control: a real generic call still parses")
val xs: [i64] = []
expect(xs.len()).to_equal(0)
val d: Dict<text, i64> = {}
expect(d.len()).to_equal(0)
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c858a9aabdc47a1bd7d1a2e4a5599642664e52f1a99dea9844da0b6521a10066`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c858a9aabdc47a1bd7d1a2e4a5599642664e52f1a99dea9844da0b6521a10066`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c858a9aabdc47a1bd7d1a2e4a5599642664e52f1a99dea9844da0b6521a10066`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/parser/comparison_chain_then_paren_group_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/comparison_chain_then_paren_group_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/comparison_chain_then_paren_group_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/comparison_chain_then_paren_group_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/comparison_chain_then_paren_group_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/parser/comparison_chain_then_paren_group_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles the `a < 0 or a > (b - c)` shape' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/comparison_chain_then_paren_group_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles the same shape with `and`' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/comparison_chain_then_paren_group_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles a non-literal left operand' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
