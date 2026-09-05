# Class detection: no checking statement parses to a discarded expression

> The `assert` defect was not a typo — it was a *shape*: a statement whose whole

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Class detection: no checking statement parses to a discarded expression

The `assert` defect was not a typo — it was a *shape*: a statement whose whole

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language |
| Status | Active |
| Source | `test/01_unit/compiler/parser/no_statement_form_discards_its_condition_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The `assert` defect was not a typo — it was a *shape*: a statement whose whole
purpose is to CHECK something parsed into `stmt_expr_stmt(<the thing>, 0)`,
which evaluates the value and throws it away. Nothing in the parser distinguishes
that from a legitimate expression statement, so the bug was invisible.

This spec generalises past the one reproducer: it sweeps every surface form of
`assert` the language accepts and requires each to land on a *call* node — the
only AST shape that can raise. A future statement form that "checks" something
by returning its bare operand fails here without anyone writing a new test.

## Scope and Preconditions

Drives the pure-Simple parser (`parser_init` + `parse_statement`) directly.
Each case is parsed in isolation; no interpreter state is required.

## Primary Workflow

For each assert form: parse it, and require the resulting statement expression
to be `EXPR_CALL` (tag 9) targeting `__assert`. Any form landing on a binary,
unary, literal, identifier, or call-to-something-else node is a discarded
condition and fails, naming the form.

## Recovery and Troubleshooting

A failure names the exact source form and the tag it produced. Tag 7 is
`EXPR_BINARY`, the original `assert a == b` defect; tag 8 is unary
(`assert not x`); a call to a non-`__assert` callee means `assert f()` returned
`f()` itself rather than wrapping it.

## Compatibility and Limitations

Static, parse-level detection. It proves the condition reaches a raising
builtin; it does not execute the builtin.

## Scenarios

### no checking statement parses to a discarded expression

#### every assert surface form reaches the raising builtin

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- every assert surface form reaches the raising builtin
- Sweep every accepted assert form through the parser
- No form may evaluate its condition and throw it away
   - Expected: offenders.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("every assert surface form reaches the raising builtin")
step("Sweep every accepted assert form through the parser")
var offenders: [text] = []
for form in assert_forms():
    val shape = describe_shape(form)
    if shape != "__assert":
        offenders.push(form.trim() + " => " + shape)
step("No form may evaluate its condition and throw it away")
expect(offenders.len()).to_equal(0)
```

</details>

#### the sweep is non-vacuous

- the sweep is non-vacuous
- The form list must actually contain cases
   - Expected: assert_forms().len() equals `8`
- And the shape probe must be able to report a discard
   - Expected: describe_shape("1 == 2\n") equals `DISCARDED(tag=7)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the sweep is non-vacuous")
step("The form list must actually contain cases")
expect(assert_forms().len()).to_equal(8)
step("And the shape probe must be able to report a discard")
expect(describe_shape("1 == 2\n")).to_equal("DISCARDED(tag=7)")
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `180038d1b184b99f718cef33d4627dc236b31a8f626ca1d7949c56f2304780c8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `180038d1b184b99f718cef33d4627dc236b31a8f626ca1d7949c56f2304780c8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `180038d1b184b99f718cef33d4627dc236b31a8f626ca1d7949c56f2304780c8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser/no_statement_form_discards_its_condition_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/no_statement_form_discards_its_condition_class_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/no_statement_form_discards_its_condition_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/compiler/parser/no_statement_form_discards_its_condition_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/parser/no_statement_form_discards_its_condition_class_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'every assert surface form reaches the raising builtin' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/no_statement_form_discards_its_condition_class_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the sweep is non-vacuous' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
