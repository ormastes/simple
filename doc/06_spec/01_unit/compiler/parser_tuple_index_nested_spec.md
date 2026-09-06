# Nested tuple indexing (`r.0.1`)

> A tuple of tuples is indexed the obvious way: `r.0` picks the first component,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nested tuple indexing (`r.0.1`)

A tuple of tuples is indexed the obvious way: `r.0` picks the first component,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language / Lexer |
| Status | Regression guard (reproducing spec) |
| Source | `test/01_unit/compiler/parser_tuple_index_nested_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A tuple of tuples is indexed the obvious way: `r.0` picks the first component,
and `r.0.1` picks the second component of that. Until 2026-08-17 the second form
did not parse at all in the Rust seed. `scan_number`
(`src/compiler_rust/parser/src/lexer/numbers.rs`) saw the digit `0`, then saw a
following `.` with a digit after it, and greedily absorbed the pair as a
fractional part — emitting a single `Float(0.1)` token where the source meant two
separate tuple indices. The postfix parser then reported:

    parse: Unexpected token: expected identifier, found Float(0.1)

An error naming a float literal for source text containing no float literal.

The audience is anyone touching numeric scanning in the seed lexer. The fix is a
positional test, `preceded_by_member_dot`: a number whose immediately preceding
character is a member-access `.` sits in an index position, and a float literal
can never appear there, because a lone `.` always lexes to `TokenKind::Dot` and
the language has no leading-dot float form.

## Scope and Preconditions

Requires a seed built at or after 2026-08-17; an older binary fails to LOAD this
file with the `found Float(0.1)` error above, which is exactly the reproduction.

## Primary Workflow

Build nested tuples and read components through two- and three-deep index chains,
asserting the component values arithmetic says they must be.

See doc/08_tracking/bug/seed_nested_tuple_index_float_munch_2026-08-06.md

## Scenarios

### nested tuple indexing

#### reads the second component of the first component

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads the second component of the first component
- Build the exact `((1, 2), (3, 4))` shape from the bug report
- A single index still works -- this was never broken
   - Expected: inner.1 equals `2`
- The chained form `r.0.1` is the one that used to emit Float(0.1)
   - Expected: r.0.1 equals `2`
- Every other two-deep combination must resolve independently
   - Expected: r.0.0 equals `1`
   - Expected: r.1.0 equals `3`
   - Expected: r.1.1 equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads the second component of the first component")
step("Build the exact `((1, 2), (3, 4))` shape from the bug report")
val r = ((1, 2), (3, 4))

step("A single index still works -- this was never broken")
val inner = r.0
expect(inner.1).to_equal(2)

step("The chained form `r.0.1` is the one that used to emit Float(0.1)")
expect(r.0.1).to_equal(2)

step("Every other two-deep combination must resolve independently")
expect(r.0.0).to_equal(1)
expect(r.1.0).to_equal(3)
expect(r.1.1).to_equal(4)
```

</details>

#### reads a three-deep index chain

- reads a three-deep index chain
- Nesting one level further exercises two consecutive munch sites
- `deep.0.1.0` would have munched `.1.0` into Float(1.0)
   - Expected: deep.0.1.0 equals `c`
   - Expected: deep.0.0.1 equals `b`
   - Expected: deep.1.1.1 equals `h`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads a three-deep index chain")
step("Nesting one level further exercises two consecutive munch sites")
val deep = ((("a", "b"), ("c", "d")), (("e", "f"), ("g", "h")))

step("`deep.0.1.0` would have munched `.1.0` into Float(1.0)")
expect(deep.0.1.0).to_equal("c")
expect(deep.0.0.1).to_equal("b")
expect(deep.1.1.1).to_equal("h")
```

</details>

#### indexes a tuple nested inside a tuple with mixed component types

- indexes a tuple nested inside a tuple with mixed component types
- The defect was purely lexical, so it fired regardless of element type
   - Expected: mixed.0.0 equals `10`
   - Expected: mixed.0.1 equals `ten`
   - Expected: mixed.1.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("indexes a tuple nested inside a tuple with mixed component types")
step("The defect was purely lexical, so it fired regardless of element type")
val mixed = ((10, "ten"), (2.5, true))
expect(mixed.0.0).to_equal(10)
expect(mixed.0.1).to_equal("ten")
expect(mixed.1.1).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-PARSER-TUPLE-INDEX-NESTED-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fd18fc423bb5a44055fe52b237567b60691d0f3e70cdae6abd28e5c3499f521c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd18fc423bb5a44055fe52b237567b60691d0f3e70cdae6abd28e5c3499f521c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd18fc423bb5a44055fe52b237567b60691d0f3e70cdae6abd28e5c3499f521c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/parser_tuple_index_nested_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser_tuple_index_nested_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/parser_tuple_index_nested_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser_tuple_index_nested_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser_tuple_index_nested_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/parser_tuple_index_nested_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/parser_tuple_index_nested_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the second component of the first component' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_tuple_index_nested_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a three-deep index chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_tuple_index_nested_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'indexes a tuple nested inside a tuple with mixed component types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
