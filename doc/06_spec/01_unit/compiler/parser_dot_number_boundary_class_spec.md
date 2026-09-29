# `.` / number token boundaries — similar-problem detection

> The nested-tuple-index bug

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `.` / number token boundaries — similar-problem detection

The nested-tuple-index bug

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language / Lexer |
| Status | Defect-class guard |
| Source | `test/01_unit/compiler/parser_dot_number_boundary_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The nested-tuple-index bug
(`doc/08_tracking/bug/seed_nested_tuple_index_float_munch_2026-08-06.md`) was one
instance of a class: **the seed lexer's number scanner deciding, with no
positional context, that a `.` adjacent to digits belongs to the number** — when
in this grammar a `.` next to digits can equally be member access (`r.0`), a
tuple-index chain (`r.0.1`), an exclusive range (`1..2`), an inclusive range
(`1..=2`), or an ellipsis (`1...`).

`scan_number` already special-cased `1..2` with a one-character lookahead. The
tuple-index case was missed because the ambiguity is *behind* the number, not
ahead of it, and nobody had enumerated the boundary systematically. Fixing one
direction while leaving the other is exactly how this recurs.

So this spec does not re-test the reported shape. It pins **every** adjacency of
`.` and digits at once, in both directions, so the next omission fails here
rather than shipping as a `found Float(x.y)` error on innocent source.

The audience is anyone editing `scan_number` or the `'.'` arm of `next_token`.

## Scope and Preconditions

Parse-time only: a failure of any group below prevents this FILE from loading, so
the runner reports it as a load error rather than a failed example. That is the
intended signal — the defect class is a parse defect. Requires a seed built at or
after 2026-08-17.

## Primary Workflow

Four groups, each an independent direction of the ambiguity: real float literals
must still be floats; ranges must still be ranges; member/index dots must never
be absorbed; and the two must be able to abut each other.

## Scenarios

### dot and number token boundaries

#### still lexes genuine float literals as floats

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- still lexes genuine float literals as floats
- A number with a fraction, in ordinary expression position
   - Expected: 1.5 + 1.5 equals `3.0`
- Leading zero, trailing digits, and an exponent form
   - Expected: 0.25 * 4.0 equals `1.0`
   - Expected: 2.5e2 equals `250.0`
- A float as a function argument and inside a collection
   - Expected: xs[1] equals `1.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still lexes genuine float literals as floats")
step("A number with a fraction, in ordinary expression position")
expect(1.5 + 1.5).to_equal(3.0)

step("Leading zero, trailing digits, and an exponent form")
expect(0.25 * 4.0).to_equal(1.0)
expect(2.5e2).to_equal(250.0)

step("A float as a function argument and inside a collection")
val xs = [0.5, 1.5]
expect(xs[1]).to_equal(1.5)
```

</details>

#### still lexes ranges rather than munching the dots into the number

- still lexes ranges rather than munching the dots into the number
- Exclusive range -- the case scan_number already guarded
   - Expected: seen equals `6`
- Inclusive range, where the third char after the digit is `=`
   - Expected: seen2 equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still lexes ranges rather than munching the dots into the number")
step("Exclusive range -- the case scan_number already guarded")
var seen = 0
for i in 1..4:
    seen = seen + i
expect(seen).to_equal(6)

step("Inclusive range, where the third char after the digit is `=`")
var seen2 = 0
for i in 1..=3:
    seen2 = seen2 + i
expect(seen2).to_equal(6)
```

</details>

#### never absorbs a member-access or tuple-index dot into the number

- never absorbs a member-access or tuple-index dot into the number
- One index -- the shallow case that always worked
   - Expected: pair.0 equals `11`
   - Expected: pair.1 equals `22`
- Two indices in a row -- Float(0.1) / Float(1.0) munch sites
   - Expected: nested.0.1 equals `22`
   - Expected: nested.1.0 equals `33`
- An index whose digits could read as an exponent (`.0e1` style)
   - Expected: wide.10 equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("never absorbs a member-access or tuple-index dot into the number")
step("One index -- the shallow case that always worked")
val pair = (11, 22)
expect(pair.0).to_equal(11)
expect(pair.1).to_equal(22)

step("Two indices in a row -- Float(0.1) / Float(1.0) munch sites")
val nested = ((11, 22), (33, 44))
expect(nested.0.1).to_equal(22)
expect(nested.1.0).to_equal(33)

step("An index whose digits could read as an exponent (`.0e1` style)")
val wide = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11)
expect(wide.10).to_equal(11)
```

</details>

#### handles an index chain abutting a float and a method call

- handles an index chain abutting a float and a method call
- A float VALUE reached through an index chain: both readings coexist
   - Expected: t.0.1 equals `2.5`
   - Expected: t.1.0 equals `3.5`
- An index followed by a method call -- postfix dot after an index dot
   - Expected: words.0.1.to_upper() equals `BETA`
- A float literal immediately followed by a method call


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles an index chain abutting a float and a method call")
step("A float VALUE reached through an index chain: both readings coexist")
val t = ((1.5, 2.5), (3.5, 4.5))
expect(t.0.1).to_equal(2.5)
expect(t.1.0).to_equal(3.5)

step("An index followed by a method call -- postfix dot after an index dot")
val words = (("alpha", "beta"), ("gamma", "delta"))
expect(words.0.1.to_upper()).to_equal("BETA")

step("A float literal immediately followed by a method call")
expect(str(2.5)).to_contain("2.5")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-PARSER-DOT-NUMBER-BOUNDARY-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `37c35f83d830a1e40472195189875942daaa4c0e5fbf113a53bbcad4b75e1a6e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `37c35f83d830a1e40472195189875942daaa4c0e5fbf113a53bbcad4b75e1a6e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `37c35f83d830a1e40472195189875942daaa4c0e5fbf113a53bbcad4b75e1a6e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/parser_dot_number_boundary_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser_dot_number_boundary_class_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/parser_dot_number_boundary_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser_dot_number_boundary_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser_dot_number_boundary_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/parser_dot_number_boundary_class_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/parser_dot_number_boundary_class_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still lexes genuine float literals as floats' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_dot_number_boundary_class_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still lexes ranges rather than munching the dots into the number' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_dot_number_boundary_class_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never absorbs a member-access or tuple-index dot into the number' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
