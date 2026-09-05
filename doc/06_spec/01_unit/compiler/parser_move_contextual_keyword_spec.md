# `move` as an ordinary identifier

> `move` is a contextual keyword in Simple: it introduces a move-closure

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `move` as an ordinary identifier

`move` is a contextual keyword in Simple: it introduces a move-closure

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language / Parser |
| Status | Regression guard |
| Source | `test/01_unit/compiler/parser_move_contextual_keyword_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`move` is a contextual keyword in Simple: it introduces a move-closure
(`move \\x: ...`) and a unary move (`move value`), but it is also a perfectly
reasonable variable name — a compaction cursor, a queue shift counter, a chess
ply. Until 2026-08-17 the parser accepted the *declaration* `var move = 3` and
then rejected the very next *use*: `while move + 1u32 < n` failed with
`expected expression, found Plus`, because `move` unconditionally consumed the
following token as its operand.

That is the same defect class as `pub` / `examples` / `and_then`: a reserved
token rejected at the USE site, with the error pointing at the innocent operator
rather than at the name. It silently broke every spec that transitively imported
`common.ui.draw_ir`.

The audience is anyone touching the unary/primary expression dispatch in the
Rust seed parser.

## Scope and Preconditions

This spec exercises `move` in the identifier positions a user would write it in:
declaration, arithmetic, comparison, assignment, indexing, field access, and as
a function argument. It requires a seed built at or after 2026-08-17; an older
binary reports `parse: Unexpected token: expected expression, found Plus`.

It deliberately does NOT assert that move-closures stopped working — that is the
counterpart scenario at the end, which proves the keyword meaning survives.

## Primary Workflow

Declare a variable named `move`, then read it in every ordinary expression
position and confirm the values are the ones arithmetic says they should be.

See doc/08_tracking/bug/move_identifier_rejected_as_expression_2026-08-15.md

## Scenarios

### move as an ordinary identifier

#### reads a variable named move in arithmetic

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads a variable named move in arithmetic
- Declare a compaction cursor named `move`, exactly as the draw_ir store did
- Read it on the left of a binary operator -- the position that used to fail
- Read it on the right of a binary operator too


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads a variable named move in arithmetic")
step("Declare a compaction cursor named `move`, exactly as the draw_ir store did")
var move = 3u32

step("Read it on the left of a binary operator -- the position that used to fail")
expect(move + 1u32 == 4u32).to_be(true)

step("Read it on the right of a binary operator too")
expect(2u32 + move == 5u32).to_be(true)
```

</details>

<details>
<summary>Advanced: compares a variable named move in a loop condition</summary>

#### compares a variable named move in a loop condition

- compares a variable named move in a loop condition
- Run the exact `while move + 1 < limit` shape from the original bug
- The loop ran to completion instead of failing to parse
   - Expected: visited equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compares a variable named move in a loop condition")
step("Run the exact `while move + 1 < limit` shape from the original bug")
var move = 0u32
var visited = 0
while move + 1u32 < 4u32:
    visited = visited + 1
    move = move + 1u32

step("The loop ran to completion instead of failing to parse")
expect(visited).to_equal(3)
expect(move == 3u32).to_be(true)
```

</details>


</details>

#### assigns through, indexes with, and passes a variable named move

- assigns through, indexes with, and passes a variable named move
- Reassign it
   - Expected: move equals `10`
- Use it as an array index
   - Expected: queue[idx] equals `9`
- Pass it as a function argument
   - Expected: str(move) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("assigns through, indexes with, and passes a variable named move")
step("Reassign it")
var move = 1
move = move * 10
expect(move).to_equal(10)

step("Use it as an array index")
val queue = [7, 8, 9]
var idx = 2
expect(queue[idx]).to_equal(9)

step("Pass it as a function argument")
expect(str(move)).to_equal("10")
```

</details>

#### still treats `move \\x: ...` as a move-closure

- still treats `move \\x: ...` as a move-closure
- The contextual rule must not disable the keyword meaning
   - Expected: f(41) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still treats `move \\x: ...` as a move-closure")
step("The contextual rule must not disable the keyword meaning")
val f = move \x: x + 1
expect(f(41)).to_equal(42)
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
- `REQ-PARSER-CONTEXTUAL-MOVE-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cd13163b99075c753c2264d708f039e4b575c487a728831dccf9d49b7d9c2646`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cd13163b99075c753c2264d708f039e4b575c487a728831dccf9d49b7d9c2646`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cd13163b99075c753c2264d708f039e4b575c487a728831dccf9d49b7d9c2646`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/parser_move_contextual_keyword_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser_move_contextual_keyword_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/parser_move_contextual_keyword_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser_move_contextual_keyword_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser_move_contextual_keyword_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/parser_move_contextual_keyword_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/parser_move_contextual_keyword_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a variable named move in arithmetic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_move_contextual_keyword_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares a variable named move in a loop condition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_move_contextual_keyword_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns through, indexes with, and passes a variable named move' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
