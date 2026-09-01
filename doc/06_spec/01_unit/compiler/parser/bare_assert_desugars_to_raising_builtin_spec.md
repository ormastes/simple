# Bare `assert` desugars to a raising builtin

> `parse_statement` in the pure-Simple frontend used to parse `assert COND`,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bare `assert` desugars to a raising builtin

`parse_statement` in the pure-Simple frontend used to parse `assert COND`,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language |
| Status | Active |
| Source | `test/01_unit/compiler/parser/bare_assert_desugars_to_raising_builtin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`parse_statement` in the pure-Simple frontend used to parse `assert COND`,
bind (and drop) the optional message, and then return
`stmt_expr_stmt(assert_cond, 0)`. The condition was *evaluated and discarded* —
never checked — so every bare `assert` in the tree was a silent no-op under the
self-hosted compiler. 1411 `assert` statements under `src/` were affected.

The fix desugars the statement to `__assert(cond)` / `__assert(cond, msg)`,
a raising builtin implemented in
`src/compiler/10.frontend/core/interpreter/eval_builtins.spl` (interpreter,
via `eval_set_error`) and in
`src/compiler/10.frontend/core/compiler/cg_expr.spl` (C codegen, via the
`spl_assert` helper already emitted by `c_codegen.spl`).

## Scope and Preconditions

This spec drives the pure-Simple parser directly (`parser_init` +
`parse_statement`) and inspects the resulting AST node. It does not depend on
which binary hosts it: the code under test is Simple source, read live.

## Primary Workflow

Parse an assert statement; the statement's expression must be an `EXPR_CALL`
whose callee is the identifier `__assert`, carrying the condition as its first
argument and the message (when present) as its second.

## Recovery and Troubleshooting

A failure reporting tag 7 (`EXPR_BINARY`) is the original defect: the raw
condition is being returned and discarded.

## Compatibility and Limitations

Covers the pure-Simple frontend only. The Rust bootstrap seed has an
independent, already-correct `assert` statement parser
(`src/compiler_rust/parser/src/stmt_parsing/assert.rs`).

## Scenarios

### bare assert desugars to a raising builtin

#### routes a bare assert through __assert

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes a bare assert through __assert
- Parse `assert 1 == 2`
- The statement expression is a call, not the bare condition
   - Expected: expr_get_tag(e) equals `EXPR_CALL_TAG`
   - Expected: callee_of(e) equals `__assert`
- The condition is carried as the first argument
   - Expected: expr_get_args(e).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("routes a bare assert through __assert")
step("Parse `assert 1 == 2`")
val e = parse_one("assert 1 == 2\n")
step("The statement expression is a call, not the bare condition")
expect(expr_get_tag(e)).to_equal(EXPR_CALL_TAG)
expect(callee_of(e)).to_equal("__assert")
step("The condition is carried as the first argument")
expect(expr_get_args(e).len()).to_equal(1)
```

</details>

#### carries the optional message as a second argument

- carries the optional message as a second argument
- Parse `assert 1 == 2, "boom"`
   - Expected: callee_of(e) equals `__assert`
- Message is passed to the builtin instead of being dropped
   - Expected: expr_get_args(e).len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("carries the optional message as a second argument")
step("Parse `assert 1 == 2, \"boom\"`")
val e = parse_one("assert 1 == 2, \"boom\"\n")
expect(callee_of(e)).to_equal("__assert")
step("Message is passed to the builtin instead of being dropped")
expect(expr_get_args(e).len()).to_equal(2)
```

</details>

#### still desugars a true assert (the check is not condition-dependent)

- still desugars a true assert (the check is not condition-dependent)
- Parse `assert 1 == 1`
   - Expected: callee_of(e) equals `__assert`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still desugars a true assert (the check is not condition-dependent)")
step("Parse `assert 1 == 1`")
val e = parse_one("assert 1 == 1\n")
expect(callee_of(e)).to_equal("__assert")
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fcd3ec5705388c51ece7ea55d1c1a277b6ad1fd87a14d69b320c649362577f9f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fcd3ec5705388c51ece7ea55d1c1a277b6ad1fd87a14d69b320c649362577f9f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fcd3ec5705388c51ece7ea55d1c1a277b6ad1fd87a14d69b320c649362577f9f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/parser/bare_assert_desugars_to_raising_builtin_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/bare_assert_desugars_to_raising_builtin_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/bare_assert_desugars_to_raising_builtin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/compiler/parser/bare_assert_desugars_to_raising_builtin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/parser/bare_assert_desugars_to_raising_builtin_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes a bare assert through __assert' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/bare_assert_desugars_to_raising_builtin_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries the optional message as a second argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/bare_assert_desugars_to_raising_builtin_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still desugars a true assert (the check is not condition-dependent)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
