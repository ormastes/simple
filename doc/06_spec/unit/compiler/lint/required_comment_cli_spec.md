# Required Comment CLI Lint Coverage

> WP-7 (aerospace hardening plan): `bin/simple lint`'s real output path

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Required Comment CLI Lint Coverage

WP-7 (aerospace hardening plan): `bin/simple lint`'s real output path

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/lint/required_comment_cli_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

WP-7 (aerospace hardening plan): `bin/simple lint`'s real output path
(`lint_cli_source`) is wired to the AST-based semantic checker
(`compiler.semantics.lint.required_comment.check_required_comment`), not the
former per-line text scanner. `Linter.lint_source` alone (no AST decls) can
no longer emit REQC001-004 — the loop lives in `lint_cli_source`
(entry_and_fixes.spl), same as STUB001/STUB002. See
doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md WP-7.

## Scenarios

### required comment lint CLI path

#### emits REQC001 through lint_cli_source for a bare pass_todo

- emits REQC001 through lint_cli_source for a bare pass_todo


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits REQC001 through lint_cli_source for a bare pass_todo")
var linter = Linter.new()
val results = lint_cli_source(linter, "sample.spl", "fn f():\n    pass_todo\n")
assert_true(has_code(results, "REQC001"))
```

</details>

#### emits REQC001 (not REQC003) through lint_cli_source for a weak bare todo(...)

- emits REQC001 (not REQC003) through lint_cli_source for a weak bare todo(...)


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits REQC001 (not REQC003) through lint_cli_source for a weak bare todo(...)")
# Real-parser finding, filed as
# doc/08_tracking/bug/todo_call_collapses_to_pass_todo_node_reqc003_unreachable_2026-08-07.md:
# the parser (parser_stmts.spl / primary_expr.spl, `ident_text ==
# "todo"`) desugars `todo(...)` into the SAME `expr_pass_todo` AST
# node as bare `pass_todo(...)` — there is no `expr_call` with callee
# "todo" for real parsed source. `check_required_comment`'s dedicated
# REQC003 branch (which matches an `expr_call` callee) is therefore
# unreachable from real source; a weak `todo(...)` falls into the
# REQC001 pass_* branch instead. `required_comment_lint_spec.spl`
# still proves the REQC003 branch itself is correct by constructing
# the `expr_call` shape directly.
var linter = Linter.new()
val results = lint_cli_source(linter, "sample.spl", "fn f():\n    todo(\"fix\")\n")
assert_true(has_code(results, "REQC001"))
assert_false(has_code(results, "REQC003"))
```

</details>

#### emits REQC004 through lint_cli_source for an unrationalized wildcard arm

- emits REQC004 through lint_cli_source for an unrationalized wildcard arm


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits REQC004 through lint_cli_source for an unrationalized wildcard arm")
var linter = Linter.new()
val results = lint_cli_source(linter, "sample.spl", "fn f():\n    match x:\n        case _: 0\n")
assert_true(has_code(results, "REQC004"))
```

</details>

#### emits exactly ONE REQC001 for a single-violation probe, not two

- emits exactly ONE REQC001 for a single-violation probe, not two
   - Expected: count_code(results, "REQC001") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits exactly ONE REQC001 for a single-violation probe, not two")
# Acceptance criterion (c): with the old text reimplementation
# deleted, only the AST-based checker can fire REQC001 — a bare
# pass_todo must produce exactly one diagnostic, not one from each
# of two live implementations.
var linter = Linter.new()
val results = lint_cli_source(linter, "sample_single.spl", "fn g():\n    pass_todo\n")
expect(count_code(results, "REQC001")).to_equal(1)
```

</details>

#### does NOT false-positive REQC001 on a multi-line pass_todo with a real rationale

- does NOT false-positive REQC001 on a multi-line pass_todo with a real rationale


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT false-positive REQC001 on a multi-line pass_todo with a real rationale")
# The disagreement case: the deleted text scanner checked ONE
# physical line at a time. `normalized.starts_with("pass_todo(")`
# on the opening-paren line alone (nothing else on that line) found
# no quoted string on THAT line and reported REQC001 even though the
# call carries a perfectly good rationale on the next line. The
# AST-based checker reads the real string-literal argument node
# regardless of which line it is printed on, so it must NOT flag
# this call.
var linter = Linter.new()
val source = "fn h():\n    pass_todo(\n        \"long enough rationale for this deferred work\",\n        \"tracked by SIMPLE-999\"\n    )\n"
val results = lint_cli_source(linter, "sample_multiline.spl", source)
assert_false(has_code(results, "REQC001"))
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ddd1e76062dc9518cb1f82fc922e2562f6ad83e3bcea3ec5ffbadcbb141fb221`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ddd1e76062dc9518cb1f82fc922e2562f6ad83e3bcea3ec5ffbadcbb141fb221`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ddd1e76062dc9518cb1f82fc922e2562f6ad83e3bcea3ec5ffbadcbb141fb221`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/lint/required_comment_cli_spec.spl
mirror: doc/06_spec/unit/compiler/lint/required_comment_cli_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/lint/required_comment_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/lint/required_comment_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/lint/required_comment_cli_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/lint/required_comment_cli_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits REQC001 through lint_cli_source for a bare pass_todo' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/lint/required_comment_cli_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits REQC001 (not REQC003) through lint_cli_source for a weak bare todo(...)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/lint/required_comment_cli_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits REQC004 through lint_cli_source for an unrationalized wildcard arm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
