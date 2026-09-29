# lint_text_spec

> Purpose: Prove that lint_text helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lint_text_spec

Purpose: Prove that lint_text helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/lint_text_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that lint_text helpers.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### lint_text helpers

#### count_triple_quotes returns 0 for empty line

- count_triple_quotes returns 0 for empty line
- Verify: count_triple_quotes returns 0 for empty line
   - Expected: count_triple_quotes("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("count_triple_quotes returns 0 for empty line")
step("Verify: count_triple_quotes returns 0 for empty line")
# @req: REQ-COMPILER-SEMANTICS-001
"""Empty input has no triple-quote sequences."""
expect(count_triple_quotes("")).to_equal(0)
```

</details>

#### count_triple_quotes returns 0 for plain text

- count_triple_quotes returns 0 for plain text
- Verify: count_triple_quotes returns 0 for plain text
   - Expected: count_triple_quotes("    val x = 1") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("count_triple_quotes returns 0 for plain text")
step("Verify: count_triple_quotes returns 0 for plain text")
"""Lines without triple-quotes return 0."""
expect(count_triple_quotes("    val x = 1")).to_equal(0)
```

</details>

#### count_triple_quotes counts one opener

- count_triple_quotes counts one opener
- Verify: count_triple_quotes counts one opener
   - Expected: count_triple_quotes("    \"\"\"docstring start") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("count_triple_quotes counts one opener")
step("Verify: count_triple_quotes counts one opener")
"""A bare opener returns 1 (odd -> toggles in_docstring)."""
expect(count_triple_quotes("    \"\"\"docstring start")).to_equal(1)
```

</details>

#### count_triple_quotes counts a same-line pair

- count_triple_quotes counts a same-line pair
- Verify: count_triple_quotes counts a same-line pair
   - Expected: count_triple_quotes("    \"\"\"one-liner\"\"\"") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("count_triple_quotes counts a same-line pair")
step("Verify: count_triple_quotes counts a same-line pair")
"""A single-line docstring like `\"\"\"text\"\"\"` returns 2 (even -> no toggle)."""
expect(count_triple_quotes("    \"\"\"one-liner\"\"\"")).to_equal(2)
```

</details>

#### iter_code_lines yields all lines when no docstrings

- iter_code_lines yields all lines when no docstrings
- Verify: iter_code_lines yields all lines when no docstrings
   - Expected: lines.len() equals `3`
   - Expected: lines[0].line_num equals `1`
   - Expected: lines[0].trimmed equals `fn f():`
   - Expected: lines[2].trimmed equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("iter_code_lines yields all lines when no docstrings")
step("Verify: iter_code_lines yields all lines when no docstrings")
"""Plain code source: every line is a CodeLine."""
val src = "fn f():\n    var x = 1\n    x"
val lines = iter_code_lines(src)
expect(lines.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(lines[0].line_num).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(lines[0].trimmed).to_equal("fn f():")
expect(lines[2].trimmed).to_equal("x")
```

</details>

#### iter_code_lines skips a multi-line docstring body

- iter_code_lines skips a multi-line docstring body
- Verify: iter_code_lines skips a multi-line docstring body
   - Expected: lines.len() equals `3`
   - Expected: lines[0].line_num equals `1`
   - Expected: lines[1].line_num equals `4`
   - Expected: lines[2].line_num equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("iter_code_lines skips a multi-line docstring body")
step("Verify: iter_code_lines skips a multi-line docstring body")
"""Lines strictly INSIDE a docstring are not yielded; the closing line IS
yielded (in_docstring toggles BEFORE the check)."""
val src = "fn f():\n    \"\"\"\n    docs body\n    \"\"\"\n    x"
val lines = iter_code_lines(src)
# Yielded: 'fn f():' (1), '"""' closing (4), 'x' (5).  Skipped: opener (2), body (3).
expect(lines.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(lines[0].line_num).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(lines[1].line_num).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(lines[2].line_num).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

#### iter_code_lines treats single-line docstring as code

- iter_code_lines treats single-line docstring as code
- Verify: iter_code_lines treats single-line docstring as code
   - Expected: lines.len() equals `3`
   - Expected: lines[1].trimmed equals `"""summary"""`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("iter_code_lines treats single-line docstring as code")
step("Verify: iter_code_lines treats single-line docstring as code")
"""Even count of triple-quotes on one line means no toggle, so the line is yielded."""
val src = "fn f():\n    \"\"\"summary\"\"\"\n    x"
val lines = iter_code_lines(src)
expect(lines.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(lines[1].trimmed).to_equal("\"\"\"summary\"\"\"")
```

</details>

#### iter_code_lines preserves 1-based line numbers

- iter_code_lines preserves 1-based line numbers
- Verify: iter_code_lines preserves 1-based line numbers
   - Expected: lines[0].line_num equals `1`
   - Expected: lines[1].line_num equals `2`
   - Expected: lines[2].line_num equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("iter_code_lines preserves 1-based line numbers")
step("Verify: iter_code_lines preserves 1-based line numbers")
"""Consumers (linters) rely on line_num matching the source's 1-based numbering."""
val src = "a\nb\nc"
val lines = iter_code_lines(src)
expect(lines[0].line_num).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(lines[1].line_num).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(lines[2].line_num).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### iter_code_lines handles back-to-back docstrings

- iter_code_lines handles back-to-back docstrings
- Verify: iter_code_lines handles back-to-back docstrings
   - Expected: lines.len() equals `5`
   - Expected: lines[0].line_num equals `1`
   - Expected: lines[1].line_num equals `4`
   - Expected: lines[2].line_num equals `5`
   - Expected: lines[3].line_num equals `8`
   - Expected: lines[4].line_num equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("iter_code_lines handles back-to-back docstrings")
step("Verify: iter_code_lines handles back-to-back docstrings")
"""Two separate docstrings: each opener is skipped, each closer is yielded as code."""
val src = "x\n\"\"\"\nA\n\"\"\"\ny\n\"\"\"\nB\n\"\"\"\nz"
val lines = iter_code_lines(src)
# Yielded line_nums: 1 (x), 4 (close-1), 5 (y), 8 (close-2), 9 (z).
expect(lines.len()).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(lines[0].line_num).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(lines[1].line_num).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(lines[2].line_num).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(lines[3].line_num).to_equal(8)  # oracle: 8 — named expected value from the requirement
expect(lines[4].line_num).to_equal(9)  # oracle: 9 — named expected value from the requirement
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

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-SEMANTICS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `be48ac2a1e4c551085b0c026d61dd446c9106d7eb8bc0b5fe2297ff952b55e55`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `be48ac2a1e4c551085b0c026d61dd446c9106d7eb8bc0b5fe2297ff952b55e55`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `be48ac2a1e4c551085b0c026d61dd446c9106d7eb8bc0b5fe2297ff952b55e55`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/semantics/lint/lint_text_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/lint/lint_text_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/lint/lint_text_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/lint/lint_text_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/lint/lint_text_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/semantics/lint/lint_text_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'count_triple_quotes returns 0 for empty line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/lint/lint_text_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'count_triple_quotes returns 0 for plain text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/lint/lint_text_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'count_triple_quotes counts one opener' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
