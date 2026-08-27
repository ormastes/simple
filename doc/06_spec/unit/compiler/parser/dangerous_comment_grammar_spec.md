# Dangerous Comment Grammar Parser Coverage

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dangerous Comment Grammar Parser Coverage

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/dangerous_comment_grammar_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### dangerous comment grammar parser

#### parses pass_todo with what-remains and hint strings

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses pass_todo with what-remains and hint strings
   - Expected: expr_get_tag(expr) equals `EXPR_PASS_TODO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses pass_todo with what-remains and hint strings")
parser_init("pass_todo(\"implement retry backoff\", \"tracked by SIMPLE-123\")")
val stmt = parse_statement()
val expr = stmt_get_expr(stmt)
expect(expr_get_tag(expr)).to_equal(EXPR_PASS_TODO)
expect(expr_get_str(expr)).to_contain("implement retry backoff")
expect(expr_get_str(expr)).to_contain("tracked by SIMPLE-123")
```

</details>

#### warns for bare pass_todo

- warns for bare pass_todo


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns for bare pass_todo")
parser_init("pass_todo")
parse_statement()
val warnings = parser_warnings_get()
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0]).to_contain("REQC001")
```

</details>

#### parses todo as a pass_todo placeholder expression

- parses todo as a pass_todo placeholder expression
   - Expected: expr_get_tag(expr) equals `EXPR_PASS_TODO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses todo as a pass_todo placeholder expression")
parser_init("todo(\"implement retry backoff\", \"tracked by SIMPLE-123\")")
val stmt = parse_statement()
val expr = stmt_get_expr(stmt)
expect(expr_get_tag(expr)).to_equal(EXPR_PASS_TODO)
expect(expr_get_str(expr)).to_contain("implement retry backoff")
expect(expr_get_str(expr)).to_contain("tracked by SIMPLE-123")
```

</details>

#### parses wildcard arm rationale metadata

- parses wildcard arm rationale metadata
   - Expected: arms.len() equals `1`
   - Expected: expr_get_str(arm_get_pattern(arms[0])) equals `_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses wildcard arm rationale metadata")
parser_init("match value:\n    case _(\"all remaining values share fallback\"):\n        pass_do_nothing(\"fallback has no side effects\")\n")
val stmt = parse_statement()
val arms = stmt_get_body(stmt)
expect(arms.len()).to_equal(1)
expect(expr_get_str(arm_get_pattern(arms[0]))).to_equal("_")
expect(arm_get_rationale(arms[0])).to_contain("all remaining values")
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3ac0cdf4e2c3a5f860c08844c00e539003ba069a99b6402afd5b5d051ec3e183`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3ac0cdf4e2c3a5f860c08844c00e539003ba069a99b6402afd5b5d051ec3e183`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3ac0cdf4e2c3a5f860c08844c00e539003ba069a99b6402afd5b5d051ec3e183`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/parser/dangerous_comment_grammar_spec.spl
mirror: doc/06_spec/unit/compiler/parser/dangerous_comment_grammar_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/dangerous_comment_grammar_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/dangerous_comment_grammar_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/dangerous_comment_grammar_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/parser/dangerous_comment_grammar_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses pass_todo with what-remains and hint strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/dangerous_comment_grammar_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns for bare pass_todo' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/dangerous_comment_grammar_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses todo as a pass_todo placeholder expression' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
