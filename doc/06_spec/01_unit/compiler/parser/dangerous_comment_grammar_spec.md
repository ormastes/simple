# Dangerous Comment Grammar Parser Coverage

> <details>

<!-- sdn-diagram:id=dangerous_comment_grammar_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dangerous_comment_grammar_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dangerous_comment_grammar_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dangerous_comment_grammar_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/compiler/parser/dangerous_comment_grammar_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### dangerous comment grammar parser

#### parses pass_todo with what-remains and hint strings

- parser init
   - Expected: expr_get_tag(expr) equals `EXPR_PASS_TODO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("pass_todo(\"implement retry backoff\", \"tracked by SIMPLE-123\")")
val stmt = parse_statement()
val expr = stmt_get_expr(stmt)
expect(expr_get_tag(expr)).to_equal(EXPR_PASS_TODO)
expect(expr_get_str(expr)).to_contain("implement retry backoff")
expect(expr_get_str(expr)).to_contain("tracked by SIMPLE-123")
```

</details>

#### warns for bare pass_todo

- parser init
- parse statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("pass_todo")
parse_statement()
val warnings = parser_warnings_get()
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0]).to_contain("REQC001")
```

</details>

#### parses todo as a pass_todo placeholder expression

- parser init
   - Expected: expr_get_tag(expr) equals `EXPR_PASS_TODO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("todo(\"implement retry backoff\", \"tracked by SIMPLE-123\")")
val stmt = parse_statement()
val expr = stmt_get_expr(stmt)
expect(expr_get_tag(expr)).to_equal(EXPR_PASS_TODO)
expect(expr_get_str(expr)).to_contain("implement retry backoff")
expect(expr_get_str(expr)).to_contain("tracked by SIMPLE-123")
```

</details>

#### parses wildcard arm rationale metadata

- parser init
   - Expected: arms.len() equals `1`
   - Expected: expr_get_str(arm_get_pattern(arms[0])) equals `_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
