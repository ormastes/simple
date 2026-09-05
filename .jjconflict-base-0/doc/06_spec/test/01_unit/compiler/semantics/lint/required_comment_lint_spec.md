# Required Comment Lint Rule Specification

> Tests the `required_comment` lint rule that walks the AST to find `pass_*` nodes and dangerous keyword call nodes missing comment arguments. Results are reported as `RequiredCommentWarning` structs with codes REQC001 / REQC002. The rule is registered in LintConfig at "warn" level.

<!-- sdn-diagram:id=required_comment_lint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=required_comment_lint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

required_comment_lint_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=required_comment_lint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Required Comment Lint Rule Specification

Tests the `required_comment` lint rule that walks the AST to find `pass_*` nodes and dangerous keyword call nodes missing comment arguments. Results are reported as `RequiredCommentWarning` structs with codes REQC001 / REQC002. The rule is registered in LintConfig at "warn" level.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #REQC-AC4 |
| Category | Compiler \| Semantics \| Lint |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/compiler/semantics/lint/required_comment_lint_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the `required_comment` lint rule that walks the AST to find `pass_*`
nodes and dangerous keyword call nodes missing comment arguments. Results are
reported as `RequiredCommentWarning` structs with codes REQC001 / REQC002.
The rule is registered in LintConfig at "warn" level.

## Key Concepts

| Concept | Description |
|---------|-------------|
| REQC001 | pass_* used without a comment string |
| REQC002 | Dangerous keyword call without a comment string |
| RequiredCommentWarning | Struct: code, severity, message, hint, site_name, line |
| check_required_comment | Entry-point function for the lint rule |
| LintConfig | Registry that maps lint name to allow/warn/deny level |

## Scenarios

### required_comment lint — REQC001 pass_* detection

#### when pass_todo has no comment

#### emits REQC001 warning

- ast reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_pass_todo("", 0)
val d = make_fn_single_stmt("placeholder_fn", e)
val ws = check_required_comment([d])
val reqc001 = find_by_code(ws, "REQC001")
expect(reqc001.len()).to_be_greater_than(0)
```

</details>

#### warning severity is warn

- ast reset
   - Expected: reqc001[0].severity equals `warn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_pass_todo("", 0)
val d = make_fn_single_stmt("placeholder_fn", e)
val ws = check_required_comment([d])
val reqc001 = find_by_code(ws, "REQC001")
expect(reqc001[0].severity).to_equal("warn")
```

</details>

#### warning site_name matches the enclosing function name

- ast reset
   - Expected: reqc001[0].site_name equals `do_work`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_pass_todo("", 0)
val d = make_fn_single_stmt("do_work", e)
val ws = check_required_comment([d])
val reqc001 = find_by_code(ws, "REQC001")
expect(reqc001[0].site_name).to_equal("do_work")
```

</details>

#### when pass_do_nothing has no comment

#### emits REQC001 warning

- ast reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_pass_do_nothing("", 0)
val d = make_fn_single_stmt("noop_handler", e)
val ws = check_required_comment([d])
val reqc001 = find_by_code(ws, "REQC001")
expect(reqc001.len()).to_be_greater_than(0)
```

</details>

#### when pass_dn has no comment

#### emits REQC001 warning

- ast reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_pass_dn("", 0)
val d = make_fn_single_stmt("quiet_fn", e)
val ws = check_required_comment([d])
val reqc001 = find_by_code(ws, "REQC001")
expect(reqc001.len()).to_be_greater_than(0)
```

</details>

#### when pass_todo has a non-empty comment

#### does NOT emit REQC001

- ast reset
   - Expected: reqc001.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_pass_todo("implement after v2 launch", 0)
val d = make_fn_single_stmt("future_fn", e)
val ws = check_required_comment([d])
val reqc001 = find_by_code(ws, "REQC001")
expect(reqc001.len()).to_equal(0)
```

</details>

#### when pass_do_nothing has a non-empty comment

#### does NOT emit REQC001

- ast reset
   - Expected: reqc001.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_pass_do_nothing("intentional: callback not needed", 0)
val d = make_fn_single_stmt("event_sink", e)
val ws = check_required_comment([d])
val reqc001 = find_by_code(ws, "REQC001")
expect(reqc001.len()).to_equal(0)
```

</details>

#### when multiple pass_* nodes in one function

#### emits one REQC001 per missing comment

- ast reset
   - Expected: reqc001.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e1 = expr_pass_todo("", 0)
val e2 = expr_pass_do_nothing("", 0)
val s1 = stmt_expr_stmt(e1, 0)
val s2 = stmt_expr_stmt(e2, 0)
val d = decl_fn("multi_pass", [], [], 0, [s1, s2], 0, [], 0)
val ws = check_required_comment([d])
val reqc001 = find_by_code(ws, "REQC001")
expect(reqc001.len()).to_equal(2)
```

</details>

### required_comment lint — REQC002 dangerous keyword detection

#### when dangerous_token_but_needs is called without comment

#### emits REQC002 warning

- ast reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val callee = expr_ident("dangerous_token_but_needs", 0)
# Empty args list = no comment
val e = expr_call(callee, [], 0)
val d = make_fn_single_stmt("risky_fn", e)
val ws = check_required_comment([d])
val reqc002 = find_by_code(ws, "REQC002")
expect(reqc002.len()).to_be_greater_than(0)
```

</details>

#### warning severity is warn

- ast reset
   - Expected: reqc002[0].severity equals `warn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val callee = expr_ident("dangerous_token_but_needs", 0)
val e = expr_call(callee, [], 0)
val d = make_fn_single_stmt("risky_fn", e)
val ws = check_required_comment([d])
val reqc002 = find_by_code(ws, "REQC002")
expect(reqc002[0].severity).to_equal("warn")
```

</details>

#### when dangerous_token_but_needs is called with a comment string

#### does NOT emit REQC002

- ast reset
   - Expected: reqc002.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val callee = expr_ident("dangerous_token_but_needs", 0)
val comment_arg = expr_string_lit("ABI freeze requires this", 0)
val e = expr_call(callee, [comment_arg], 0)
val d = make_fn_single_stmt("risky_fn", e)
val ws = check_required_comment([d])
val reqc002 = find_by_code(ws, "REQC002")
expect(reqc002.len()).to_equal(0)
```

</details>

#### when loss is called without comment in statement position

#### emits REQC002 warning

- ast reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val callee = expr_ident("loss", 0)
val e = expr_call(callee, [], 0)
val d = make_fn_single_stmt("train_step", e)
val ws = check_required_comment([d])
val reqc002 = find_by_code(ws, "REQC002")
expect(reqc002.len()).to_be_greater_than(0)
```

</details>

#### when loss is called with a comment

#### does NOT emit REQC002

- ast reset
   - Expected: reqc002.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val callee = expr_ident("loss", 0)
val comment_arg = expr_string_lit("gradient accumulation intentional", 0)
val e = expr_call(callee, [comment_arg], 0)
val d = make_fn_single_stmt("train_step", e)
val ws = check_required_comment([d])
val reqc002 = find_by_code(ws, "REQC002")
expect(reqc002.len()).to_equal(0)
```

</details>

#### when an ordinary function call is present

#### does NOT emit REQC002 for non-dangerous identifiers

- ast reset
   - Expected: reqc002.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val callee = expr_ident("compute_value", 0)
val e = expr_call(callee, [], 0)
val d = make_fn_single_stmt("normal_fn", e)
val ws = check_required_comment([d])
val reqc002 = find_by_code(ws, "REQC002")
expect(reqc002.len()).to_equal(0)
```

</details>

### RequiredCommentWarning — struct fields and fmt()

#### REQC001 warning fields

#### code is REQC001

- ast reset
   - Expected: reqc001[0].code equals `REQC001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_pass_todo("", 0)
val d = make_fn_single_stmt("check_fn", e)
val ws = check_required_comment([d])
val reqc001 = find_by_code(ws, "REQC001")
expect(reqc001[0].code).to_equal("REQC001")
```

</details>

#### hint field is non-empty

- ast reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_pass_todo("", 0)
val d = make_fn_single_stmt("check_fn", e)
val ws = check_required_comment([d])
val reqc001 = find_by_code(ws, "REQC001")
val hint = reqc001[0].hint
expect(hint.len()).to_be_greater_than(0)
```

</details>

#### fmt() includes the code

- ast reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_pass_todo("", 0)
val d = make_fn_single_stmt("check_fn", e)
val ws = check_required_comment([d])
val reqc001 = find_by_code(ws, "REQC001")
val formatted = reqc001[0].fmt()
expect(formatted).to_contain("REQC001")
```

</details>

#### fmt() includes the site_name

- ast reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_pass_todo("", 0)
val d = make_fn_single_stmt("important_fn", e)
val ws = check_required_comment([d])
val reqc001 = find_by_code(ws, "REQC001")
val formatted = reqc001[0].fmt()
expect(formatted).to_contain("important_fn")
```

</details>

### required_comment lint registration in LintConfig

#### required_comment appears in ALL_LINT_NAMES

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_names = get_all_lint_names_test()
expect(_contains_text(all_names, "required_comment"))
```

</details>

#### default level for required_comment is warn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = get_lint_default_level_test("required_comment")
expect(level).to_equal("warn")
```

</details>

#### REQC001 maps to required_comment in code-to-name mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = map_lint_code_test("REQC001")
expect(name).to_equal("required_comment")
```

</details>

#### REQC002 maps to required_comment in code-to-name mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = map_lint_code_test("REQC002")
expect(name).to_equal("required_comment")
```

</details>

#### REQC003 maps to required_comment in code-to-name mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = map_lint_code_test("REQC003")
expect(name).to_equal("required_comment")
```

</details>

#### REQC004 maps to required_comment in code-to-name mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = map_lint_code_test("REQC004")
expect(name).to_equal("required_comment")
```

</details>

### required_comment lint — REQC003 todo detection

#### emits REQC003 for todo without two useful strings

- ast reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val callee = expr_ident("todo", 0)
val e = expr_call(callee, [], 0)
val d = make_fn_single_stmt("unfinished_fn", e)
val ws = check_required_comment([d])
val reqc003 = find_by_code(ws, "REQC003")
expect(reqc003.len()).to_be_greater_than(0)
```

</details>

#### does not emit REQC003 for canonical todo form

- ast reset
- expr string lit
- expr string lit
   - Expected: reqc003.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val callee = expr_ident("todo", 0)
val e = expr_call(callee, [
    expr_string_lit("implement retry backoff", 0),
    expr_string_lit("tracked by issue SIMPLE-123", 0)
], 0)
val d = make_fn_single_stmt("unfinished_fn", e)
val ws = check_required_comment([d])
val reqc003 = find_by_code(ws, "REQC003")
expect(reqc003.len()).to_equal(0)
```

</details>

### required_comment lint — REQC004 wildcard arm detection

#### emits REQC004 for wildcard match arm without rationale

- ast reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val pattern = expr_ident("_", 0)
val arm = arm_new_with_binding_and_rationale(pattern, -1, [stmt_expr_stmt(expr_unit(0), 0)], "", "")
val match_stmt = stmt_match_stmt(expr_ident("value", 0), [arm], 0)
val d = decl_fn("classify", [], [], 0, [match_stmt], 0, [], 0)
val ws = check_required_comment([d])
val reqc004 = find_by_code(ws, "REQC004")
expect(reqc004.len()).to_be_greater_than(0)
```

</details>

#### does not emit REQC004 for wildcard match arm with rationale

- ast reset
   - Expected: reqc004.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val pattern = expr_ident("_", 0)
val arm = arm_new_with_binding_and_rationale(pattern, -1, [stmt_expr_stmt(expr_unit(0), 0)], "", "all enum variants already normalized by parser")
val match_stmt = stmt_match_stmt(expr_ident("value", 0), [arm], 0)
val d = decl_fn("classify", [], [], 0, [match_stmt], 0, [], 0)
val ws = check_required_comment([d])
val reqc004 = find_by_code(ws, "REQC004")
expect(reqc004.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
