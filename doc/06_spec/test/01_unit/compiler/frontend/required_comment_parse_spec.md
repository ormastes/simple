# Required Comment Parse Specification

> Tests that `pass_todo`, `pass_do_nothing`, and `pass_dn` emit a parser warning when used without a string comment argument. Also tests that a comment string present as an argument suppresses the warning and, when debug mode is active, is printed as a log message.

<!-- sdn-diagram:id=required_comment_parse_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=required_comment_parse_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

required_comment_parse_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=required_comment_parse_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Required Comment Parse Specification

Tests that `pass_todo`, `pass_do_nothing`, and `pass_dn` emit a parser warning when used without a string comment argument. Also tests that a comment string present as an argument suppresses the warning and, when debug mode is active, is printed as a log message.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #REQC-AC1, #REQC-AC2 |
| Category | Compiler \| Frontend \| Parser |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/compiler/frontend/required_comment_parse_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that `pass_todo`, `pass_do_nothing`, and `pass_dn` emit a parser warning
when used without a string comment argument. Also tests that a comment string
present as an argument suppresses the warning and, when debug mode is active,
is printed as a log message.

## Key Concepts

| Concept | Description |
|---------|-------------|
| REQC001 | Warning code for pass_* used without a comment string |
| par_warnings | Global warning list collected during parsing |
| parser_warn | Function that appends to par_warnings without setting par_had_error |
| debug log | rt_is_debug_mode_enabled() gate for printing comment at parse time |

## Behavior

- pass_todo / pass_do_nothing / pass_dn without parens -> warning emitted
- pass_todo() with empty parens -> warning emitted (no string inside)
- pass_todo("reason") -> no warning, comment stored in expr_s_val
- debug mode enabled + comment present -> comment printed via [debug:pass] prefix

## Scenarios

### pass_todo — required comment warning

#### when pass_todo has no argument

#### emits a REQC001 warning

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = collect_pass_warning("")
expect(ws.len()).to_be_greater_than(0)
assert_true(has_warning_for_code(ws, "REQC001"))
```

</details>

#### warning message mentions pass_todo

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = collect_pass_warning("")
expect(ws[0]).to_contain("pass_*")
```

</details>

#### when pass_todo has an empty string argument

#### still emits a REQC001 warning

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = collect_pass_warning("")
expect(ws.len()).to_equal(1)
assert_true(has_warning_for_code(ws, "REQC001"))
```

</details>

#### when pass_todo has a non-empty comment string

#### does NOT emit a warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = collect_pass_warning("implement later")
expect(ws.len()).to_equal(0)
```

</details>

#### stores the comment in the AST node expr_s_val

- expr reset
   - Expected: expr_get_tag(e) equals `40`
   - Expected: expr_get_str(e) equals `implement later`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expr_reset()
val e = expr_pass_todo("implement later", 0)
expect(expr_get_tag(e)).to_equal(40)
expect(expr_get_str(e)).to_equal("implement later")
```

</details>

#### when pass_todo has a comment string

#### comment string is non-empty

- expr reset
   - Expected: expr_get_str(e) equals `migration pending`
   - Expected: ws.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expr_reset()
val e = expr_pass_todo("migration pending", 0)
expect(expr_get_str(e)).to_equal("migration pending")
val ws = collect_pass_warning(expr_get_str(e))
expect(ws.len()).to_equal(0)
```

</details>

### pass_do_nothing — required comment warning

#### when pass_do_nothing has no argument

#### emits a REQC001 warning

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = collect_pass_warning("")
expect(ws.len()).to_be_greater_than(0)
assert_true(has_warning_for_code(ws, "REQC001"))
```

</details>

#### when pass_do_nothing has a non-empty comment

#### does NOT emit a warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = collect_pass_warning("intentional no-op: event handler not needed here")
expect(ws.len()).to_equal(0)
```

</details>

#### stores the comment in the AST node expr_s_val

- expr reset
   - Expected: expr_get_tag(e) equals `41`
   - Expected: expr_get_str(e) equals `intentional no-op: event handler not needed here`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expr_reset()
val e = expr_pass_do_nothing("intentional no-op: event handler not needed here", 0)
expect(expr_get_tag(e)).to_equal(41)
expect(expr_get_str(e)).to_equal("intentional no-op: event handler not needed here")
```

</details>

### pass_dn — required comment warning

#### when pass_dn has no argument

#### emits a REQC001 warning

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = collect_pass_warning("")
expect(ws.len()).to_be_greater_than(0)
assert_true(has_warning_for_code(ws, "REQC001"))
```

</details>

#### when pass_dn has a non-empty comment

#### does NOT emit a warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = collect_pass_warning("stub: will add retry logic in v2")
expect(ws.len()).to_equal(0)
```

</details>

#### stores the comment in the AST node

- expr reset
   - Expected: expr_get_tag(e) equals `43`
   - Expected: expr_get_str(e) equals `stub: will add retry logic in v2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expr_reset()
val e = expr_pass_dn("stub: will add retry logic in v2", 0)
expect(expr_get_tag(e)).to_equal(43)
expect(expr_get_str(e)).to_equal("stub: will add retry logic in v2")
```

</details>

### pass_* debug mode comment logging

#### when debug mode is disabled and comment is present

#### does not produce a debug log entry

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val should_log = debug_log_check(false, "some reason")
assert_false(should_log)
```

</details>

#### when debug mode is enabled and comment is empty

#### does not produce a debug log entry (no comment to log)

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val should_log = debug_log_check(true, "")
assert_false(should_log)
```

</details>

#### when debug mode is enabled and comment is present

#### produces a debug log entry

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val should_log = debug_log_check(true, "implement after refactor")
assert_true(should_log)
```

</details>

#### debug log message format

#### log message includes the comment string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = build_debug_log("implement after refactor")
expect(msg).to_contain("implement after refactor")
```

</details>

#### log message has [debug:pass] prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = build_debug_log("implement after refactor")
expect(msg).to_start_with("[debug:pass]")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
