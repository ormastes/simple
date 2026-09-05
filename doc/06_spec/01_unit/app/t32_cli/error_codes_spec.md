# Error Codes Specification

> <details>

<!-- sdn-diagram:id=error_codes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=error_codes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

error_codes_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=error_codes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Codes Specification

## Scenarios

### T32 Error Codes — suggest_similar

#### finds prefix matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = ["sessions", "cores", "windows", "help"]
val matches = t32_suggest_similar("sess", candidates)
expect(matches.len() > 0).to_equal(true)
expect(matches[0]).to_equal("sessions")
```

</details>

#### finds first-char matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = ["windows", "window", "field"]
val matches = t32_suggest_similar("w", candidates)
expect(matches.len()).to_equal(2)
```

</details>

#### returns empty for no matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = ["sessions", "cores"]
val matches = t32_suggest_similar("xyz", candidates)
expect(matches.len()).to_equal(0)
```

</details>

#### handles empty name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = ["sessions", "cores"]
val matches = t32_suggest_similar("", candidates)
expect(matches.len()).to_equal(0)
```

</details>

### T32 Error Codes — did_you_mean

#### suggests closest match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hint = t32_did_you_mean("winows", ["sessions", "cores", "windows", "help"])
expect(hint).to_contain("windows")
expect(hint).to_start_with("Did you mean:")
```

</details>

#### returns empty when no match

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hint = t32_did_you_mean("xyz", ["sessions", "cores"])
expect(hint).to_equal("")
```

</details>

### T32 Error Codes — join_list

#### joins items with separator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_join_list(["a", "b", "c"], ", ")
expect(result).to_equal("a, b, c")
```

</details>

#### handles single item

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_join_list(["only"], ", ")
expect(result).to_equal("only")
```

</details>

#### handles empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_join_list([], ", ")
expect(result).to_equal("")
```

</details>

### T32 Error Codes — message builders

#### t32_err_unknown_cmd includes T4001 and available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_unknown_cmd("winows")
expect(msg).to_contain("T4001")
expect(msg).to_contain("winows")
expect(msg).to_contain("Available:")
expect(msg).to_contain("windows")
```

</details>

#### t32_err_unknown_subcmd includes T4002

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_unknown_subcmd("sessions", "opn", ["open", "close", "use", "info"])
expect(msg).to_contain("T4002")
expect(msg).to_contain("opn")
expect(msg).to_contain("open")
```

</details>

#### t32_err_missing_args includes T4003 and example

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_missing_args("field", "field <get|set> <key>", "field get symbol")
expect(msg).to_contain("T4003")
expect(msg).to_contain("Usage:")
expect(msg).to_contain("Example:")
```

</details>

#### t32_err_not_found includes code and available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_not_found("T4030", "window", "xyz", ["register", "data_list"])
expect(msg).to_contain("T4030")
expect(msg).to_contain("xyz")
expect(msg).to_contain("Available:")
expect(msg).to_contain("register")
```

</details>

#### t32_err_no_session includes T4013

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_no_session()
expect(msg).to_contain("T4013")
expect(msg).to_contain("sessions open")
```

</details>

#### t32_err_session_duplicate includes T4011

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_session_duplicate("T32_ARM", "s1")
expect(msg).to_contain("T4011")
expect(msg).to_contain("T32_ARM")
expect(msg).to_contain("s1")
```

</details>

#### t32_err_session_closed includes T4012

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_session_closed("s1")
expect(msg).to_contain("T4012")
expect(msg).to_contain("s1")
```

</details>

#### t32_err_missing_param includes T4082 with usage

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_missing_param("command", "t32_cmd_run", "t32_cmd_run(command: \"...\")", "t32_cmd_run(command: \"Break.Set main\")")
expect(msg).to_contain("T4082")
expect(msg).to_contain("command")
expect(msg).to_contain("t32_cmd_run")
expect(msg).to_contain("Usage:")
expect(msg).to_contain("Example:")
```

</details>

#### t32_err_unknown_tool includes T4081 and available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_unknown_tool("t32_sesions_list")
expect(msg).to_contain("T4081")
expect(msg).to_contain("Available:")
expect(msg).to_contain("t32_sessions_list")
```

</details>

#### t32_err_resource_not_found includes T4090 and valid URIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_resource_not_found("t32:///invalid")
expect(msg).to_contain("T4090")
expect(msg).to_contain("t32:///sessions")
```

</details>

#### t32_err_missing_tool_name includes T4080

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_missing_tool_name()
expect(msg).to_contain("T4080")
```

</details>

#### t32_err_catalog_warning includes T4060

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_catalog_warning("/missing/path.sdn")
expect(msg).to_contain("T4060")
expect(msg).to_contain("/missing/path.sdn")
```

</details>

#### t32_err_t32rem_not_found includes T4070

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_t32rem_not_found()
expect(msg).to_contain("T4070")
expect(msg).to_contain("T32REM")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/t32_cli/error_codes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Error Codes — suggest_similar
- T32 Error Codes — did_you_mean
- T32 Error Codes — join_list
- T32 Error Codes — message builders

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
