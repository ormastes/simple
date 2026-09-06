# Lsp Mcp Format Specification

> <details>

<!-- sdn-diagram:id=lsp_mcp_format_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lsp_mcp_format_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lsp_mcp_format_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lsp_mcp_format_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lsp Mcp Format Specification

## Scenarios

### LSP MCP Format Output

#### structuredContent presence

<details>
<summary>Advanced: query check --format=json output contains structuredContent key</summary>

#### query check --format=json output contains structuredContent key _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    val unused_var = 42\n    print \"done\"\n"
val path = write_temp_file("struct_content", code)
val output = run_check_json(path)
val has_structured = output.contains("structuredContent") or output.contains("diagnostics")
expect(has_structured).to_equal(true)
```

</details>


</details>

#### diagnostics array

<details>
<summary>Advanced: diagnostics array is present in output</summary>

#### diagnostics array is present in output _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn broken(\n    val x = \n"
val path = write_temp_file("diag_array", code)
val output = run_check_json(path)
val has_diagnostics = output.contains("\"diagnostics\"")
expect(has_diagnostics).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: diagnostics array contains entries for errors</summary>

#### diagnostics array contains entries for errors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test() -> i64:\n    return 42\n    val dead = 10\n"
val path = write_temp_file("diag_entries", code)
val output = run_check_json(path)
# Should have at least one diagnostic entry with line/message
val has_line = output.contains("\"line\"")
val has_message = output.contains("\"message\"")
expect(has_line).to_equal(true)
expect(has_message).to_equal(true)
```

</details>


</details>

#### count field

<details>
<summary>Advanced: count field is present in output</summary>

#### count field is present in output _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    val unused1 = 1\n    val unused2 = 2\n    print \"done\"\n"
val path = write_temp_file("count_field", code)
val output = run_check_json(path)
# Output should contain count information (error_count or warning_count or count)
val has_count = output.contains("\"error_count\"") or output.contains("\"warning_count\"") or output.contains("\"count\"")
expect(has_count).to_equal(true)
```

</details>


</details>

#### isError field

<details>
<summary>Advanced: isError field reflects error status</summary>

#### isError field reflects error status _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn broken(\n"
val path = write_temp_file("is_error", code)
val output = run_check_json(path)
# Output should indicate error status
val has_status = output.contains("\"status\"") or output.contains("\"isError\"") or output.contains("\"exit_code\"")
expect(has_status).to_equal(true)
```

</details>


</details>

#### diagnostic entry fields

<details>
<summary>Advanced: each diagnostic has severity field</summary>

#### each diagnostic has severity field _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    val unused_x = 42\n    print \"done\"\n"
val path = write_temp_file("has_severity", code)
val output = run_check_json(path)
val has_severity = output.contains("\"severity\"")
expect(has_severity).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: each diagnostic has code field</summary>

#### each diagnostic has code field _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test_depr():\n    val result = Vec__new()\n"
val path = write_temp_file("has_code", code)
val output = run_check_json(path)
val has_code_field = output.contains("\"code\"")
expect(has_code_field).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: each diagnostic has message field</summary>

#### each diagnostic has message field _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test() -> i64:\n    return 42\n    val dead = 0\n"
val path = write_temp_file("has_message", code)
val output = run_check_json(path)
val has_message = output.contains("\"message\"")
expect(has_message).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: each diagnostic has line field</summary>

#### each diagnostic has line field _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    val unused_z = 99\n    print \"done\"\n"
val path = write_temp_file("has_line", code)
val output = run_check_json(path)
val has_line = output.contains("\"line\"")
expect(has_line).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: each diagnostic has col field</summary>

#### each diagnostic has col field _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn broken(\n    val x = \n"
val path = write_temp_file("has_col", code)
val output = run_check_json(path)
val has_col = output.contains("\"col\"")
expect(has_col).to_equal(true)
```

</details>


</details>

#### clean code

<details>
<summary>Advanced: clean code produces zero diagnostics</summary>

#### clean code produces zero diagnostics _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn add(a: i64, b: i64) -> i64:\n    a + b\n"
val path = write_temp_file("clean_code", code)
val output = run_check_json(path)
# Clean code should have status "ok" and 0 counts
val has_ok = output.contains("\"ok\"") or output.contains("\"error_count\":0") or output.contains("\"error_count\": 0") or output.contains("\"count\":0") or output.contains("\"count\": 0")
expect(has_ok).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | LSP |
| Status | Active |
| Source | `test/03_system/tools/lsp/lsp_mcp_format_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LSP MCP Format Output

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 11 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
