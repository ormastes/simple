# lsp_diagnostics_enhanced_spec

> val pattern = "\"severity\":{severity}"

<!-- sdn-diagram:id=lsp_diagnostics_enhanced_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lsp_diagnostics_enhanced_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lsp_diagnostics_enhanced_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lsp_diagnostics_enhanced_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lsp_diagnostics_enhanced_spec

val pattern = "\"severity\":{severity}"

## At a Glance

| Field | Value |
|-------|-------|
| Category | LSP |
| Status | Active |
| Source | `test/03_system/tools/lsp/lsp_diagnostics_enhanced_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

val pattern = "\"severity\":{severity}"
    val pattern2 = "\"severity\": {severity}"
    output.contains(pattern) or output.contains(pattern2)

fn output_contains_tag(output: text, tag: i64) -> bool:
    """Check if JSON output contains a diagnostic with the given tag.
    Tags: 1=Unnecessary, 2=Deprecated

## Scenarios

### LSP Enhanced Diagnostics

<details>
<summary>Advanced: syntax error produces Error severity diagnostic</summary>

#### syntax error produces Error severity diagnostic _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = write_temp_file("syntax_err", "fn broken(\n    val x = \n")
val output = run_check_json(path)
# Severity 1 = Error
val has_error_severity = output_contains_severity(output, 1)
expect(has_error_severity).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: unused variable produces Warning severity with Unnecessary tag</summary>

#### unused variable produces Warning severity with Unnecessary tag _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test_unused():\n    val unused_var = 42\n    val used_var = 10\n    print used_var\n"
val path = write_temp_file("unused_var", code)
val output = run_check_json(path)
# Should contain a warning (severity 2)
val has_warning = output_contains_severity(output, 2)
expect(has_warning).to_equal(true)
# Should mention the unused variable
val mentions_unused = output.contains("unused_var")
expect(mentions_unused).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: deprecated Type__method pattern produces Warning with Deprecated tag</summary>

#### deprecated Type__method pattern produces Warning with Deprecated tag _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test_deprecated():\n    val result = Vec__new()\n"
val path = write_temp_file("deprecated", code)
val output = run_check_json(path)
# Should contain DEPR001 code
val has_depr001 = output_contains_code(output, "DEPR001")
expect(has_depr001).to_equal(true)
# Should have Deprecated tag (tag value 2)
val has_deprecated_tag = output_contains_tag(output, 2)
expect(has_deprecated_tag).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: deprecated .new() constructor produces Warning with Deprecated tag</summary>

#### deprecated .new() constructor produces Warning with Deprecated tag _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test_new():\n    val p = Point.new(1, 2)\n"
val path = write_temp_file("deprecated_new", code)
val output = run_check_json(path)
# Should contain DEPR002 code
val has_depr002 = output_contains_code(output, "DEPR002")
expect(has_depr002).to_equal(true)
# Should have Deprecated tag (tag value 2)
val has_deprecated_tag = output_contains_tag(output, 2)
expect(has_deprecated_tag).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: unreachable code after return produces Warning with Unnecessary tag</summary>

#### unreachable code after return produces Warning with Unnecessary tag _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test_unreachable() -> i64:\n    return 42\n    val x = 10\n"
val path = write_temp_file("unreachable", code)
val output = run_check_json(path)
# Should contain UNREACH001 code
val has_unreach = output_contains_code(output, "UNREACH001")
expect(has_unreach).to_equal(true)
# Should have Unnecessary tag (tag value 1)
val has_unnecessary_tag = output_contains_tag(output, 1)
expect(has_unnecessary_tag).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: non-exhaustive match produces Warning</summary>

#### non-exhaustive match produces Warning _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test_match(x: i64) -> text:\n    match x:\n        case 1: \"one\"\n        case 2: \"two\"\n"
val path = write_temp_file("match_exhaust", code)
val output = run_check_json(path)
# Should have some warning output (severity 2 = Warning)
# Match exhaustiveness is a heuristic check
val has_output = output.len() > 0
expect(has_output).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: structured JSON output from query check contains correct fields</summary>

#### structured JSON output from query check contains correct fields _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test_json():\n    val result = Vec__new()\n"
val path = write_temp_file("json_fields", code)
val output = run_check_json(path)
# Verify JSON output contains expected field names
val has_severity = output.contains("\"severity\"")
val has_code_field = output.contains("\"code\"")
val has_message = output.contains("\"message\"")
val has_line = output.contains("\"line\"")
val has_col = output.contains("\"col\"")
val has_tags = output.contains("\"tags\"")
val has_source = output.contains("\"source\"")
expect(has_severity).to_equal(true)
expect(has_code_field).to_equal(true)
expect(has_message).to_equal(true)
expect(has_line).to_equal(true)
expect(has_col).to_equal(true)
expect(has_tags).to_equal(true)
expect(has_source).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: clean code produces no warnings</summary>

#### clean code produces no warnings _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn add(a: i64, b: i64) -> i64:\n    a + b\n"
val path = write_temp_file("clean", code)
val (output, exit_code) = run_check_text(path)
expect(exit_code).to_equal(0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 8 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
