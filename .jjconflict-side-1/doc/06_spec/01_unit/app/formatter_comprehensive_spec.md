# Formatter Comprehensive Specification

> <details>

<!-- sdn-diagram:id=formatter_comprehensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=formatter_comprehensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

formatter_comprehensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=formatter_comprehensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Formatter Comprehensive Specification

## Scenarios

### Formatter Comprehensive

#### keeps comma indentation and code line formatting passes available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = formatter_source()

expect(source).to_contain("fn fix_missing_commas(source: String) -> String")
expect(source).to_contain("fn fix_array_commas(text: String) -> String")
expect(source).to_contain("fn fix_dict_commas(text: String) -> String")
expect(source).to_contain("fn fix_param_commas(text: String) -> String")
expect(source).to_contain("fn fix_indentation(source: String) -> String")
expect(source).to_contain("fn format_code_lines(lines: [String]) -> Result<[String], String>")
```

</details>

#### keeps long line breaking and CLI formatting helpers available

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = formatter_source()

expect(source).to_contain("fn break_long_line(line: String, base_indent: Int) -> [String]")
expect(source).to_contain("fn is_method_chain(line: String) -> Bool")
expect(source).to_contain("fn break_method_chain(line: String, indent_str: String, continuation_str: String) -> [String]")
expect(source).to_contain("fn break_function_signature(line: String, indent_str: String, continuation_str: String) -> [String]")
expect(source).to_contain("fn break_function_call(line: String, indent_str: String, continuation_str: String) -> [String]")
expect(source).to_contain("fn format_file_inplace(path: String) -> Result<String, String>")
expect(source).to_contain("fn check_formatting(path: String) -> Result<Bool, String>")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/formatter_comprehensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Formatter Comprehensive

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
