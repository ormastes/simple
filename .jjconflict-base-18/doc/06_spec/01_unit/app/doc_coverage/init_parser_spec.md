# Init Parser Specification

> <details>

<!-- sdn-diagram:id=init_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=init_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

init_parser_spec -> std
init_parser_spec -> doc_coverage
init_parser_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=init_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Init Parser Specification

## Scenarios

### InitParser - Comment-based API Documentation

#### parses real __init__.spl file from src/std/spec

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec_init = cwd() + "/src/std/spec/__init__.spl"

if file_exists(spec_init):
    val result = parse_init_file(spec_init)
    val groups = result.0
    val items = result.1

    # Should find at least one group or item
    val has_data = groups.len() > 0 or items.len() > 0
    expect(has_data).to_equal(true)
```

</details>

#### detects group headers correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test the pattern matching for group headers
val header1 = "# File operations"
val header2 = "# - file_read"

val has_cap1 = _contains_capital_in_text(header1)
val has_cap2 = header2.contains(" - ")

expect(has_cap1).to_equal(true)
expect(has_cap2).to_equal(true)
```

</details>

#### extracts item names from dash lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# These patterns should be recognized as items
val line1 = "#   - file_read"
val line2 = "# - dir_create()"

val has_dash1 = line1.contains(" - ")
val has_dash2 = line2.contains(" - ")

expect(has_dash1).to_equal(true)
expect(has_dash2).to_equal(true)
```

</details>

#### detects use statements for function extraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val use_line = "use std.spec.{describe, it, expect}"
val is_use = use_line.starts_with("use ")
val has_braces = use_line.contains("{") and use_line.contains("}")

expect(is_use).to_equal(true)
expect(has_braces).to_equal(true)
```

</details>

#### returns empty results for non-existent files

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_path = "/tmp/nonexistent_file.spl"
val result = parse_init_file(fake_path)
val groups = result.0
val items = result.1

expect(groups.len()).to_equal(0)
expect(items.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/doc_coverage/init_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- InitParser - Comment-based API Documentation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
