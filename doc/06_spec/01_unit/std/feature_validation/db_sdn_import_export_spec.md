# Database SDN Table Import/Export Validation

> Validates that SdnTable can correctly parse SDN format including quoted values containing commas, and export back to SDN format. Tests the core split_sdn_row, strip_quotes, and quote_if_needed helpers.

<!-- sdn-diagram:id=db_sdn_import_export_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=db_sdn_import_export_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

db_sdn_import_export_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=db_sdn_import_export_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database SDN Table Import/Export Validation

Validates that SdnTable can correctly parse SDN format including quoted values containing commas, and export back to SDN format. Tests the core split_sdn_row, strip_quotes, and quote_if_needed helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #700 Database SDN table import/export |
| Category | Uncategorized |
| Status | Fixed |
| Source | `test/01_unit/std/feature_validation/db_sdn_import_export_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that SdnTable can correctly parse SDN format including
quoted values containing commas, and export back to SDN format.
Tests the core split_sdn_row, strip_quotes, and quote_if_needed helpers.

## Scenarios

### Feature #700 - SDN Row Parsing

#### simple row parsing

#### parses unquoted values

1. var parts = split sdn row
   - Expected: parts.len() equals `3`
   - Expected: parts[0].trim() equals `1`
   - Expected: parts[1].trim() equals `Alice`
   - Expected: parts[2].trim() equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var line = "1, Alice, true"
var parts = split_sdn_row(line)
expect(parts.len()).to_equal(3)
expect(parts[0].trim()).to_equal("1")
expect(parts[1].trim()).to_equal("Alice")
expect(parts[2].trim()).to_equal("true")
```

</details>

#### parses numeric values

1. var parts = split sdn row
   - Expected: parts.len() equals `3`
   - Expected: parts[0].trim() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var line = "42, 100, 200"
var parts = split_sdn_row(line)
expect(parts.len()).to_equal(3)
expect(parts[0].trim()).to_equal("42")
```

</details>

#### quoted value parsing

#### parses quoted strings without commas

1. var parts = split sdn row
   - Expected: parts.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var line = '1, "Alice", true'
var parts = split_sdn_row(line)
expect(parts.len()).to_equal(3)
```

</details>

#### parses quoted strings with commas

1. var parts = split sdn row
   - Expected: parts.len() equals `3`
2. var middle = parts[1] trim
3. var unquoted = strip quotes
   - Expected: unquoted equals `hello, world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var line = '1, "hello, world", true'
var parts = split_sdn_row(line)
expect(parts.len()).to_equal(3)
var middle = parts[1].trim()
var unquoted = strip_quotes(middle)
expect(unquoted).to_equal("hello, world")
```

</details>

#### handles multiple quoted fields

1. var parts = split sdn row
   - Expected: parts.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var line = '"Testing Framework", "Describe Blocks", "BDD describe blocks"'
var parts = split_sdn_row(line)
expect(parts.len()).to_equal(3)
```

</details>

#### strip_quotes helper

#### strips surrounding double quotes

1. var result = strip quotes
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = strip_quotes('"hello"')
expect(result).to_equal("hello")
```

</details>

#### leaves unquoted values unchanged

1. var result = strip quotes
   - Expected: result equals `plain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = strip_quotes("plain")
expect(result).to_equal("plain")
```

</details>

#### leaves empty string unchanged

1. var result = strip quotes
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = strip_quotes("")
expect(result).to_equal("")
```

</details>

#### leaves single char unchanged

1. var result = strip quotes
   - Expected: result equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = strip_quotes("x")
expect(result).to_equal("x")
```

</details>

#### quote_if_needed helper

#### quotes values with commas

1. var result = quote if needed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = quote_if_needed("hello, world")
expect(result).to_contain('"')
expect(result).to_start_with('"')
expect(result).to_end_with('"')
```

</details>

#### leaves values without commas unquoted

1. var result = quote if needed
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = quote_if_needed("hello")
expect(result).to_equal("hello")
```

</details>

#### leaves empty values unquoted

1. var result = quote if needed
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = quote_if_needed("")
expect(result).to_equal("")
```

</details>

### Feature #700 - SDN Table Round-Trip

#### simple table parsing

#### parses basic SDN table

1. var table = parse sdn table
   - Expected: table != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "users |id, name, active|\n    1, Alice, true\n    2, Bob, false"
var table = parse_sdn_table(content)
expect(table != nil).to_equal(true)
```

</details>

#### parses table with correct column count

1. var table opt = parse sdn table
   - Expected: table_opt != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "users |id, name|\n    1, Alice\n    2, Bob"
var table_opt = parse_sdn_table(content)
# Table should be parsed successfully
expect(table_opt != nil).to_equal(true)
```

</details>

#### table export

#### exports table to SDN format

1. var table = SdnTable new
2. var row1 = SdnTable empty row
3. table add row
4. var exported = table to sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SdnTable.new("test_table", ["id", "value"])
var row1 = SdnTable.empty_row()
row1["id"] = "1"
row1["value"] = "hello"
table.add_row(row1)

var exported = table.to_sdn()
expect(exported).to_contain("test_table")
expect(exported).to_contain("id")
expect(exported).to_contain("value")
expect(exported).to_contain("hello")
```

</details>

#### quoted value round-trip

#### preserves values with commas through export

1. var table = SdnTable new
2. var row = SdnTable empty row
3. table add row
4. var exported = table to sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SdnTable.new("data", ["id", "description"])
var row = SdnTable.empty_row()
row["id"] = "1"
row["description"] = "hello, world"
table.add_row(row)

var exported = table.to_sdn()
# Value with comma should be quoted in export
expect(exported).to_contain('"hello, world"')
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
