# Sdn Reader Utf8 Specification

> <details>

<!-- sdn-diagram:id=sdn_reader_utf8_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sdn_reader_utf8_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sdn_reader_utf8_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sdn_reader_utf8_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdn Reader Utf8 Specification

## Scenarios

### split_sdn_row with multibyte UTF-8

#### splits a row whose quoted field holds an em-dash without crashing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "1, \"em—dash title\", true"
val parts = split_sdn_row(line)
expect(parts.len()).to_equal(3)
```

</details>

#### round-trips the em-dash field content through strip_quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "1, \"em—dash title\", true"
val parts = split_sdn_row(line)
val title = strip_quotes(parts[1].trim())
expect(title).to_equal("em—dash title")
```

</details>

#### keeps a quoted field with both a comma and an em-dash intact

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "id1, \"a, b — c\", open"
val parts = split_sdn_row(line)
expect(parts.len()).to_equal(3)
val title = strip_quotes(parts[1].trim())
expect(title).to_equal("a, b — c")
```

</details>

### strip_quotes with multibyte UTF-8

#### strips surrounding quotes from an em-dash value by char count

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(strip_quotes("\"em—dash\"")).to_equal("em—dash")
```

</details>

#### leaves an unquoted multibyte value unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(strip_quotes("em—dash")).to_equal("em—dash")
```

</details>

### parse_sdn_table with multibyte UTF-8 quoted title

#### loads a table whose row has a multibyte quoted field

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "bugs |id, title, status|\n    b1, \"em—dash bug—title\", open\n    b2, plain, closed\n"
val parsed = parse_sdn_table(content)
expect(parsed.?).to_equal(true)
val tbl = parsed?
expect(tbl.rows.len()).to_equal(2)
val title = tbl.rows[0].get("title") ?? "NIL"
expect(title).to_equal("em—dash bug—title")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/sdn_reader_utf8_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- split_sdn_row with multibyte UTF-8
- strip_quotes with multibyte UTF-8
- parse_sdn_table with multibyte UTF-8 quoted title

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
