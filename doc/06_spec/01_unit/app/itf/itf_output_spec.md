# Itf Output Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Itf Output Specification

## Scenarios

### format_size

#### shows byte counts under 1 KiB as-is

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_size(0)).to_equal("0 B")
expect(format_size(512)).to_equal("512 B")
expect(format_size(1023)).to_equal("1023 B")
```

</details>

#### formats KiB with one decimal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_size(1024)).to_equal("1.0 KiB")
expect(format_size(1536)).to_equal("1.5 KiB")
```

</details>

#### formats MiB with one decimal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_size(1048576)).to_equal("1.0 MiB")
expect(format_size(134217728)).to_equal("128.0 MiB")
```

</details>

#### formats GiB with one decimal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_size(1073741824)).to_equal("1.0 GiB")
```

</details>

#### formats TiB with one decimal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_size(1099511627776)).to_equal("1.0 TiB")
```

</details>

#### passes through a negative (unknown) size unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_size(-1)).to_equal("-1")
```

</details>

### _table_col_widths (dynamic-width table sizing)

#### seeds each column width from the header when rows are shorter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val widths = _table_col_widths(["NUMBER", "TITLE"], [["#1", "x"]])
expect(widths[0]).to_equal(6)
expect(widths[1]).to_equal(5)
```

</details>

#### grows a column width to fit the longest cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val widths = _table_col_widths(["NUMBER", "TITLE"], [["#1", "a very long title indeed"]])
expect(widths[0]).to_equal(6)
expect(widths[1]).to_equal(24)
```

</details>

#### takes the max across multiple rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val widths = _table_col_widths(["K"], [["short"], ["a much longer value"]])
expect(widths[0]).to_equal(19)
```

</details>

### _visible_len / _pad_visible (ANSI-aware table alignment)

#### counts an ANSI-colored word by its visible characters, not its byte length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val colored = "\u{001b}[32mOPEN\u{001b}[0m"
expect(_visible_len(colored)).to_equal(4)
```

</details>

#### matches plain-text length when there is no escape code

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_visible_len("CLOSED")).to_equal(6)
```

</details>

#### _table_col_widths measures colored cells by visible width, not byte length

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val colored_open = "\u{001b}[32mOPEN\u{001b}[0m"
val colored_closed = "\u{001b}[2mCLOSED\u{001b}[0m"
val widths = _table_col_widths(["STATE"], [[colored_open], [colored_closed]])
# Visible widths are 4 ("OPEN") and 6 ("CLOSED"); header "STATE" is 5.
# Max visible width must be 6 — not the byte-inflated 13/14 that
# `.len()` would have measured before this fix.
expect(widths[0]).to_equal(6)
```

</details>

#### _pad_visible pads a colored cell to the same visible width as a plain one

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val colored = "\u{001b}[32mOPEN\u{001b}[0m"
val padded_colored = _pad_visible(colored, 6)
val padded_plain = _pad_visible("AB", 6)
# Both should have 4 trailing spaces after their visible content —
# i.e. same total visible width once the escape codes are stripped.
expect(_visible_len(padded_colored)).to_equal(6)
expect(_visible_len(padded_plain)).to_equal(6)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/itf/itf_output_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- format_size
- _table_col_widths (dynamic-width table sizing)
- _visible_len / _pad_visible (ANSI-aware table alignment)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
