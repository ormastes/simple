# Mcp T32 Dialog Parse Specification

> <details>

<!-- sdn-diagram:id=mcp_t32_dialog_parse_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_dialog_parse_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_dialog_parse_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_dialog_parse_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Dialog Parse Specification

## Scenarios

### T32 Dialog Parse

#### single dialog block

#### extracts multiple dialog elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(sample_dialog_cmm())
expect(elements.len()).to_be_greater_than(5)
```

</details>

#### finds header element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(sample_dialog_cmm())
expect(dp_has_type(elements, "header")).to_equal(true)
```

</details>

#### finds labeled edit widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(sample_dialog_cmm())
expect(dp_has_label(elements, "myname")).to_equal(true)
```

</details>

#### finds labeled checkbox widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(sample_dialog_cmm())
expect(dp_has_label(elements, "mycheck")).to_equal(true)
```

</details>

#### finds labeled choosebox widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(sample_dialog_cmm())
expect(dp_has_label(elements, "mychoose")).to_equal(true)
```

</details>

#### finds labeled defbutton widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(sample_dialog_cmm())
expect(dp_has_label(elements, "ok_btn")).to_equal(true)
```

</details>

#### finds labeled button widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(sample_dialog_cmm())
expect(dp_has_label(elements, "cancel_btn")).to_equal(true)
```

</details>

#### finds labeled pulldown widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(sample_dialog_cmm())
expect(dp_has_label(elements, "mypull")).to_equal(true)
```

</details>

#### finds line element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(sample_dialog_cmm())
expect(dp_has_type(elements, "line")).to_equal(true)
```

</details>

#### finds close element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(sample_dialog_cmm())
expect(dp_has_type(elements, "close")).to_equal(true)
```

</details>

#### finds pos element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(sample_dialog_cmm())
expect(dp_has_type(elements, "pos")).to_equal(true)
```

</details>

#### finds text element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(sample_dialog_cmm())
expect(dp_has_type(elements, "text")).to_equal(true)
```

</details>

#### label extraction

#### collects all labeled widgets

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(sample_dialog_cmm())
val labels = dp_extract_labels(elements)
expect(labels.len()).to_equal(6)
```

</details>

#### contains myname label

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(sample_dialog_cmm())
val labels = dp_extract_labels(elements)
expect(labels).to_contain("myname")
```

</details>

#### contains ok_btn label

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(sample_dialog_cmm())
val labels = dp_extract_labels(elements)
expect(labels).to_contain("ok_btn")
```

</details>

#### generated labels

#### generates labels for unlabeled buttons

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements("DIALOG\n(\n  BUTTON \"Run\" \"gosub run\"\n)")
expect(elements[0].generated_label).to_equal(true)
```

</details>

#### parses unlabeled choosebox widgets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements("DIALOG\n(\n  CHOOSEBOX \"Run\" \"\"\n)")
expect(elements[0].element_type).to_equal("choosebox")
```

</details>

#### no dialog blocks

#### returns empty elements for non-dialog CMM

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(empty_cmm())
expect(elements.len()).to_equal(0)
```

</details>

#### returns empty labels for non-dialog CMM

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(empty_cmm())
val labels = dp_extract_labels(elements)
expect(labels.len()).to_equal(0)
```

</details>

#### counts zero dialog blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = dp_count_blocks(empty_cmm())
expect(count).to_equal(0)
```

</details>

#### multiple dialog blocks

#### extracts elements from both dialogs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(multi_dialog_cmm())
expect(elements.len()).to_equal(2)
```

</details>

#### collects labels from both dialogs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements(multi_dialog_cmm())
val labels = dp_extract_labels(elements)
expect(labels).to_contain("name1")
expect(labels).to_contain("name2")
```

</details>

#### empty source

#### returns empty elements for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = dp_extract_elements("")
expect(elements.len()).to_equal(0)
```

</details>

#### dialog block count

#### counts one for single dialog

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = dp_count_blocks(sample_dialog_cmm())
expect(count).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_dialog_parse_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Dialog Parse

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
