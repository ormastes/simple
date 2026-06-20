# Md Diagram Update Scanner Specification

> <details>

<!-- sdn-diagram:id=md_diagram_update_scanner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_diagram_update_scanner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_diagram_update_scanner_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_diagram_update_scanner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Diagram Update Scanner Specification

## Scenarios

### md-diagram-update scanner

#### extracts normal diagram marker ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normal = scan_diagram_regions(_region("doc.arch"))
expect(normal.len()).to_equal(1)
expect(normal[0].id).to_equal("doc.arch")
```

</details>

#### extracts marker ids without a space before comment close

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_space_close = scan_diagram_regions(_region_no_space_close("doc.arch"))
expect(no_space_close.len()).to_equal(1)
expect(no_space_close[0].id).to_equal("doc.arch")
```

</details>

#### ignores blank diagram marker ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blank = scan_diagram_regions(_region(""))
expect(blank.len()).to_equal(0)
```

</details>

#### ignores whitespace diagram marker ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val whitespace = scan_diagram_regions(_region("doc arch"))
expect(whitespace.len()).to_equal(0)
```

</details>

#### ignores diagram marker ids without a comment close

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_close = scan_diagram_regions(["<!-- sdn-diagram:id=doc.arch", "```sdn", "A: A", "```", "<!-- sdn-diagram:end -->"].join("\n"))
expect(missing_close.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/md_diagram_update_scanner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- md-diagram-update scanner

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
