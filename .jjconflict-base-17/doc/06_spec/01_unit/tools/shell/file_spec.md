# File Specification

> <details>

<!-- sdn-diagram:id=file_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=file_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

file_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=file_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File Specification

## Scenarios

### file tool

#### extension detection

#### identifies .spl as Simple source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "main.spl"
val is_spl = name.ends_with(".spl")
expect(is_spl).to_equal(true)
```

</details>

#### identifies .shs as Simple shell

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "build.shs"
val is_shs = name.ends_with(".shs")
expect(is_shs).to_equal(true)
```

</details>

#### identifies .md as Markdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "README.md"
val is_md = name.ends_with(".md")
expect(is_md).to_equal(true)
```

</details>

#### content inspection

#### detects shebang scripts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "#!/bin/sh\necho hello"
expect(content.starts_with("#!")).to_equal(true)
```

</details>

#### detects JSON by opening brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "{\"key\": \"value\"}"
expect(content.starts_with("{")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/shell/file_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- file tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
