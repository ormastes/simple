# Lib Common Lsp Specification

> <details>

<!-- sdn-diagram:id=lib_common_lsp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lib_common_lsp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lib_common_lsp_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lib_common_lsp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lib Common Lsp Specification

## Scenarios

### LSP System: lib/common

<details>
<summary>Advanced: hover: no crashes</summary>

#### hover: no crashes _(slow)_

1. report crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val crashes = batch_lsp("hover", files)
    report_crashes("hover", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

<details>
<summary>Advanced: definition: no crashes</summary>

#### definition: no crashes _(slow)_

1. report crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val crashes = batch_lsp("definition", files)
    report_crashes("definition", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

<details>
<summary>Advanced: references: no crashes</summary>

#### references: no crashes _(slow)_

1. report crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val crashes = batch_lsp("references", files)
    report_crashes("references", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

<details>
<summary>Advanced: completions: no crashes</summary>

#### completions: no crashes _(slow)_

1. report crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val crashes = batch_lsp("completions", files)
    report_crashes("completions", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

<details>
<summary>Advanced: semantic-tokens: no crashes</summary>

#### semantic-tokens: no crashes _(slow)_

1. report crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val crashes = batch_lsp_no_pos("semantic-tokens", files)
    report_crashes("semantic-tokens", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

<details>
<summary>Advanced: folding-range: no crashes</summary>

#### folding-range: no crashes _(slow)_

1. report crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val crashes = batch_lsp_no_pos("folding-range", files)
    report_crashes("folding-range", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

<details>
<summary>Advanced: document-highlight: no crashes</summary>

#### document-highlight: no crashes _(slow)_

1. report crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val crashes = batch_lsp("document-highlight", files)
    report_crashes("document-highlight", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

<details>
<summary>Advanced: type-definition: no crashes</summary>

#### type-definition: no crashes _(slow)_

1. report crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val crashes = batch_lsp("type-definition", files)
    report_crashes("type-definition", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | LSP |
| Status | Active |
| Source | `test/03_system/tools/lsp/lib_common_lsp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LSP System: lib/common

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 8 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
