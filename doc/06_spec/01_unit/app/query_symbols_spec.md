# Query Symbols Specification

> <details>

<!-- sdn-diagram:id=query_symbols_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_symbols_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_symbols_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_symbols_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Symbols Specification

## Scenarios

### query symbols

#### returns 0 for valid file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = engine_document_symbols("src/app/lsp/lsp_json.spl")
expect(result).to_equal(0)
```

</details>

#### returns 0 for file with no symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = engine_document_symbols("/dev/null")
expect(result).to_equal(0)
```

</details>

#### returns 0 for lsp_handlers file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = engine_document_symbols("src/app/lsp/lsp_handlers.spl")
expect(result).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/query_symbols_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- query symbols

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
