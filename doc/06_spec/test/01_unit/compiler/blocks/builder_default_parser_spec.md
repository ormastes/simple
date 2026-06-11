# Builder Default Parser Specification

> <details>

<!-- sdn-diagram:id=builder_default_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=builder_default_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

builder_default_parser_spec -> std
builder_default_parser_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=builder_default_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Builder Default Parser Specification

## Scenarios

### BlockBuilder Default Parser

#### builder created without explicit parser

#### has a non-nil default parser

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = blockbuilder_new("test_block")
expect(builder._parser.?).to_equal(true)
```

</details>

#### default parser is callable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = blockbuilder_new("test_block")
val parser = builder._parser
expect(parser.?).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/blocks/builder_default_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BlockBuilder Default Parser

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
