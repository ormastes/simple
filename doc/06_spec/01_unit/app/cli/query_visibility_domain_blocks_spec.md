# Query Visibility Domain Blocks Specification

> <details>

<!-- sdn-diagram:id=query_visibility_domain_blocks_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_visibility_domain_blocks_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_visibility_domain_blocks_spec -> std
query_visibility_domain_blocks_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_visibility_domain_blocks_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Visibility Domain Blocks Specification

## Scenarios

### query visibility domain blocks

#### exposes top-level domain blocks as LSP document symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = parse_symbols_in_file(DOMAIN_FIXTURE)

expect(symbols.len()).to_equal(3)
expect(symbols[0].name).to_equal("schema" + "{}")
expect(symbols[0].kind).to_equal("domain")
expect(symbol_kind_number(symbols[0].kind)).to_equal(2)
expect(symbols[0].start_col).to_equal(0)
expect(symbols[0].end_col).to_equal(6)
expect(symbol_range_json(symbols[0])).to_equal("{\"start\":{\"line\":0,\"character\":0},\"end\":{\"line\":0,\"character\":6}}")
expect(symbols[1].name).to_equal("style" + "{}")
expect(symbols[1].kind).to_equal("domain")
expect(symbols[1].start_col).to_equal(0)
expect(symbols[1].end_col).to_equal(5)
expect(symbols[2].name).to_equal("schema")
expect(symbols[2].kind).to_equal("var")
expect(symbols[2].start_col).to_equal(4)
expect(symbols[2].end_col).to_equal(10)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/query_visibility_domain_blocks_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- query visibility domain blocks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
