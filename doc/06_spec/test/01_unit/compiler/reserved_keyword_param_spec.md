# Reserved Keyword Param Specification

> <details>

<!-- sdn-diagram:id=reserved_keyword_param_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=reserved_keyword_param_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

reserved_keyword_param_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=reserved_keyword_param_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reserved Keyword Param Specification

## Scenarios

### reserved keyword param rejection

#### non-reserved param names work fine

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(auth("admin", "secret")).to_equal("secret")
```

</details>

#### buffer param works

1. var result: [u8] = write to
   - Expected: result.length() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d: [u8] = [0x01u8, 0x02u8]
var result: [u8] = write_to([], d)
expect(result.length()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/reserved_keyword_param_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- reserved keyword param rejection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
