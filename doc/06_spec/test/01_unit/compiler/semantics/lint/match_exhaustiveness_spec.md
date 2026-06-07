# Match Exhaustiveness Specification

> <details>

<!-- sdn-diagram:id=match_exhaustiveness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=match_exhaustiveness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

match_exhaustiveness_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=match_exhaustiveness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Match Exhaustiveness Specification

## Scenarios

### Match Exhaustiveness Lint

#### exhaustive matches

#### does not flag match with wildcard arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn classify(x: i64) -> text:\n    match x:\n        case 1: \"one\"\n        case 2: \"two\"\n        case _: \"other\"\n"
val codes = check_match_exhaustiveness_text(code)
val has_warning = codes_contain(codes, "MEXH002")
expect(has_warning).to_equal(false)
```

</details>

#### does not flag match with default catch-all

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test(x: i64) -> text:\n    match x:\n        case 0: \"zero\"\n        case _: \"nonzero\"\n"
val codes = check_match_exhaustiveness_text(code)
val has_warning = codes_contain(codes, "MEXH002")
expect(has_warning).to_equal(false)
```

</details>

#### non-exhaustive matches

#### flags match without wildcard or default case

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test(x: i64) -> text:\n    match x:\n        case 1: \"one\"\n        case 2: \"two\"\n"
val codes = check_match_exhaustiveness_text(code)
val has_warning = codes_contain(codes, "MEXH002")
expect(has_warning).to_equal(true)
```

</details>

#### flags match with only one case and no default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test(x: i64) -> text:\n    match x:\n        case 42: \"the answer\"\n"
val codes = check_match_exhaustiveness_text(code)
val has_warning = codes_contain(codes, "MEXH002")
expect(has_warning).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/match_exhaustiveness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Match Exhaustiveness Lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
