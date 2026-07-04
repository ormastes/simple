# Semantic Fallback Probe Specification

> <details>

<!-- sdn-diagram:id=semantic_fallback_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=semantic_fallback_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

semantic_fallback_probe_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=semantic_fallback_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semantic Fallback Probe Specification

## Scenarios

### semantic fallback probe

#### uses text fallback over duplicated doc comments

- signature: "fn add score
- signature: "fn merge score
   - Expected: report.used_fallback is true
   - Expected: report.items_with_docs equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = [
    DocEntry(
        file_path: "/tmp/semantic_probe_a.spl",
        line_number: 2,
        item_name: "add_score",
        item_kind: "fn",
        signature: "fn add_score(seed: i64) -> i64",
        doc_comment: "Adds a normalized value for downstream scoring.",
        has_doc: true
    ),
    DocEntry(
        file_path: "/tmp/semantic_probe_b.spl",
        line_number: 2,
        item_name: "merge_score",
        item_kind: "fn",
        signature: "fn merge_score(seed: i64) -> i64",
        doc_comment: "Adds a normalized value for downstream scoring.",
        has_doc: true
    )
]

val report = run_text_fallback(entries, 0.70, 0.40)

expect(report.used_fallback).to_equal(true)
expect(report.matches.len()).to_be_greater_than(0)
expect(report.items_with_docs).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/duplicate_check/semantic_fallback_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- semantic fallback probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
