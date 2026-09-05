# Frontend Collection Desugar Start Specification

> <details>

<!-- sdn-diagram:id=frontend_collection_desugar_start_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=frontend_collection_desugar_start_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

frontend_collection_desugar_start_spec -> compiler
frontend_collection_desugar_start_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=frontend_collection_desugar_start_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Frontend Collection Desugar Start Specification

## Scenarios

### frontend collection desugar start index

#### keeps parse_full_frontend domain-block receiver mutable

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/compiler/10.frontend/frontend.spl")

expect(source.contains("val module = parse_and_build_module")).to_equal(false)
expect(source).to_contain("var module = parse_and_build_module")
expect(source).to_contain("module.domain_blocks = domain_blocks")
```

</details>

#### desugars collection patterns after a larger previous parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = frontend_desugar_start_logger()
val large = parse_full_frontend(frontend_desugar_large_source(), "large_frontend_desugar.spl", "large_frontend_desugar", log)
expect(large.functions.contains("filler_11")).to_equal(true)

val small_source = "fn append_one() -> [i64]:\n    var xs = [1]\n    xs = xs + [2]\n    xs\n"
val small = parse_full_frontend(small_source, "small_frontend_desugar.spl", "small_frontend_desugar", log)

expect(small.functions.contains("append_one")).to_equal(true)
expect(collection_desugar_rewrite_count()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/frontend_collection_desugar_start_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- frontend collection desugar start index

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
