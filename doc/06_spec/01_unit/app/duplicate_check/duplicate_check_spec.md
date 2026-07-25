# Duplicate Check Specification

> <details>

<!-- sdn-diagram:id=duplicate_check_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=duplicate_check_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

duplicate_check_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=duplicate_check_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Duplicate Check Specification

## Scenarios

### duplicate_check command argument parsing

#### strips runtime prefixes and duplicate-check command

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = [
    "bin/simple",
    "run",
    "src/compiler/90.tools/duplicate_check/main.spl",
    "duplicate-check",
    "/tmp/dup_scope",
    "--format",
    "json"
]

val cmd_args = collect_command_args(args)

expect(cmd_args.len()).to_equal(3)
expect(cmd_args[0]).to_equal("/tmp/dup_scope")
expect(cmd_args[1]).to_equal("--format")
expect(cmd_args[2]).to_equal("json")
```

</details>

#### defaults to semantic analysis and parses semantic flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = parse_args([
    "/tmp/dup_scope",
    "--semantic-threshold=0.93",
    "--semantic-model",
    "nomic-embed-text",
    "--format=json"
])

expect(config.use_semantic).to_equal(true)
expect(config.semantic_threshold > 0.92).to_equal(true)
expect(config.semantic_threshold < 0.94).to_equal(true)
expect(config.semantic_model).to_equal("nomic-embed-text")
expect(config.output_format).to_equal("json")
```

</details>

#### parses token mode and lexical thresholds

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = parse_args([
    "/tmp/dup_scope",
    "--mode",
    "token",
    "--min-tokens",
    "30",
    "--min-lines=5",
    "--cache-path=/tmp/duplicate-check-cache.sdn",
    "--jobs",
    "4"
])

expect(analysis_mode(config)).to_equal("token")
expect(config.use_cosine_similarity).to_equal(false)
expect(config.min_lines).to_equal(5)
expect(config.min_tokens).to_equal(30)
expect(config.incremental_cache_path).to_equal("/tmp/duplicate-check-cache.sdn")
expect(config.num_workers).to_equal(4)
```

</details>

#### parses cosine mode and fuzzy threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = parse_args([
    "/tmp/dup_scope",
    "--mode=cosine",
    "--similarity-threshold",
    "0.61"
])

expect(analysis_mode(config)).to_equal("cosine")
expect(config.use_cosine_similarity).to_equal(true)
expect(config.similarity_threshold > 0.60).to_equal(true)
expect(config.similarity_threshold < 0.62).to_equal(true)
```

</details>

### duplicate_check formatter shared helpers

#### summarizes duplicate groups with unique file counting

1. sample block
2. sample block
3. sample block
4. sample block
   - Expected: summary.total_groups equals `2`
   - Expected: summary.total_occurrences equals `4`
   - Expected: summary.total_lines equals `12`
   - Expected: summary.files_affected equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val groups = [
    DuplicateGroup(
        blocks: [
            sample_block("/tmp/a.spl", 1, 3, 10, "fn shared_a():\n    return 1"),
            sample_block("/tmp/b.spl", 4, 6, 10, "fn shared_b():\n    return 1")
        ],
        occurrences: 2,
        total_lines: 6,
        impact_score: 12
    ),
    DuplicateGroup(
        blocks: [
            sample_block("/tmp/b.spl", 10, 12, 21, "fn extra_b():\n    return 2"),
            sample_block("/tmp/c.spl", 14, 16, 21, "fn extra_c():\n    return 2")
        ],
        occurrences: 2,
        total_lines: 6,
        impact_score: 12
    )
]

val summary = summarize_duplicate_groups(groups)

expect(summary.total_groups).to_equal(2)
expect(summary.total_occurrences).to_equal(4)
expect(summary.total_lines).to_equal(12)
expect(summary.files_affected).to_equal(3)
```

</details>

#### formats shared ratios and scores consistently

1. blocks: [sample block
   - Expected: format_score_hundredths(0.9) equals `0.90`
   - Expected: format_score_hundredths(0.97) equals `0.97`
   - Expected: format_ratio_tenths(2, 3) equals `66.6`
   - Expected: format_ratio_tenths(0, 0) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(duplicate_lines_per_block(DuplicateGroup(
    blocks: [sample_block("/tmp/a.spl", 1, 3, 10, "fn one():\n    return 1")],
    occurrences: 0,
    total_lines: 5,
    impact_score: 5
))).to_equal(0)
expect(format_score_hundredths(0.9)).to_equal("0.90")
expect(format_score_hundredths(0.97)).to_equal("0.97")
expect(format_ratio_tenths(2, 3)).to_equal("66.6")
expect(format_ratio_tenths(0, 0)).to_equal("0.0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/duplicate_check/duplicate_check_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- duplicate_check command argument parsing
- duplicate_check formatter shared helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
