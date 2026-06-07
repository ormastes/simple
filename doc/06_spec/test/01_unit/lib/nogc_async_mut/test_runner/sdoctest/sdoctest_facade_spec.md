# Sdoctest Facade Specification

> <details>

<!-- sdn-diagram:id=sdoctest_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sdoctest_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sdoctest_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sdoctest_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdoctest Facade Specification

## Scenarios

### nogc_async_mut sdoctest facade

#### re-exports config parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_sdoctest_config()
expect(config.default_timeout).to_equal(5000)
expect(config.environments[0].name).to_equal("default")

val parsed = parse_config_from_text("sdoctest:\n  version: 1\n  default_timeout: 9000\nenvironments:\n  ci:\n    timeout: 12000\n")
expect(parsed.default_timeout).to_equal(9000)
expect(parsed.environments[0].name).to_equal("ci")
expect(parsed.environments[0].timeout).to_equal(12000)
```

</details>

#### re-exports extraction and result helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_fence_line("```spl:skip,tag=fast")
expect(parsed.0).to_equal("spl")
expect(parsed.1.len() as i64).to_equal(2)

val block = SdoctestBlock(source_file: "README.md", line_number: 7, code: "1 + 1", language: "spl", modifiers: [SdoctestModifier.Skip])
expect(block.has_modifier_skip()).to_equal(true)
expect(block.has_modifier_should_fail()).to_equal(false)
expect(block_status_to_str(BlockStatus.Passed)).to_equal("passed")

val run = SdoctestRunResult(files: [], total: 1, passed: 1, failed: 0, skipped: 0, errors: 0, accepted: 0, duration_ms: 1)
expect(run.is_ok()).to_equal(true)
```

</details>

#### re-exports glob helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(glob_match_path("doc/guide/example.md", "doc/**/*.md")).to_equal(true)
expect(glob_match_path("src/main.spl", "doc/**/*.md")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/test_runner/sdoctest/sdoctest_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut sdoctest facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
