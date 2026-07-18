# Condition Specification

> <details>

<!-- sdn-diagram:id=condition_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=condition_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

condition_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=condition_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Condition Specification

## Scenarios

### Condition

#### keeps skip-condition data model and matcher entrypoint available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_sync_mut/spec/condition.spl")

expect(source).to_contain("struct SkipCondition")
expect(source).to_contain("platforms: [text]")
expect(source).to_contain("runtimes: [text]")
expect(source).to_contain("fn matches() -> bool")
```

</details>

#### keeps platform runtime and environment matchers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_sync_mut/spec/condition.spl")

expect(source).to_contain("fn matches_platforms(platforms: [text]) -> bool")
expect(source).to_contain("fn matches_runtimes(runtimes: [text]) -> bool")
expect(source).to_contain("fn matches_env_vars")
expect(source).to_contain("fn matches_network")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/condition_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Condition

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
