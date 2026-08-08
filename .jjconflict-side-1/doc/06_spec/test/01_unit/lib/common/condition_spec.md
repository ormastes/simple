# Condition Specification

> <details>

<!-- sdn-diagram:id=condition_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=condition_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

condition_spec
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
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Condition Specification

## Scenarios

### Condition

#### keeps the sync facade wired to condition evaluation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = condition_facade_source()

expect(source).to_contain("export use std.gc_async_mut.spec.condition.*")
```

</details>

#### keeps skip condition dimensions available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = condition_source()

expect(source).to_contain("struct SkipCondition:")
expect(source).to_contain("platforms: [text]")
expect(source).to_contain("runtimes: [text]")
expect(source).to_contain("architectures: [text]")
expect(source).to_contain("env_vars: {text: text}")
```

</details>

#### keeps matcher functions for environment-based skip logic

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = condition_source()

expect(source).to_contain("fn matches_platforms(platforms: [text]) -> bool")
expect(source).to_contain("fn matches_runtimes(runtimes: [text]) -> bool")
expect(source).to_contain("fn matches_architectures(architectures: [text]) -> bool")
expect(source).to_contain("fn matches_network(network: bool) -> bool")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/condition_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Condition

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
