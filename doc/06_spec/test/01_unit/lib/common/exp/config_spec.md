# Config Specification

> <details>

<!-- sdn-diagram:id=config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

config_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Config Specification

## Scenarios

### ConfigValue

#### keeps common config value and loader APIs available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = exp_source("config")

expect(source).to_contain("enum ConfigValue")
expect(source).to_contain("struct ExpConfig")
expect(source).to_contain("static fn empty() -> ExpConfig")
expect(source).to_contain("pub fn load_exp_config")
expect(source).to_contain("pub fn parse_cli_overrides")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/exp/config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ConfigValue

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
