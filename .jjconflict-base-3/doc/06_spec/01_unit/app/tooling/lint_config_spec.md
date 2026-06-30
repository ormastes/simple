# Lint Configuration Specification

> Configuration parsing for the lint framework. Supports enabling/disabling

<!-- sdn-diagram:id=lint_config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lint_config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lint_config_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lint_config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lint Configuration Specification

Configuration parsing for the lint framework. Supports enabling/disabling

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3140 |
| Category | Tooling |
| Status | In Progress |
| Source | `test/01_unit/app/tooling/lint_config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Configuration parsing for the lint framework. Supports enabling/disabling
specific lints, setting lint severity levels, and customizing lint behavior
through configuration files and CLI flags.

## Scenarios

### lint_config module compiles

#### basic sanity check

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
