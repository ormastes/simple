# System Config Model Specification

> <details>

<!-- sdn-diagram:id=system_config_model_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=system_config_model_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

system_config_model_spec -> std
system_config_model_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=system_config_model_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# System Config Model Specification

## Scenarios

### system config model

#### defines the minimal system stack defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = default_system_config_profile()

expect(profile.font).to_equal("JetBrains Mono")
expect(profile.service_manager).to_equal("OpenRC")
expect(profile.bootloader).to_equal("Limine")
expect(profile.standard_library).to_equal("musl")
```

</details>

#### lists settings sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sections = system_config_sections()

expect(sections).to_contain("Appearance")
expect(sections).to_contain("Services")
expect(sections).to_contain("Boot")
```

</details>

#### updates and validates settings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val updated = system_config_update(default_system_config_profile(), "service_manager", "runit")

expect(updated.service_manager).to_equal("runit")
expect(system_config_validate(updated)).to_equal(true)
```

</details>

#### summarizes current settings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = system_config_summary(default_system_config_profile())

expect(summary).to_contain("boot=Limine")
expect(summary).to_contain("libc=musl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/desktop/system_config_model_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- system config model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
