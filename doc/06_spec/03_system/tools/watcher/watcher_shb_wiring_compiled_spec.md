# Watcher Shb Wiring Compiled Specification

> <details>

<!-- sdn-diagram:id=watcher_shb_wiring_compiled_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=watcher_shb_wiring_compiled_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

watcher_shb_wiring_compiled_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=watcher_shb_wiring_compiled_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Watcher Shb Wiring Compiled Specification

## Scenarios

### SHB Watcher Wiring portable smoke

#### records SHB generation contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("get_or_generate_shb").to_equal("get_or_generate_shb")
expect(".shb").to_equal(".shb")
```

</details>

#### records freshness contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("CACHE_FRESH").to_equal("CACHE_FRESH")
```

</details>

#### records change classifications

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val statuses = shb_cache_statuses()
expect(statuses).to_contain("new")
expect(statuses).to_contain("body_only")
expect(statuses).to_contain("interface")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Active |
| Source | `test/03_system/tools/watcher/watcher_shb_wiring_compiled_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SHB Watcher Wiring portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
