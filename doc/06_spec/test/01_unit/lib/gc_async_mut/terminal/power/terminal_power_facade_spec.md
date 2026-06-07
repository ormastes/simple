# Terminal Power Facade Specification

> <details>

<!-- sdn-diagram:id=terminal_power_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=terminal_power_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

terminal_power_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=terminal_power_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Terminal Power Facade Specification

## Scenarios

### gc_async_mut terminal power facade

#### re-exports hosted-safe relay and host backend entry points

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val relay = make_power_config_relay("relay", "", "", "", "", "", "", "", "", "", "", "", "", "", "")
expect(relay_power_on(relay).state).to_equal(POWER_STATE_UNKNOWN)
val host = make_power_config_host("host", "", 22, "user", "none", "", "", "")
expect(host_power_on(host).state).to_equal(POWER_STATE_UNKNOWN)
expect(send_wol_packet("not-a-mac")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/terminal/power/terminal_power_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut terminal power facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
