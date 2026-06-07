# Terminal Types Facade Specification

> <details>

<!-- sdn-diagram:id=terminal_types_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=terminal_types_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

terminal_types_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=terminal_types_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Terminal Types Facade Specification

## Scenarios

### nogc_async_mut terminal types facade

#### re-exports terminal configuration and result helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(term_kind_name(TERM_KIND_SSH)).to_equal("ssh")
expect(term_kind_name(TERM_KIND_TELNET)).to_equal("telnet")
expect(power_state_name(POWER_STATE_ON)).to_equal("on")

val ssh = make_ssh_config("host", "127.0.0.1", 22, "user", "password", "secret")
expect(ssh.kind).to_equal(TERM_KIND_SSH)
expect(ssh.username).to_equal("user")
val telnet = make_telnet_config("console", "127.0.0.1", 23)
expect(telnet.kind).to_equal(TERM_KIND_TELNET)

val power = make_power_config_t32("probe", "localhost", 20000)
expect(power.kind).to_equal("t32")
expect(make_power_state(POWER_STATE_ON, 42).label).to_equal("on")

val conn = make_terminal_connection(7, ssh)
expect(conn.connected).to_equal(false)
expect(make_exec_result(0, "ok", "", 5).stdout).to_equal("ok")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/terminal/terminal_types_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut terminal types facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
