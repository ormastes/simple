# Mcp Debug Session Bridge Specification

> 1. dap close session

<!-- sdn-diagram:id=mcp_debug_session_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_debug_session_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_debug_session_bridge_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_debug_session_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Debug Session Bridge Specification

## Scenarios

### MCP debug session bridge

#### captures RTL remote_bitbang bootstrap metadata in session creation

1. dap close session


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = dap_create_session(
    "build/rtl.elf",
    "openocd",
    "openocd_remote_bitbang",
    "riscv32",
    "rtl_sim",
    "generic",
    "",
    "",
    "localhost",
    "3333",
    "",
    "",
    "127.0.0.1",
    "5555",
    "",
    "true"
)
expect(session.transport).to_equal("openocd_remote_bitbang")
expect(session.exec_mode).to_equal("rtl_sim")
expect(session.state).to_equal("bootstrap_ready")
expect(session.bootstrap_launch_command).to_contain("remote_bitbang")
expect(session.capabilities).to_contain("virtual_jtag")
dap_close_session(session.id)
```

</details>

#### captures Intel jtagd discovery metadata in session creation

1. dap close session


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = dap_create_session(
    "build/hw.elf",
    "intel_jtagd",
    "intel_jtagd",
    "riscv32",
    "hw",
    "intel",
    "",
    "",
    "localhost",
    "1309",
    "",
    "",
    "",
    "",
    "@1:10",
    "true"
)
expect(session.backend_id).to_equal("intel_jtagd")
expect(session.bootstrap_discovery_command).to_equal("jtagconfig --enum")
expect(session.bootstrap_attach_target).to_contain("@1:10")
expect(session.persistent_session).to_equal(true)
dap_close_session(session.id)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_debug_session_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP debug session bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
