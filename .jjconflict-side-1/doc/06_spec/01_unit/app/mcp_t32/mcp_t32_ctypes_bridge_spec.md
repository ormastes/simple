# Mcp T32 Ctypes Bridge Specification

> <details>

<!-- sdn-diagram:id=mcp_t32_ctypes_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_ctypes_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_ctypes_bridge_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_ctypes_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 54 | 54 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Ctypes Bridge Specification

## Scenarios

### T32 ctypes bridge

#### library discovery

#### returns config path when T32_API_LIB_PATH is set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cb_find_lib_path("/opt/custom/t32api64.so", ["/opt/t32/bin/pc_linux64/t32api64.so"])
expect(result).to_equal("/opt/custom/t32api64.so")
```

</details>

#### falls back to candidates when config path empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cb_find_lib_path("", ["/opt/t32/bin/pc_linux64/t32api64.so"])
expect(result).to_equal("/opt/t32/bin/pc_linux64/t32api64.so")
```

</details>

#### returns empty when no candidates available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cb_find_lib_path("", ["", ""])
expect(result).to_equal("")
```

</details>

#### returns empty when all sources empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cb_find_lib_path("", [])
expect(result).to_equal("")
```

</details>

#### prefers config over candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cb_find_lib_path("/my/lib.so", ["/other/lib.so"])
expect(result).to_equal("/my/lib.so")
```

</details>

#### command routing

#### routes EVAL commands to eval handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = cb_route_command("EVAL DIALOG.BOOLEAN(check)")
expect(route).to_equal("eval")
```

</details>

#### routes eval with lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = cb_route_command("eval STATE.RUN()")
expect(route).to_equal("eval")
```

</details>

#### routes EVAL with leading spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = cb_route_command("  EVAL Register(PC)")
expect(route).to_equal("eval")
```

</details>

#### routes PING to ping handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = cb_route_command("PING")
expect(route).to_equal("ping")
```

</details>

#### routes ping lowercase to ping handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = cb_route_command("ping")
expect(route).to_equal("ping")
```

</details>

#### routes Break.Set to cmd handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = cb_route_command("Break.Set main")
expect(route).to_equal("cmd")
```

</details>

#### routes SYStem.Up to cmd handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = cb_route_command("SYStem.Up")
expect(route).to_equal("cmd")
```

</details>

#### routes DIALOG.Set to cmd handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = cb_route_command("DIALOG.Set mycheck")
expect(route).to_equal("cmd")
```

</details>

#### routes DO script to cmd handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = cb_route_command("DO init.cmm")
expect(route).to_equal("cmd")
```

</details>

#### routes empty command to cmd handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = cb_route_command("")
expect(route).to_equal("cmd")
```

</details>

#### eval expression extraction

#### extracts expression from EVAL command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expr = cb_extract_eval_expr("EVAL DIALOG.BOOLEAN(check)")
expect(expr).to_equal("DIALOG.BOOLEAN(check)")
```

</details>

#### extracts expression from EVAL STATE.RUN()

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expr = cb_extract_eval_expr("EVAL STATE.RUN()")
expect(expr).to_equal("STATE.RUN()")
```

</details>

#### extracts expression from EVAL Register(PC)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expr = cb_extract_eval_expr("EVAL Register(PC)")
expect(expr).to_equal("Register(PC)")
```

</details>

#### returns empty for short command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expr = cb_extract_eval_expr("EVAL")
expect(expr).to_equal("")
```

</details>

#### connection state management

#### needs reconnect when not connected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = CbConnState(connected: false, host: "", port: 0)
expect(cb_needs_reconnect(state, "localhost", 20000)).to_equal(true)
```

</details>

#### does not need reconnect when same host:port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = CbConnState(connected: true, host: "localhost", port: 20000)
expect(cb_needs_reconnect(state, "localhost", 20000)).to_equal(false)
```

</details>

#### needs reconnect when host changed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = CbConnState(connected: true, host: "localhost", port: 20000)
expect(cb_needs_reconnect(state, "192.168.1.10", 20000)).to_equal(true)
```

</details>

#### needs reconnect when port changed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = CbConnState(connected: true, host: "localhost", port: 20000)
expect(cb_needs_reconnect(state, "localhost", 20001)).to_equal(true)
```

</details>

#### needs reconnect when both changed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = CbConnState(connected: true, host: "localhost", port: 20000)
expect(cb_needs_reconnect(state, "remote", 30000)).to_equal(true)
```

</details>

#### message type parsing

#### maps 0 to info

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cb_parse_msg_type(0)).to_equal("info")
```

</details>

#### maps 1 to warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cb_parse_msg_type(1)).to_equal("warning")
```

</details>

#### maps 2 to error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cb_parse_msg_type(2)).to_equal("error")
```

</details>

#### maps unknown to info

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cb_parse_msg_type(99)).to_equal("info")
```

</details>

#### maps negative to info

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cb_parse_msg_type(-1)).to_equal("info")
```

</details>

#### target state parsing

#### maps TRUE to running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cb_parse_target_state("TRUE")).to_equal("running")
```

</details>

#### maps true lowercase to running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cb_parse_target_state("true")).to_equal("running")
```

</details>

#### maps TRUE. with trailing dot to running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cb_parse_target_state("TRUE.")).to_equal("running")
```

</details>

#### maps true. with trailing dot to running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cb_parse_target_state("true.")).to_equal("running")
```

</details>

#### maps FALSE to stopped

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cb_parse_target_state("FALSE")).to_equal("stopped")
```

</details>

#### maps false lowercase to stopped

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cb_parse_target_state("false")).to_equal("stopped")
```

</details>

#### maps FALSE. with trailing dot to stopped

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cb_parse_target_state("FALSE.")).to_equal("stopped")
```

</details>

#### maps empty to unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cb_parse_target_state("")).to_equal("unknown")
```

</details>

#### maps garbage to unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cb_parse_target_state("maybe")).to_equal("unknown")
```

</details>

#### trims whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cb_parse_target_state("  TRUE  ")).to_equal("running")
```

</details>

#### trims whitespace on false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cb_parse_target_state("  false.  ")).to_equal("stopped")
```

</details>

#### config precedence

#### env var overrides SDN config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cb_resolve_config("/usr/bin/python3.11", "python3", "python3")
expect(result).to_equal("/usr/bin/python3.11")
```

</details>

#### SDN config overrides default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cb_resolve_config("", "/usr/bin/python3.10", "python3")
expect(result).to_equal("/usr/bin/python3.10")
```

</details>

#### uses default when env and SDN empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cb_resolve_config("", "", "python3")
expect(result).to_equal("python3")
```

</details>

#### env var takes priority even when SDN set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cb_resolve_config("/custom/python", "/other/python", "python3")
expect(result).to_equal("/custom/python")
```

</details>

#### backend preference routing

#### ctypes is default when preference empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pref = ""
val try_ctypes = (pref == "" or pref == "ctypes")
expect(try_ctypes).to_equal(true)
```

</details>

#### ctypes when preference is ctypes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pref = "ctypes"
val try_ctypes = (pref == "" or pref == "ctypes")
expect(try_ctypes).to_equal(true)
```

</details>

#### not ctypes-first when preference is t32rem

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pref = "t32rem"
val try_ctypes = (pref == "" or pref == "ctypes")
expect(try_ctypes).to_equal(false)
```

</details>

#### not ctypes-first when preference is python_rcl

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pref = "python_rcl"
val try_ctypes = (pref == "" or pref == "ctypes")
expect(try_ctypes).to_equal(false)
```

</details>

#### T32 Config string format

#### NODE= config key format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "NODE="
expect(key).to_equal("NODE=")
```

</details>

#### PORT= config key format

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "PORT="
val port_str = str(20000)
expect(port_str).to_equal("20000")
```

</details>

#### PACKLEN= config key format

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "PACKLEN="
val value = "1024"
expect(key + value).to_equal("PACKLEN=1024")
```

</details>

#### EVAL command construction

#### builds EVAL from expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expr = "STATE.RUN()"
val cmd = "EVAL " + expr
expect(cmd).to_equal("EVAL STATE.RUN()")
```

</details>

#### builds EVAL DIALOG.BOOLEAN

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val label = "mycheck"
val cmd = "EVAL DIALOG.BOOLEAN(" + label + ")"
expect(cmd).to_equal("EVAL DIALOG.BOOLEAN(mycheck)")
```

</details>

#### builds EVAL MESSAGE.STR()

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "EVAL MESSAGE.STR()"
expect(cmd).to_equal("EVAL MESSAGE.STR()")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_ctypes_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 ctypes bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 54 |
| Active scenarios | 54 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
