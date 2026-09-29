# Mcp T32 Ctypes Bridge Specification

> Tests covering T32 ctypes bridge.

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

- returns config path when T32_API_LIB_PATH is set
   - Expected: result equals `/opt/custom/t32api64.so`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns config path when T32_API_LIB_PATH is set")
val result = cb_find_lib_path("/opt/custom/t32api64.so", ["/opt/t32/bin/pc_linux64/t32api64.so"])
expect(result).to_equal("/opt/custom/t32api64.so")
```

</details>

#### falls back to candidates when config path empty

- falls back to candidates when config path empty
   - Expected: result equals `/opt/t32/bin/pc_linux64/t32api64.so`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to candidates when config path empty")
val result = cb_find_lib_path("", ["/opt/t32/bin/pc_linux64/t32api64.so"])
expect(result).to_equal("/opt/t32/bin/pc_linux64/t32api64.so")
```

</details>

#### returns empty when no candidates available

- returns empty when no candidates available
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty when no candidates available")
val result = cb_find_lib_path("", ["", ""])
expect(result).to_equal("")
```

</details>

#### returns empty when all sources empty

- returns empty when all sources empty
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty when all sources empty")
val result = cb_find_lib_path("", [])
expect(result).to_equal("")
```

</details>

#### prefers config over candidates

- prefers config over candidates
   - Expected: result equals `/my/lib.so`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefers config over candidates")
val result = cb_find_lib_path("/my/lib.so", ["/other/lib.so"])
expect(result).to_equal("/my/lib.so")
```

</details>

#### command routing

#### routes EVAL commands to eval handler

- routes EVAL commands to eval handler
   - Expected: route equals `eval`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes EVAL commands to eval handler")
val route = cb_route_command("EVAL DIALOG.BOOLEAN(check)")
expect(route).to_equal("eval")
```

</details>

#### routes eval with lowercase

- routes eval with lowercase
   - Expected: route equals `eval`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes eval with lowercase")
val route = cb_route_command("eval STATE.RUN()")
expect(route).to_equal("eval")
```

</details>

#### routes EVAL with leading spaces

- routes EVAL with leading spaces
   - Expected: route equals `eval`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes EVAL with leading spaces")
val route = cb_route_command("  EVAL Register(PC)")
expect(route).to_equal("eval")
```

</details>

#### routes PING to ping handler

- routes PING to ping handler
   - Expected: route equals `ping`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes PING to ping handler")
val route = cb_route_command("PING")
expect(route).to_equal("ping")
```

</details>

#### routes ping lowercase to ping handler

- routes ping lowercase to ping handler
   - Expected: route equals `ping`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes ping lowercase to ping handler")
val route = cb_route_command("ping")
expect(route).to_equal("ping")
```

</details>

#### routes Break.Set to cmd handler

- routes Break.Set to cmd handler
   - Expected: route equals `cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes Break.Set to cmd handler")
val route = cb_route_command("Break.Set main")
expect(route).to_equal("cmd")
```

</details>

#### routes SYStem.Up to cmd handler

- routes SYStem.Up to cmd handler
   - Expected: route equals `cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes SYStem.Up to cmd handler")
val route = cb_route_command("SYStem.Up")
expect(route).to_equal("cmd")
```

</details>

#### routes DIALOG.Set to cmd handler

- routes DIALOG.Set to cmd handler
   - Expected: route equals `cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes DIALOG.Set to cmd handler")
val route = cb_route_command("DIALOG.Set mycheck")
expect(route).to_equal("cmd")
```

</details>

#### routes DO script to cmd handler

- routes DO script to cmd handler
   - Expected: route equals `cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes DO script to cmd handler")
val route = cb_route_command("DO init.cmm")
expect(route).to_equal("cmd")
```

</details>

#### routes empty command to cmd handler

- routes empty command to cmd handler
   - Expected: route equals `cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes empty command to cmd handler")
val route = cb_route_command("")
expect(route).to_equal("cmd")
```

</details>

#### eval expression extraction

#### extracts expression from EVAL command

- extracts expression from EVAL command
   - Expected: expr equals `DIALOG.BOOLEAN(check)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts expression from EVAL command")
val expr = cb_extract_eval_expr("EVAL DIALOG.BOOLEAN(check)")
expect(expr).to_equal("DIALOG.BOOLEAN(check)")
```

</details>

#### extracts expression from EVAL STATE.RUN()

- extracts expression from EVAL STATE.RUN()
   - Expected: expr equals `STATE.RUN()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts expression from EVAL STATE.RUN()")
val expr = cb_extract_eval_expr("EVAL STATE.RUN()")
expect(expr).to_equal("STATE.RUN()")
```

</details>

#### extracts expression from EVAL Register(PC)

- extracts expression from EVAL Register(PC)
   - Expected: expr equals `Register(PC)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts expression from EVAL Register(PC)")
val expr = cb_extract_eval_expr("EVAL Register(PC)")
expect(expr).to_equal("Register(PC)")
```

</details>

#### returns empty for short command

- returns empty for short command
   - Expected: expr equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for short command")
val expr = cb_extract_eval_expr("EVAL")
expect(expr).to_equal("")
```

</details>

#### connection state management

#### needs reconnect when not connected

- needs reconnect when not connected
   - Expected: cb_needs_reconnect(state, "localhost", 20000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("needs reconnect when not connected")
val state = CbConnState(connected: false, host: "", port: 0)
expect(cb_needs_reconnect(state, "localhost", 20000)).to_equal(true)
```

</details>

#### does not need reconnect when same host:port

- does not need reconnect when same host:port
   - Expected: cb_needs_reconnect(state, "localhost", 20000) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not need reconnect when same host:port")
val state = CbConnState(connected: true, host: "localhost", port: 20000)
expect(cb_needs_reconnect(state, "localhost", 20000)).to_equal(false)
```

</details>

#### needs reconnect when host changed

- needs reconnect when host changed
   - Expected: cb_needs_reconnect(state, "192.168.1.10", 20000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("needs reconnect when host changed")
val state = CbConnState(connected: true, host: "localhost", port: 20000)
expect(cb_needs_reconnect(state, "192.168.1.10", 20000)).to_equal(true)
```

</details>

#### needs reconnect when port changed

- needs reconnect when port changed
   - Expected: cb_needs_reconnect(state, "localhost", 20001) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("needs reconnect when port changed")
val state = CbConnState(connected: true, host: "localhost", port: 20000)
expect(cb_needs_reconnect(state, "localhost", 20001)).to_equal(true)
```

</details>

#### needs reconnect when both changed

- needs reconnect when both changed
   - Expected: cb_needs_reconnect(state, "remote", 30000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("needs reconnect when both changed")
val state = CbConnState(connected: true, host: "localhost", port: 20000)
expect(cb_needs_reconnect(state, "remote", 30000)).to_equal(true)
```

</details>

#### message type parsing

#### maps 0 to info

- maps 0 to info
   - Expected: cb_parse_msg_type(0) equals `info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps 0 to info")
expect(cb_parse_msg_type(0)).to_equal("info")
```

</details>

#### maps 1 to warning

- maps 1 to warning
   - Expected: cb_parse_msg_type(1) equals `warning`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps 1 to warning")
expect(cb_parse_msg_type(1)).to_equal("warning")
```

</details>

#### maps 2 to error

- maps 2 to error
   - Expected: cb_parse_msg_type(2) equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps 2 to error")
expect(cb_parse_msg_type(2)).to_equal("error")
```

</details>

#### maps unknown to info

- maps unknown to info
   - Expected: cb_parse_msg_type(99) equals `info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps unknown to info")
expect(cb_parse_msg_type(99)).to_equal("info")
```

</details>

#### maps negative to info

- maps negative to info
   - Expected: cb_parse_msg_type(-1) equals `info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps negative to info")
expect(cb_parse_msg_type(-1)).to_equal("info")
```

</details>

#### target state parsing

#### maps TRUE to running

- maps TRUE to running
   - Expected: cb_parse_target_state("TRUE") equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps TRUE to running")
expect(cb_parse_target_state("TRUE")).to_equal("running")
```

</details>

#### maps true lowercase to running

- maps true lowercase to running
   - Expected: cb_parse_target_state("true") equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps true lowercase to running")
expect(cb_parse_target_state("true")).to_equal("running")
```

</details>

#### maps TRUE. with trailing dot to running

- maps TRUE. with trailing dot to running
   - Expected: cb_parse_target_state("TRUE.") equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps TRUE. with trailing dot to running")
expect(cb_parse_target_state("TRUE.")).to_equal("running")
```

</details>

#### maps true. with trailing dot to running

- maps true. with trailing dot to running
   - Expected: cb_parse_target_state("true.") equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps true. with trailing dot to running")
expect(cb_parse_target_state("true.")).to_equal("running")
```

</details>

#### maps FALSE to stopped

- maps FALSE to stopped
   - Expected: cb_parse_target_state("FALSE") equals `stopped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps FALSE to stopped")
expect(cb_parse_target_state("FALSE")).to_equal("stopped")
```

</details>

#### maps false lowercase to stopped

- maps false lowercase to stopped
   - Expected: cb_parse_target_state("false") equals `stopped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps false lowercase to stopped")
expect(cb_parse_target_state("false")).to_equal("stopped")
```

</details>

#### maps FALSE. with trailing dot to stopped

- maps FALSE. with trailing dot to stopped
   - Expected: cb_parse_target_state("FALSE.") equals `stopped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps FALSE. with trailing dot to stopped")
expect(cb_parse_target_state("FALSE.")).to_equal("stopped")
```

</details>

#### maps empty to unknown

- maps empty to unknown
   - Expected: cb_parse_target_state("") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps empty to unknown")
expect(cb_parse_target_state("")).to_equal("unknown")
```

</details>

#### maps garbage to unknown

- maps garbage to unknown
   - Expected: cb_parse_target_state("maybe") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps garbage to unknown")
expect(cb_parse_target_state("maybe")).to_equal("unknown")
```

</details>

#### trims whitespace

- trims whitespace
   - Expected: cb_parse_target_state("  TRUE  ") equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims whitespace")
expect(cb_parse_target_state("  TRUE  ")).to_equal("running")
```

</details>

#### trims whitespace on false

- trims whitespace on false
   - Expected: cb_parse_target_state("  false.  ") equals `stopped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims whitespace on false")
expect(cb_parse_target_state("  false.  ")).to_equal("stopped")
```

</details>

#### config precedence

#### env var overrides SDN config

- env var overrides SDN config
   - Expected: result equals `/usr/bin/python3.11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env var overrides SDN config")
val result = cb_resolve_config("/usr/bin/python3.11", "python3", "python3")
expect(result).to_equal("/usr/bin/python3.11")
```

</details>

#### SDN config overrides default

- SDN config overrides default
   - Expected: result equals `/usr/bin/python3.10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SDN config overrides default")
val result = cb_resolve_config("", "/usr/bin/python3.10", "python3")
expect(result).to_equal("/usr/bin/python3.10")
```

</details>

#### uses default when env and SDN empty

- uses default when env and SDN empty
   - Expected: result equals `python3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses default when env and SDN empty")
val result = cb_resolve_config("", "", "python3")
expect(result).to_equal("python3")
```

</details>

#### env var takes priority even when SDN set

- env var takes priority even when SDN set
   - Expected: result equals `/custom/python`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env var takes priority even when SDN set")
val result = cb_resolve_config("/custom/python", "/other/python", "python3")
expect(result).to_equal("/custom/python")
```

</details>

#### backend preference routing

#### ctypes is default when preference empty

- ctypes is default when preference empty
   - Expected: try_ctypes is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ctypes is default when preference empty")
val pref = ""
val try_ctypes = (pref == "" or pref == "ctypes")
expect(try_ctypes).to_equal(true)
```

</details>

#### ctypes when preference is ctypes

- ctypes when preference is ctypes
   - Expected: try_ctypes is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ctypes when preference is ctypes")
val pref = "ctypes"
val try_ctypes = (pref == "" or pref == "ctypes")
expect(try_ctypes).to_equal(true)
```

</details>

#### not ctypes-first when preference is t32rem

- not ctypes-first when preference is t32rem
   - Expected: try_ctypes is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("not ctypes-first when preference is t32rem")
val pref = "t32rem"
val try_ctypes = (pref == "" or pref == "ctypes")
expect(try_ctypes).to_equal(false)
```

</details>

#### not ctypes-first when preference is python_rcl

- not ctypes-first when preference is python_rcl
   - Expected: try_ctypes is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("not ctypes-first when preference is python_rcl")
val pref = "python_rcl"
val try_ctypes = (pref == "" or pref == "ctypes")
expect(try_ctypes).to_equal(false)
```

</details>

#### T32 Config string format

#### NODE= config key format

- NODE= config key format
   - Expected: key equals `NODE=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NODE= config key format")
val key = "NODE="
expect(key).to_equal("NODE=")
```

</details>

#### PORT= config key format

- PORT= config key format
   - Expected: port_str equals `20000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PORT= config key format")
val key = "PORT="
val port_str = str(20000)
expect(port_str).to_equal("20000")
```

</details>

#### PACKLEN= config key format

- PACKLEN= config key format
   - Expected: key + value equals `PACKLEN=1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PACKLEN= config key format")
val key = "PACKLEN="
val value = "1024"
expect(key + value).to_equal("PACKLEN=1024")
```

</details>

#### EVAL command construction

#### builds EVAL from expression

- builds EVAL from expression
   - Expected: cmd equals `EVAL STATE.RUN()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds EVAL from expression")
val expr = "STATE.RUN()"
val cmd = "EVAL " + expr
expect(cmd).to_equal("EVAL STATE.RUN()")
```

</details>

#### builds EVAL DIALOG.BOOLEAN

- builds EVAL DIALOG.BOOLEAN
   - Expected: cmd equals `EVAL DIALOG.BOOLEAN(mycheck)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds EVAL DIALOG.BOOLEAN")
val label = "mycheck"
val cmd = "EVAL DIALOG.BOOLEAN(" + label + ")"
expect(cmd).to_equal("EVAL DIALOG.BOOLEAN(mycheck)")
```

</details>

#### builds EVAL MESSAGE.STR()

- builds EVAL MESSAGE.STR()
   - Expected: cmd equals `EVAL MESSAGE.STR()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds EVAL MESSAGE.STR()")
val cmd = "EVAL MESSAGE.STR()"
expect(cmd).to_equal("EVAL MESSAGE.STR()")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_t32/mcp_t32_ctypes_bridge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 ctypes bridge.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d3651e7370efa6510b5eb9f0b25061d51c7e2b1da2d9f6974abbc4a7208333c8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d3651e7370efa6510b5eb9f0b25061d51c7e2b1da2d9f6974abbc4a7208333c8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d3651e7370efa6510b5eb9f0b25061d51c7e2b1da2d9f6974abbc4a7208333c8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_t32/mcp_t32_ctypes_bridge_spec.spl
mirror: doc/06_spec/unit/app/mcp_t32/mcp_t32_ctypes_bridge_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_t32/mcp_t32_ctypes_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_t32/mcp_t32_ctypes_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_t32/mcp_t32_ctypes_bridge_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns config path when T32_API_LIB_PATH is set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_ctypes_bridge_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back to candidates when config path empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_ctypes_bridge_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty when no candidates available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
