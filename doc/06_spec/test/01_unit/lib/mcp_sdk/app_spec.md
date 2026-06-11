# App Specification

> <details>

<!-- sdn-diagram:id=app_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=app_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

app_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=app_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# App Specification

## Scenarios

### McpServer golden transcript (AC-1)

#### serves full 5-message transcript and writes exact expected responses

- mcp server reset
- mcp server init
- fn
- fn
- fn
- fn
- msgs push
- msgs push
- msgs push
- msgs push
- msgs push
- var transport = BufferTransport with messages
- mcp serve
   - Expected: sent_len equals `4`
   - Expected: has_server_name is true
   - Expected: has_server_version is true
   - Expected: has_server_info_key is true
   - Expected: has_protocol_version is true
   - Expected: has_capabilities is true
   - Expected: has_jsonrpc is true
   - Expected: has_adder is true
   - Expected: has_greeter is true
   - Expected: has_tools_key is true
   - Expected: has_content is true
   - Expected: has_result_value is true
   - Expected: has_result_key is true
   - Expected: has_error_key is true
   - Expected: has_error_code is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 72 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mcp_server_reset()

mcp_server_init("my-server", "1.2.3")
mcp_server_tool(
    "adder",
    "Adds two numbers",
    fn() -> text: "{\"type\":\"object\",\"properties\":{\"a\":{\"type\":\"number\"}}}",
    fn(args: text) -> text: "42"
)
mcp_server_tool(
    "greeter",
    "Greets someone",
    fn() -> text: "{\"type\":\"object\",\"properties\":{\"name\":{\"type\":\"string\"}}}",
    fn(args: text) -> text: "hello"
)

var msgs: [text] = []
msgs.push(make_initialize_msg())
msgs.push(make_initialized_notif())
msgs.push(make_tools_list_msg())
msgs.push(make_tools_call_msg("adder"))
msgs.push(make_unknown_msg())

var transport = BufferTransport.with_messages(msgs)

mcp_serve(transport)

val sent = transport.all_sent()

# notifications/initialized produces no response → 4 responses total
val sent_len = sent.length()
expect(sent_len).to_equal(4)

# --- Response 0: initialize ---
val init_resp = sent[0]
val has_server_name = init_resp.contains("\"my-server\"")
expect(has_server_name).to_equal(true)
val has_server_version = init_resp.contains("\"1.2.3\"")
expect(has_server_version).to_equal(true)
val has_server_info_key = init_resp.contains("\"serverInfo\"")
expect(has_server_info_key).to_equal(true)
val has_protocol_version = init_resp.contains("\"protocolVersion\"")
expect(has_protocol_version).to_equal(true)
val has_capabilities = init_resp.contains("\"capabilities\"")
expect(has_capabilities).to_equal(true)
val has_jsonrpc = init_resp.contains("\"2.0\"")
expect(has_jsonrpc).to_equal(true)

# --- Response 1: tools/list (schemas built now) ---
val list_resp = sent[1]
val has_adder = list_resp.contains("\"adder\"")
expect(has_adder).to_equal(true)
val has_greeter = list_resp.contains("\"greeter\"")
expect(has_greeter).to_equal(true)
val has_tools_key = list_resp.contains("\"tools\"")
expect(has_tools_key).to_equal(true)

# --- Response 2: tools/call adder → result content "42" ---
val call_resp = sent[2]
val has_content = call_resp.contains("\"content\"")
expect(has_content).to_equal(true)
val has_result_value = call_resp.contains("42")
expect(has_result_value).to_equal(true)
val has_result_key = call_resp.contains("\"result\"")
expect(has_result_key).to_equal(true)

# --- Response 3: unknown method → error -32601 ---
val err_resp = sent[3]
val has_error_key = err_resp.contains("\"error\"")
expect(has_error_key).to_equal(true)
val has_error_code = err_resp.contains("-32601")
expect(has_error_code).to_equal(true)
```

</details>

### McpServer laziness gate (AC-2)

#### schemas_built == 0 after init + initialize handled

- mcp server reset
- mcp server init
- fn
- fn
- fn
- fn
   - Expected: pre_built equals `0`
   - Expected: built_after_init equals `0`
   - Expected: built_after_notif equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mcp_server_reset()

mcp_server_init("lazy-server", "0.1.0")
mcp_server_tool(
    "tool_x",
    "Tool X",
    fn() -> text: "{\"type\":\"object\"}",
    fn(args: text) -> text: "x_result"
)
mcp_server_tool(
    "tool_y",
    "Tool Y",
    fn() -> text: "{\"type\":\"object\"}",
    fn(args: text) -> text: "y_result"
)

val pre_built = registry_schemas_built()
expect(pre_built).to_equal(0)

val init_resp_opt = mcp_server_handle(make_initialize_msg())
val built_after_init = registry_schemas_built()
expect(built_after_init).to_equal(0)

val notif_resp_opt = mcp_server_handle(make_initialized_notif())
val built_after_notif = registry_schemas_built()
expect(built_after_notif).to_equal(0)
```

</details>

#### schemas_built == 2 after first tools/list

- mcp server reset
- mcp server init
- fn
- fn
- fn
- fn
   - Expected: pre_built equals `0`
   - Expected: built_after_list equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mcp_server_reset()

mcp_server_init("lazy-server", "0.1.0")
mcp_server_tool(
    "tool_a",
    "Tool A",
    fn() -> text: "{\"type\":\"object\"}",
    fn(args: text) -> text: "a_result"
)
mcp_server_tool(
    "tool_b",
    "Tool B",
    fn() -> text: "{\"type\":\"object\"}",
    fn(args: text) -> text: "b_result"
)

val pre_built = registry_schemas_built()
expect(pre_built).to_equal(0)

val list_resp_opt = mcp_server_handle(make_tools_list_msg())
val built_after_list = registry_schemas_built()
expect(built_after_list).to_equal(2)
```

</details>

### McpServer loop termination

#### mcp_serve returns when inbound queue is empty

- mcp server reset
- mcp server init
- var transport = BufferTransport with messages
- mcp serve
   - Expected: sent_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mcp_server_reset()
mcp_server_init("term-server", "1.0.0")

var empty_msgs: [text] = []
var transport = BufferTransport.with_messages(empty_msgs)
mcp_serve(transport)

val sent_count = transport.sent_count()
expect(sent_count).to_equal(0)
```

</details>

#### mcp_serve processes all messages and then returns

- mcp server reset
- mcp server init
- msgs push
- var transport = BufferTransport with messages
- mcp serve
   - Expected: sent_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mcp_server_reset()
mcp_server_init("term-server", "1.0.0")

var msgs: [text] = []
msgs.push(make_initialize_msg())

var transport = BufferTransport.with_messages(msgs)
mcp_serve(transport)

val sent_count = transport.sent_count()
expect(sent_count).to_equal(1)
```

</details>

### mcp_server_handle individual methods

#### initialize returns serverInfo with correct name and version

- mcp server reset
- mcp server init
   - Expected: is_nil is false
   - Expected: has_name is true
   - Expected: has_version is true
   - Expected: has_server_info is true
   - Expected: has_capabilities is true
   - Expected: has_protocol is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mcp_server_reset()
mcp_server_init("unit-server", "9.9.9")

val resp_opt = mcp_server_handle(make_initialize_msg())
val is_nil = resp_opt == nil
expect(is_nil).to_equal(false)
val resp = unwrap_resp(resp_opt)
val has_name = resp.contains("\"unit-server\"")
expect(has_name).to_equal(true)
val has_version = resp.contains("\"9.9.9\"")
expect(has_version).to_equal(true)
val has_server_info = resp.contains("\"serverInfo\"")
expect(has_server_info).to_equal(true)
val has_capabilities = resp.contains("\"capabilities\"")
expect(has_capabilities).to_equal(true)
val has_protocol = resp.contains("\"protocolVersion\"")
expect(has_protocol).to_equal(true)
```

</details>

#### notifications/initialized returns nil

- mcp server reset
- mcp server init
   - Expected: is_nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mcp_server_reset()
mcp_server_init("unit-server", "1.0.0")

val resp_opt = mcp_server_handle(make_initialized_notif())
val is_nil = resp_opt == nil
expect(is_nil).to_equal(true)
```

</details>

#### tools/list contains registered tool names

- mcp server reset
- mcp server init
- fn
- fn
   - Expected: is_nil is false
   - Expected: has_name is true
   - Expected: has_tools is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mcp_server_reset()
mcp_server_init("unit-server", "1.0.0")
mcp_server_tool(
    "my_tool",
    "My tool",
    fn() -> text: "{\"type\":\"object\"}",
    fn(args: text) -> text: "ok"
)

val resp_opt = mcp_server_handle(make_tools_list_msg())
val is_nil = resp_opt == nil
expect(is_nil).to_equal(false)
val resp = unwrap_resp(resp_opt)
val has_name = resp.contains("\"my_tool\"")
expect(has_name).to_equal(true)
val has_tools = resp.contains("\"tools\"")
expect(has_tools).to_equal(true)
```

</details>

#### tools/call invokes handler and wraps result in content envelope

- mcp server reset
- mcp server init
- fn
- fn
   - Expected: is_nil is false
   - Expected: has_output is true
   - Expected: has_content is true
   - Expected: has_result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mcp_server_reset()
mcp_server_init("unit-server", "1.0.0")
mcp_server_tool(
    "echo",
    "Echo tool",
    fn() -> text: "{\"type\":\"object\"}",
    fn(args: text) -> text: "echo_output"
)

val resp_opt = mcp_server_handle(make_tools_call_msg("echo"))
val is_nil = resp_opt == nil
expect(is_nil).to_equal(false)
val resp = unwrap_resp(resp_opt)
val has_output = resp.contains("echo_output")
expect(has_output).to_equal(true)
val has_content = resp.contains("\"content\"")
expect(has_content).to_equal(true)
val has_result = resp.contains("\"result\"")
expect(has_result).to_equal(true)
```

</details>

#### unknown method returns JSON-RPC error -32601

- mcp server reset
- mcp server init
   - Expected: is_nil is false
   - Expected: has_error is true
   - Expected: has_code is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mcp_server_reset()
mcp_server_init("unit-server", "1.0.0")

val resp_opt = mcp_server_handle(make_unknown_msg())
val is_nil = resp_opt == nil
expect(is_nil).to_equal(false)
val resp = unwrap_resp(resp_opt)
val has_error = resp.contains("\"error\"")
expect(has_error).to_equal(true)
val has_code = resp.contains("-32601")
expect(has_code).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/mcp_sdk/app_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- McpServer golden transcript (AC-1)
- McpServer laziness gate (AC-2)
- McpServer loop termination
- mcp_server_handle individual methods

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
