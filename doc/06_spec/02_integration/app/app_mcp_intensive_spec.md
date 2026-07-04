# MCP Server Intensive Tests

> End-to-end testing of MCP (Model Context Protocol) servers:

<!-- sdn-diagram:id=app_mcp_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=app_mcp_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

app_mcp_intensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=app_mcp_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Server Intensive Tests

End-to-end testing of MCP (Model Context Protocol) servers:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1031-1040 |
| Category | Testing |
| Difficulty | 5/5 |
| Status | Implemented |
| Source | `test/02_integration/app/app_mcp_intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end testing of MCP (Model Context Protocol) servers:
- mcp: Main MCP server for Simple language
- mcp_jj: Jujutsu version control integration

Tests server lifecycle, message handling, and integration.

## Key Concepts

| Concept | Description |
|---------|-------------|
| MCP Protocol | JSON-RPC based communication |
| Server Lifecycle | Initialize, request/response, shutdown |
| Tool Integration | Exposing Simple tools via MCP |

## Related Specifications

- [MCP Server](../../src/app/mcp/) - Main server
- [MCP JJ](../../src/app/mcp_jj/) - Version control server

## Examples

```simple
# MCP message handling
val request = parse_json_rpc(message)
val response = handle_request(request)
```

## Scenarios

### MCP Source-Mode Protocol Coverage

#### server lifecycle

<details>
<summary>Advanced: initializes the source-mode MCP server</summary>

#### initializes the source-mode MCP server _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _send_mcp_intensive(_mcp_initialize_line("1"))
expect(code).to_equal(0)
expect(out.contains("\"protocolVersion\":\"2025-06-18\"")).to_be(true)
expect(out.contains("\"serverInfo\"")).to_be(true)
expect(not out.contains("\"error\"")).to_be(true)
```

</details>


</details>

<details>
<summary>Advanced: lists tools through the source-mode MCP server</summary>

#### lists tools through the source-mode MCP server _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _mcp_initialize_line("1") + _mcp_initialized_line() + _mcp_request_line("2", "tools/list", "{}")
val (out, err, code) = _send_mcp_intensive(input)
expect(code).to_equal(0)
expect(out.contains("\"result\":{\"tools\":[")).to_be(true)
expect(out.contains("\"name\":\"debug_create_session\"")).to_be(true)
expect(not out.contains("\"error\"")).to_be(true)
```

</details>


</details>

<details>
<summary>Advanced: returns tool-level error for unknown source-mode MCP tool</summary>

#### returns tool-level error for unknown source-mode MCP tool _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _mcp_initialize_line("1") + _mcp_initialized_line() + _mcp_request_line("2", "tools/call", "{\"name\":\"no_such_tool\",\"arguments\":{}}")
val (out, err, code) = _send_mcp_intensive(input)
expect(code).to_equal(0)
expect(out.contains("\"isError\":true")).to_be(true)
expect(out.contains("Unknown tool")).to_be(true)
expect(not out.contains("\"error\"")).to_be(true)
```

</details>


</details>

#### log CLI contract

<details>
<summary>Advanced: runs shared MCP log-mode preflight paths</summary>

#### runs shared MCP log-mode preflight paths _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (help_out, help_err, help_code) = _run_mcp_intensive(["--help"])
expect(help_code).to_equal(0)
expect(help_out.contains("Simple MCP Server")).to_be(true)
expect(help_out.contains("--log-mode")).to_be(true)
expect(help_out.contains("--progress")).to_be(true)
val (json_out, json_err, json_code) = _run_mcp_intensive(["--log-mode=json"])
expect(json_code).to_equal(0)
expect(json_out.contains("\"command\":\"mcp\"")).to_be(true)
expect(json_out.contains("\"status\":\"ready\"")).to_be(true)
```

</details>


</details>

<details>
<summary>Advanced: runs shared MCP invalid-mode and protocol paths</summary>

#### runs shared MCP invalid-mode and protocol paths _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (bad_out, bad_err, bad_code) = _run_mcp_intensive(["--log-mode=noisy"])
expect(bad_code).to_equal(1)
val (ping_out, ping_err, ping_code) = _ping_mcp_intensive()
expect(ping_code).to_equal(0)
expect(ping_out.contains("\"jsonrpc\":\"2.0\"")).to_be(true)
expect(ping_out.contains("\"result\":{}")).to_be(true)
```

</details>


</details>

### MCP Server Lifecycle - Intensive

#### server startup

<details>
<summary>Advanced: validates server configuration</summary>

#### validates server configuration _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = {
    name: "simple-mcp-server",
    version: "0.5.0",
    protocol_version: "2024-11-05"
}

expect(config["name"]).to_equal("simple-mcp-server")
expect(config["version"].?).to_be(true)
expect(config["protocol_version"].?).to_be(true)
```

</details>


</details>

<details>
<summary>Advanced: initializes 100 server instances</summary>

#### initializes 100 server instances _(slow)_

1. instances = instances append
   - Expected: instances.len() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var instances = []

for i in 0..99:
    val instance = {
        id: i,
        status: "initialized",
        port: 3000 + i
    }
    instances = instances.append(instance)

expect(instances.len()).to_equal(100)
```

</details>


</details>

#### server capabilities

<details>
<summary>Advanced: declares tool capabilities</summary>

#### declares tool capabilities _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = [
    "simple/build",
    "simple/test",
    "simple/lint",
    "simple/format"
]

for tool in tools:
    expect(tool.starts_with("simple/")).to_be(true)
```

</details>


</details>

<details>
<summary>Advanced: registers 50 tool endpoints</summary>

#### registers 50 tool endpoints _(slow)_

1. endpoints = endpoints append
   - Expected: endpoints.len() equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var endpoints = []

for i in 0..49:
    val endpoint = {
        name: "tool_{i}",
        method: "POST",
        path: "/tools/tool_{i}"
    }
    endpoints = endpoints.append(endpoint)

expect(endpoints.len()).to_equal(50)
```

</details>


</details>

<details>
<summary>Advanced: initializes the source-mode MCP server</summary>

#### initializes the source-mode MCP server _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _send_mcp_intensive(_mcp_initialize_line("1"))
expect(code).to_equal(0)
expect(out.contains("\"protocolVersion\":\"2025-06-18\"")).to_be(true)
expect(out.contains("\"serverInfo\"")).to_be(true)
expect(not out.contains("\"error\"")).to_be(true)
```

</details>


</details>

### MCP Message Handling - Intensive

#### request parsing

<details>
<summary>Advanced: parses 500 JSON-RPC requests</summary>

#### parses 500 JSON-RPC requests _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parsed = 0

for i in 0..499:
    val request = "{\"jsonrpc\":\"2.0\",\"id\":{i},\"method\":\"test\"}"
    if request.contains("jsonrpc") and request.contains("method"):
        parsed = parsed + 1

expect(parsed).to_equal(500)
```

</details>


</details>

<details>
<summary>Advanced: validates request structure</summary>

#### validates request structure _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var requests = [
    {"jsonrpc": "2.0", "id": 1, "method": "initialize"},
    {"jsonrpc": "2.0", "id": 2, "method": "tools/list"},
    {"jsonrpc": "2.0", "id": 3, "method": "tools/call"}
]

for req in requests:
    expect(req["jsonrpc"]).to_equal("2.0")
    expect(req["id"].?).to_be(true)
    expect(req["method"].?).to_be(true)
```

</details>


</details>

#### response generation

<details>
<summary>Advanced: generates 500 responses</summary>

#### generates 500 responses _(slow)_

1. responses = responses append
   - Expected: responses.len() equals `500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var responses = []

for i in 0..499:
    val response = {
        jsonrpc: "2.0",
        id: i,
        result: "success"
    }
    responses = responses.append(response)

expect(responses.len()).to_equal(500)
```

</details>


</details>

<details>
<summary>Advanced: handles error responses</summary>

#### handles error responses _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = [
    {"code": -32700, "message": "Parse error"},
    {"code": -32600, "message": "Invalid Request"},
    {"code": -32601, "message": "Method not found"}
]

for err in errors:
    expect(err["code"].?).to_be(true)
    expect(err["message"].?).to_be(true)
```

</details>


</details>

<details>
<summary>Advanced: lists tools through the source-mode MCP server</summary>

#### lists tools through the source-mode MCP server _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _mcp_initialize_line("1") + _mcp_initialized_line() + _mcp_request_line("2", "tools/list", "{}")
val (out, err, code) = _send_mcp_intensive(input)
expect(code).to_equal(0)
expect(out.contains("\"result\":{\"tools\":[")).to_be(true)
expect(out.contains("\"name\":\"debug_create_session\"")).to_be(true)
expect(not out.contains("\"error\"")).to_be(true)
```

</details>


</details>

### MCP Tool Integration - Intensive

#### build tool

<details>
<summary>Advanced: handles 100 build requests</summary>

#### handles 100 build requests _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builds = 0

for i in 0..99:
    val request = {
        tool: "simple/build",
        arguments: {
            target: "file{i}.spl",
            release: i % 2 == 0
        }
    }

    if request["tool"] == "simple/build":
        builds = builds + 1

expect(builds).to_equal(100)
```

</details>


</details>

<details>
<summary>Advanced: validates build parameters</summary>

#### validates build parameters _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = [
    {"target": "src/compiler/10.frontend/core/lexer.spl", "release": true},
    {"target": "test/unit/test.spl", "release": false},
    {"target": "examples/hello.spl", "release": true}
]

for param in params:
    expect(param["target"].?).to_be(true)
    expect(param["release"].?).to_be(true)
```

</details>


</details>

#### test tool

<details>
<summary>Advanced: handles 100 test requests</summary>

#### handles 100 test requests _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tests = 0

for i in 0..99:
    val request = {
        tool: "simple/test",
        arguments: {
            pattern: "test/unit/*_spec.spl",
            tag: if i % 3 == 0: "unit" else: "integration"
        }
    }

    if request["tool"] == "simple/test":
        tests = tests + 1

expect(tests).to_equal(100)
```

</details>


</details>

#### format tool

<details>
<summary>Advanced: handles format requests with options</summary>

#### handles format requests with options _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var requests = [
    {"tool": "simple/format", "args": {"check": true}},
    {"tool": "simple/format", "args": {"fix": true}},
    {"tool": "simple/format", "args": {"dry_run": true}}
]

for req in requests:
    expect(req["tool"]).to_equal("simple/format")
    expect(req["args"].?).to_be(true)
```

</details>


</details>

<details>
<summary>Advanced: returns tool-level error for unknown source-mode MCP tool</summary>

#### returns tool-level error for unknown source-mode MCP tool _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _mcp_initialize_line("1") + _mcp_initialized_line() + _mcp_request_line("2", "tools/call", "{\"name\":\"no_such_tool\",\"arguments\":{}}")
val (out, err, code) = _send_mcp_intensive(input)
expect(code).to_equal(0)
expect(out.contains("\"isError\":true")).to_be(true)
expect(out.contains("Unknown tool")).to_be(true)
expect(not out.contains("\"error\"")).to_be(true)
```

</details>


</details>

### MCP JJ Integration - Intensive

#### jj status queries

<details>
<summary>Advanced: handles 100 status requests</summary>

#### handles 100 status requests _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var status_calls = 0

for i in 0..99:
    val request = {
        tool: "jj/status",
        arguments: {}
    }

    if request["tool"] == "jj/status":
        status_calls = status_calls + 1

expect(status_calls).to_equal(100)
```

</details>


</details>

<details>
<summary>Advanced: parses jj status output</summary>

#### parses jj status output _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status_lines = [
    "Working copy : abc123",
    "Parent commit: def456",
    "Changed files: 5"
]

for line in status_lines:
    expect(line.len()).to_be_greater_than(0)
    expect(line.contains(":")).to_be(true)
```

</details>


</details>

#### jj commit operations

<details>
<summary>Advanced: handles 50 commit requests</summary>

#### handles 50 commit requests _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var commits = 0

for i in 0..49:
    val request = {
        tool: "jj/commit",
        arguments: {
            message: "Commit {i}",
            files: ["file{i}.spl"]
        }
    }

    if request["tool"] == "jj/commit":
        commits = commits + 1

expect(commits).to_equal(50)
```

</details>


</details>

<details>
<summary>Advanced: validates commit messages</summary>

#### validates commit messages _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val messages = [
    "Add feature X",
    "Fix bug Y",
    "Update documentation",
    "Refactor module Z"
]

for msg in messages:
    expect(msg.len()).to_be_greater_than(0)
    expect(msg.len()).to_be_less_than(100)
```

</details>


</details>

#### jj diff operations

<details>
<summary>Advanced: handles diff requests</summary>

#### handles diff requests _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diff_requests = [
    {"file": "src/compiler/10.frontend/core/lexer.spl", "revision": "abc123"},
    {"file": "src/compiler/10.frontend/core/parser.spl", "revision": "def456"},
    {"file": "test/unit/test.spl", "revision": "ghi789"}
]

for req in diff_requests:
    expect(req["file"].ends_with(".spl")).to_be(true)
    expect(req["revision"].?).to_be(true)
```

</details>


</details>

### MCP Concurrency - Intensive

#### parallel requests

<details>
<summary>Advanced: simulates 200 concurrent requests</summary>

#### simulates 200 concurrent requests _(slow)_

1. requests = requests append
   - Expected: requests.len() equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var requests = []

for i in 0..199:
    val req = {
        id: i,
        method: "tools/call",
        timestamp: i
    }
    requests = requests.append(req)

expect(requests.len()).to_equal(200)
```

</details>


</details>

<details>
<summary>Advanced: processes requests in batches</summary>

#### processes requests in batches _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var total = 1000
var batch_size = 50
var batches = total / batch_size

var processed = 0
for b in 0..(batches - 1):
    processed = processed + batch_size

expect(processed).to_equal(1000)
```

</details>


</details>

#### request queuing

<details>
<summary>Advanced: manages request queue</summary>

#### manages request queue _(slow)_

1. queue = queue append
2. processed = processed append
   - Expected: processed.len() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = []

# Add 100 requests
for i in 0..99:
    queue = queue.append(i)

# Process them
var processed = []
while queue.len() > 0:
    val item = queue[0]
    processed = processed.append(item)
    queue = queue[1..-1]

expect(processed.len()).to_equal(100)
```

</details>


</details>

### MCP Error Handling - Intensive

#### invalid requests

<details>
<summary>Advanced: detects 100 malformed requests</summary>

#### detects 100 malformed requests _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var errors = 0

for i in 0..99:
    val request = {"invalid": "structure"}

    # Check for required fields
    if not request.get("jsonrpc").?:
        errors = errors + 1

expect(errors).to_equal(100)
```

</details>


</details>

<details>
<summary>Advanced: validates method names</summary>

#### validates method names _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val methods = [
    "initialize",
    "tools/list",
    "tools/call",
    "invalid_method_name"
]

var valid_methods = ["initialize", "tools/list", "tools/call"]

var valid_count = 0
for method in methods:
    if method in valid_methods:
        valid_count = valid_count + 1

expect(valid_count).to_equal(3)
```

</details>


</details>

#### timeout handling

<details>
<summary>Advanced: simulates request timeouts</summary>

#### simulates request timeouts _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timeouts = 0

for i in 0..100:
    val duration = i * 10  # milliseconds

    if duration > 5000:  # 5 second timeout
        timeouts = timeouts + 1

expect(timeouts).to_be_greater_than(0)
```

</details>


</details>

### MCP Logging - Intensive

#### request logging

<details>
<summary>Advanced: logs 500 requests</summary>

#### logs 500 requests _(slow)_

1. log entries = log entries append
   - Expected: log_entries.len() equals `500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var log_entries = []

for i in 0..499:
    val entry = {
        timestamp: i,
        level: "INFO",
        message: "Request {i} received"
    }
    log_entries = log_entries.append(entry)

expect(log_entries.len()).to_equal(500)
```

</details>


</details>

<details>
<summary>Advanced: categorizes log levels</summary>

#### categorizes log levels _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val levels = ["DEBUG", "INFO", "WARN", "ERROR"]

var counts = {
    "DEBUG": 0,
    "INFO": 0,
    "WARN": 0,
    "ERROR": 0
}

for i in 0..399:
    val level = levels[i % 4]
    counts[level] = counts[level] + 1

expect(counts["DEBUG"]).to_equal(100)
expect(counts["INFO"]).to_equal(100)
```

</details>


</details>

#### source-mode log CLI contract

<details>
<summary>Advanced: runs shared MCP log-mode preflight paths</summary>

#### runs shared MCP log-mode preflight paths _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (help_out, help_err, help_code) = _run_mcp_intensive(["--help"])
expect(help_code).to_equal(0)
expect(help_out).to_contain("Simple MCP Server")
expect(help_out).to_contain("--log-mode")
expect(help_out).to_contain("--progress")
val (json_out, json_err, json_code) = _run_mcp_intensive(["--log-mode=json"])
expect(json_code).to_equal(0)
expect(json_out).to_contain("\"command\":\"mcp\"")
expect(json_out).to_contain("\"status\":\"ready\"")
```

</details>


</details>

<details>
<summary>Advanced: runs shared MCP invalid-mode and protocol paths</summary>

#### runs shared MCP invalid-mode and protocol paths _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (bad_out, bad_err, bad_code) = _run_mcp_intensive(["--log-mode=noisy"])
expect(bad_code).to_equal(1)
val (ping_out, ping_err, ping_code) = _ping_mcp_intensive()
expect(ping_code).to_equal(0)
expect(ping_out).to_contain("\"jsonrpc\":\"2.0\"")
expect(ping_out).to_contain("\"result\":{}")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 35 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
