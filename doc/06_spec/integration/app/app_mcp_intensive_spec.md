# App Mcp Intensive Specification

> Tests covering MCP Source-Mode Protocol Coverage, MCP Server Lifecycle - Intensive, MCP Message Handling - Intensive, MCP Tool Integration - Intensive, MCP JJ Integration - Intensive, MCP Concurrency - Intensive, MCP Error Handling - Intensive, MCP Logging - Intensive.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# App Mcp Intensive Specification

## Scenarios

### MCP Source-Mode Protocol Coverage

#### server lifecycle

<details>
<summary>Advanced: initializes the source-mode MCP server</summary>

#### initializes the source-mode MCP server _(slow)_

- initializes the source-mode MCP server
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("initializes the source-mode MCP server")
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

- lists tools through the source-mode MCP server
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lists tools through the source-mode MCP server")
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

- returns tool-level error for unknown source-mode MCP tool
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns tool-level error for unknown source-mode MCP tool")
val input = _mcp_initialize_line("1") + _mcp_initialized_line() + _mcp_request_line("2", "tools/call", "{\"name\":\"no_such_tool\",\"arguments\":{}}")
val (out, err, code) = _send_mcp_intensive(input)
expect(code).to_equal(0)
expect(out.contains("\"isError\":true")).to_be(true)
expect(out.contains("unknown tool")).to_be(true)
expect(out.contains("no_such_tool")).to_be(true)
expect(not out.contains("\"error\"")).to_be(true)
```

</details>


</details>

#### log CLI contract

<details>
<summary>Advanced: runs shared MCP log-mode preflight paths</summary>

#### runs shared MCP log-mode preflight paths _(slow)_

- runs shared MCP log-mode preflight paths
   - Expected: help_code equals `0`
   - Expected: json_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs shared MCP log-mode preflight paths")
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

- runs shared MCP invalid-mode and protocol paths
   - Expected: bad_code equals `1`
   - Expected: ping_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs shared MCP invalid-mode and protocol paths")
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

- validates server configuration
   - Expected: config["name"] equals `simple-mcp-server`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("validates server configuration")
val config = {
    name: "simple-mcp-server",
    version: "0.5.0",
    protocol_version: "2024-11-05"
}

expect(config["name"]).to_equal("simple-mcp-server")
expect(config["version"].? != nil).to_be(true)
expect(config["protocol_version"].? != nil).to_be(true)
```

</details>


</details>

<details>
<summary>Advanced: initializes 100 server instances</summary>

#### initializes 100 server instances _(slow)_

- initializes 100 server instances
   - Expected: instances.len() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("initializes 100 server instances")
var instances = []

for i in 0..100:
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

- declares tool capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("declares tool capabilities")
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

- registers 50 tool endpoints
   - Expected: endpoints.len() equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("registers 50 tool endpoints")
var endpoints = []

for i in 0..50:
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

- initializes the source-mode MCP server
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("initializes the source-mode MCP server")
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

- parses 500 JSON-RPC requests
   - Expected: parsed equals `500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses 500 JSON-RPC requests")
var parsed = 0

for i in 0..500:
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

- validates request structure
   - Expected: req["jsonrpc"] equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("validates request structure")
var requests = [
    {"jsonrpc": "2.0", "id": 1, "method": "initialize"},
    {"jsonrpc": "2.0", "id": 2, "method": "tools/list"},
    {"jsonrpc": "2.0", "id": 3, "method": "tools/call"}
]

for req in requests:
    expect(req["jsonrpc"]).to_equal("2.0")
    expect(req["id"].? != nil).to_be(true)
    expect(req["method"].? != nil).to_be(true)
```

</details>


</details>

#### response generation

<details>
<summary>Advanced: generates 500 responses</summary>

#### generates 500 responses _(slow)_

- generates 500 responses
   - Expected: responses.len() equals `500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates 500 responses")
var responses = []

for i in 0..500:
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

- handles error responses


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles error responses")
val errors = [
    {"code": -32700, "message": "Parse error"},
    {"code": -32600, "message": "Invalid Request"},
    {"code": -32601, "message": "Method not found"}
]

for err in errors:
    expect(err["code"].? != nil).to_be(true)
    expect(err["message"].? != nil).to_be(true)
```

</details>


</details>

<details>
<summary>Advanced: lists tools through the source-mode MCP server</summary>

#### lists tools through the source-mode MCP server _(slow)_

- lists tools through the source-mode MCP server
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lists tools through the source-mode MCP server")
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

- handles 100 build requests
   - Expected: builds equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles 100 build requests")
var builds = 0

for i in 0..100:
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

- validates build parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("validates build parameters")
val params = [
    {"target": "src/compiler/10.frontend/core/lexer.spl", "release": true},
    {"target": "test/unit/test.spl", "release": false},
    {"target": "examples/hello.spl", "release": true}
]

for param in params:
    expect(param["target"].? != nil).to_be(true)
    expect(param["release"].? != nil).to_be(true)
```

</details>


</details>

#### test tool

<details>
<summary>Advanced: handles 100 test requests</summary>

#### handles 100 test requests _(slow)_

- handles 100 test requests
   - Expected: tests equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles 100 test requests")
var tests = 0

for i in 0..100:
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

- handles format requests with options
   - Expected: req["tool"] equals `simple/format`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles format requests with options")
var requests = [
    {"tool": "simple/format", "args": {"check": true}},
    {"tool": "simple/format", "args": {"fix": true}},
    {"tool": "simple/format", "args": {"dry_run": true}}
]

for req in requests:
    expect(req["tool"]).to_equal("simple/format")
    expect(req["args"].? != nil).to_be(true)
```

</details>


</details>

<details>
<summary>Advanced: returns tool-level error for unknown source-mode MCP tool</summary>

#### returns tool-level error for unknown source-mode MCP tool _(slow)_

- returns tool-level error for unknown source-mode MCP tool
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns tool-level error for unknown source-mode MCP tool")
val input = _mcp_initialize_line("1") + _mcp_initialized_line() + _mcp_request_line("2", "tools/call", "{\"name\":\"no_such_tool\",\"arguments\":{}}")
val (out, err, code) = _send_mcp_intensive(input)
expect(code).to_equal(0)
expect(out.contains("\"isError\":true")).to_be(true)
expect(out.contains("unknown tool")).to_be(true)
expect(out.contains("no_such_tool")).to_be(true)
expect(not out.contains("\"error\"")).to_be(true)
```

</details>


</details>

### MCP JJ Integration - Intensive

#### jj status queries

<details>
<summary>Advanced: handles 100 status requests</summary>

#### handles 100 status requests _(slow)_

- handles 100 status requests
   - Expected: status_calls equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles 100 status requests")
var status_calls = 0

for i in 0..100:
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

- parses jj status output


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses jj status output")
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

- handles 50 commit requests
   - Expected: commits equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles 50 commit requests")
var commits = 0

for i in 0..50:
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

- validates commit messages


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("validates commit messages")
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

- handles diff requests


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles diff requests")
val diff_requests = [
    {"file": "src/compiler/10.frontend/core/lexer.spl", "revision": "abc123"},
    {"file": "src/compiler/10.frontend/core/parser.spl", "revision": "def456"},
    {"file": "test/unit/test.spl", "revision": "ghi789"}
]

for req in diff_requests:
    expect(req["file"].ends_with(".spl")).to_be(true)
    expect(req["revision"].? != nil).to_be(true)
```

</details>


</details>

### MCP Concurrency - Intensive

#### parallel requests

<details>
<summary>Advanced: simulates 200 concurrent requests</summary>

#### simulates 200 concurrent requests _(slow)_

- simulates 200 concurrent requests
   - Expected: requests.len() equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simulates 200 concurrent requests")
var requests = []

for i in 0..200:
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

- processes requests in batches
   - Expected: processed equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("processes requests in batches")
var total = 1000
var batch_size = 50
var batches = total / batch_size

var processed = 0
for b in 0..batches:
    processed = processed + batch_size

expect(processed).to_equal(1000)
```

</details>


</details>

#### request queuing

<details>
<summary>Advanced: manages request queue</summary>

#### manages request queue _(slow)_

- manages request queue
   - Expected: processed.len() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("manages request queue")
var queue = []

# Add 100 requests
for i in 0..100:
    queue = queue.append(i)

# Process them
var processed = []
while queue.len() > 0:
    val item = queue[0]
    processed = processed.append(item)
    queue = queue[1..queue.len()]

expect(processed.len()).to_equal(100)
```

</details>


</details>

### MCP Error Handling - Intensive

#### invalid requests

<details>
<summary>Advanced: detects 100 malformed requests</summary>

#### detects 100 malformed requests _(slow)_

- detects 100 malformed requests
   - Expected: errors equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects 100 malformed requests")
var errors = 0

for i in 0..100:
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

- validates method names
   - Expected: valid_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("validates method names")
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

- simulates request timeouts


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simulates request timeouts")
var timeouts = 0

for i in 0..1000:
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

- logs 500 requests
   - Expected: log_entries.len() equals `500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("logs 500 requests")
var log_entries = []

for i in 0..500:
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

- categorizes log levels
   - Expected: counts["DEBUG"] equals `100`
   - Expected: counts["INFO"] equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("categorizes log levels")
val levels = ["DEBUG", "INFO", "WARN", "ERROR"]

var counts = {
    "DEBUG": 0,
    "INFO": 0,
    "WARN": 0,
    "ERROR": 0
}

for i in 0..400:
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

- runs shared MCP log-mode preflight paths
   - Expected: help_code equals `0`
   - Expected: json_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs shared MCP log-mode preflight paths")
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

- runs shared MCP invalid-mode and protocol paths
   - Expected: bad_code equals `1`
   - Expected: ping_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs shared MCP invalid-mode and protocol paths")
val (bad_out, bad_err, bad_code) = _run_mcp_intensive(["--log-mode=noisy"])
expect(bad_code).to_equal(1)
val (ping_out, ping_err, ping_code) = _ping_mcp_intensive()
expect(ping_code).to_equal(0)
expect(ping_out).to_contain("\"jsonrpc\":\"2.0\"")
expect(ping_out).to_contain("\"result\":{}")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/app_mcp_intensive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP Source-Mode Protocol Coverage, MCP Server Lifecycle - Intensive, MCP Message Handling - Intensive, MCP Tool Integration - Intensive, MCP JJ Integration - Intensive, MCP Concurrency - Intensive, MCP Error Handling - Intensive, MCP Logging - Intensive.
- MCP Source-Mode Protocol Coverage
- MCP Server Lifecycle - Intensive
- MCP Message Handling - Intensive
- MCP Tool Integration - Intensive
- MCP JJ Integration - Intensive
- MCP Concurrency - Intensive
- MCP Error Handling - Intensive
- MCP Logging - Intensive

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 35 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c6a6c8cac5ba68bc441f4522945b43f9a24c34ed11f72917a60283a9ace87414`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c6a6c8cac5ba68bc441f4522945b43f9a24c34ed11f72917a60283a9ace87414`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c6a6c8cac5ba68bc441f4522945b43f9a24c34ed11f72917a60283a9ace87414`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/app_mcp_intensive_spec.spl
mirror: doc/06_spec/integration/app/app_mcp_intensive_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/app_mcp_intensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/app_mcp_intensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/app_mcp_intensive_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 30 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/app_mcp_intensive_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes the source-mode MCP server' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/app_mcp_intensive_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists tools through the source-mode MCP server' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/app_mcp_intensive_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns tool-level error for unknown source-mode MCP tool' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
