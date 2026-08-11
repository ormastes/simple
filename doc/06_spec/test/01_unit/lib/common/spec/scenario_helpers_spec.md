# Scenario Helpers Specification

> <details>

<!-- sdn-diagram:id=scenario_helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scenario_helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scenario_helpers_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scenario_helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 53 | 53 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scenario Helpers Specification

## Scenarios

### scenario checker helpers

#### checks text containment returns true when substring present

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_text_contains("hello world", "world")).to_equal(true)
```

</details>

#### checks text containment returns false when substring absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_text_contains("hello world", "mars")).to_equal(false)
```

</details>

#### checks status code equality when codes match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_status_code(200, 200)).to_equal(true)
```

</details>

#### checks status code inequality when codes differ

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_status_code(404, 200)).to_equal(false)
```

</details>

#### checks exit code equality when codes match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_exit_code(0, 0)).to_equal(true)
```

</details>

#### checks exit code inequality when codes differ

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_exit_code(1, 0)).to_equal(false)
```

</details>

#### checks json field present in json text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"name\": \"test\", \"value\": 42}"
expect(check_json_field(json, "name")).to_equal(true)
```

</details>

#### checks json field absent in json text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"name\": \"test\"}"
expect(check_json_field(json, "missing")).to_equal(false)
```

</details>

#### checks file exists for a known path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_file_exists("/dev/null")).to_equal(true)
```

</details>

#### checks file does not exist for bogus path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_file_exists("/tmp/nonexistent_scenario_helper_test_file_xyz")).to_equal(false)
```

</details>

#### checks visible html text without matching attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><button aria-label=\"Hidden label\">Save &amp; close</button></body></html>"
expect(check_html_contains_visible_text(html, "Save & close")).to_equal(true)
expect(check_html_contains_visible_text(html, "Hidden label")).to_equal(false)
```

</details>

#### checks html element visible text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<main><h1>Dashboard</h1></main>"
expect(check_html_has_element_text(html, "h1", "Dashboard")).to_equal(true)
expect(check_html_has_element_text(html, "section", "Dashboard")).to_equal(false)
```

</details>

### scenario checker evidence helpers

#### creates passing text containment evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = check_text_contains_evidence(
    "Login response body",
    "status ok token issued",
    "token issued"
)
expect(evidence.passed).to_equal(true)
expect(evidence.assertion).to_equal("text contains token issued")
expect(evidence.artifact.kind).to_equal(ScenarioCaptureKind.text)
expect(evidence.artifact.body).to_contain("expected substring: token issued")
expect(evidence.artifact.body).to_contain("actual: status ok token issued")
```

</details>

#### creates failing text containment evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = check_text_contains_evidence(
    "Login response body",
    "status denied",
    "token issued"
)
expect(evidence.passed).to_equal(false)
expect(scenario_checker_manual_summary(evidence)).to_equal("text contains token issued (failed) — Login response body (text, text/plain)")
```

</details>

#### creates passing API status evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = check_status_code_evidence(
    "Login API",
    "POST",
    "/login",
    200,
    200,
    "body: token issued"
)
expect(evidence.passed).to_equal(true)
expect(evidence.assertion).to_equal("status 200 equals 200")
expect(evidence.artifact.kind).to_equal(ScenarioCaptureKind.api)
expect(evidence.artifact.body).to_contain("POST /login")
expect(evidence.artifact.body).to_contain("status: 200")
expect(evidence.artifact.body).to_contain("expected status: 200")
```

</details>

#### creates failing API status evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = check_status_code_evidence(
    "Login API",
    "POST",
    "/login",
    500,
    200,
    "body: internal error"
)
expect(evidence.passed).to_equal(false)
expect(evidence.assertion).to_equal("status 500 equals 200")
expect(evidence.artifact.body).to_contain("expected status: 200")
```

</details>

#### creates passing execution exit evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = check_exit_code_evidence(
    "MCP stdio command",
    "simple_mcp_server --stdio",
    0,
    0,
    "stdout: initialize result"
)
expect(evidence.passed).to_equal(true)
expect(evidence.assertion).to_equal("exit 0 equals 0")
expect(evidence.artifact.kind).to_equal(ScenarioCaptureKind.exec)
expect(evidence.artifact.body).to_contain("$ simple_mcp_server --stdio")
expect(evidence.artifact.body).to_contain("exit: 0")
expect(evidence.artifact.body).to_contain("expected exit: 0")
```

</details>

#### creates failing execution exit evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = check_exit_code_evidence(
    "MCP stdio command",
    "simple_mcp_server --stdio",
    2,
    0,
    "stderr: invalid option"
)
expect(evidence.passed).to_equal(false)
expect(evidence.assertion).to_equal("exit 2 equals 0")
expect(evidence.artifact.body).to_contain("expected exit: 0")
```

</details>

#### creates JSON field evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = check_json_field_evidence(
    "Tool result JSON",
    "{\"result\":{\"content\":[]}}",
    "result"
)
expect(evidence.passed).to_equal(true)
expect(evidence.assertion).to_equal("json field exists result")
expect(evidence.artifact.body).to_contain("expected field: result")
expect(evidence.artifact.body).to_contain("\"result\"")
```

</details>

#### creates visible HTML text evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = check_html_contains_visible_text_evidence(
    "Rendered page",
    "<html><body><h1>Ready</h1></body></html>",
    "Ready"
)
expect(evidence.passed).to_equal(true)
expect(evidence.assertion).to_equal("html visible text contains Ready")
expect(evidence.artifact.kind).to_equal(ScenarioCaptureKind.html)
expect(evidence.artifact.body).to_contain("visible text: Ready")
```

</details>

#### creates Simple Web GUI HTML check evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = check_simple_gui_html_contains_text_evidence(
    "Simple Web app",
    "<html><body><button>Launch</button></body></html>",
    "Launch",
    "artifacts/simple-web.html",
    "simple-web",
    "launch"
)
expect(evidence.passed).to_equal(true)
expect(evidence.assertion).to_equal("simple gui html visible text contains Launch")
expect(evidence.artifact.kind).to_equal(ScenarioCaptureKind.html)
expect(evidence.artifact.path).to_equal("artifacts/simple-web.html")
expect(evidence.artifact.scenario_id).to_equal("simple-web")
expect(evidence.artifact.step_id).to_equal("launch")
```

</details>

### scenario capture helpers

#### captures text evidence with correct kind and body

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_text("Response body", "ok: logged in")
expect(artifact.kind).to_equal(ScenarioCaptureKind.text)
expect(artifact.title).to_equal("Response body")
expect(artifact.body).to_equal("ok: logged in")
expect(artifact.mime).to_equal("text/plain")
```

</details>

#### captures log evidence joining lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ["line 1", "line 2", "line 3"]
val artifact = capture_log("Server log", lines)
expect(artifact.kind).to_equal(ScenarioCaptureKind.log)
expect(artifact.title).to_equal("Server log")
expect(artifact.body).to_contain("line 1")
expect(artifact.body).to_contain("line 2")
expect(artifact.body).to_contain("line 3")
```

</details>

#### captures log evidence with empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines: [text] = []
val artifact = capture_log("Empty log", lines)
expect(artifact.body).to_equal("")
```

</details>

#### captures execution response evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_exec_response(
    "MCP stdio command",
    "simple_mcp_server --stdio",
    0,
    "stdout: initialize result"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.exec)
expect(artifact.body).to_contain("$ simple_mcp_server --stdio")
expect(artifact.body).to_contain("exit: 0")
expect(artifact.body).to_contain("stdout: initialize result")
```

</details>

#### captures detailed execution provider evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_exec_detailed(
    "MCP stdio exchange",
    "simple_mcp_server",
    "--stdio --log-level warn",
    "stdin: initialize then tools/list",
    "stdout: initialize result and tools",
    "stderr: no panic",
    0
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.exec)
expect(artifact.body).to_contain("$ simple_mcp_server")
expect(artifact.body).to_contain("args: --stdio --log-level warn")
expect(artifact.body).to_contain("input: stdin: initialize then tools/list")
expect(artifact.body).to_contain("stdout: stdout: initialize result and tools")
expect(artifact.body).to_contain("stderr: stderr: no panic")
expect(artifact.body).to_contain("exit: 0")
```

</details>

#### captures execution provider evidence with scenario and step ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_exec_provider(
    "MCP stdio exchange",
    "simple_mcp_server",
    "--stdio",
    "stdin: initialize",
    "stdout: initialized",
    "stderr: clean",
    0,
    "mcp-stdio",
    "initialize"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.exec)
expect(artifact.scenario_id).to_equal("mcp-stdio")
expect(artifact.step_id).to_equal("initialize")
expect(artifact.body).to_contain("args: --stdio")
expect(artifact.body).to_contain("input: stdin: initialize")
```

</details>

#### captures binary response evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_binary_response(
    "ELF header",
    "ELF64",
    "e_machine=riscv64; e_type=executable"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.binary)
expect(artifact.mime).to_equal("application/octet-stream")
expect(artifact.body).to_contain("format: ELF64")
expect(artifact.body).to_contain("e_machine=riscv64")
```

</details>

#### captures detailed binary provider evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_binary_detailed(
    "ELF header",
    "ELF64",
    "7f 45 4c 46 ...",
    "e_machine=riscv64; e_type=executable",
    "e_machine selects target architecture"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.binary)
expect(artifact.body).to_contain("format: ELF64")
expect(artifact.body).to_contain("raw bytes: 7f 45 4c 46 ...")
expect(artifact.body).to_contain("decoded fields: e_machine=riscv64; e_type=executable")
expect(artifact.body).to_contain("field comments: e_machine selects target architecture")
```

</details>

#### captures binary provider evidence with scenario and step ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_binary_provider(
    "ELF header",
    "ELF64",
    "7f 45 4c 46",
    "e_machine=riscv64",
    "e_machine selects target architecture",
    "loader",
    "parse-header"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.binary)
expect(artifact.scenario_id).to_equal("loader")
expect(artifact.step_id).to_equal("parse-header")
expect(artifact.body).to_contain("raw bytes: 7f 45 4c 46")
```

</details>

#### captures TUI selection provider evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_tui_selection(
    "Settings menu",
    "x=4 y=2 w=18 h=1",
    "menu item: Save",
    "File > Save",
    "focus on Save, status Ready",
    "artifacts/settings-menu.txt",
    "settings",
    "save-menu"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.tui)
expect(artifact.mime).to_equal("text/plain")
expect(artifact.path).to_equal("artifacts/settings-menu.txt")
expect(artifact.scenario_id).to_equal("settings")
expect(artifact.step_id).to_equal("save-menu")
expect(artifact.body).to_contain("selected rectangle: x=4 y=2 w=18 h=1")
expect(artifact.body).to_contain("highlight: menu item: Save")
expect(artifact.body).to_contain("inverted active menu: File > Save")
expect(artifact.body).to_contain("visible state: focus on Save, status Ready")
```

</details>

#### captures GUI selection provider evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_gui_selection(
    "Toolbar hover",
    "x=10 y=12 w=32 h=32",
    "Save toolbar button",
    "",
    "button highlighted",
    "artifacts/toolbar.png",
    "toolbar",
    "hover-save"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.gui)
expect(artifact.mime).to_equal("image/png")
expect(artifact.path).to_equal("artifacts/toolbar.png")
expect(artifact.body).to_contain("highlight: Save toolbar button")
```

</details>

#### captures html text evidence from markup

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_html_text(
    "Rendered page",
    "<html><body><h1>Status</h1><p>Ready</p></body></html>",
    "artifacts/page.html"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.html)
expect(artifact.path).to_equal("artifacts/page.html")
expect(artifact.body).to_contain("visible text: Status Ready")
```

</details>

#### captures Simple Web GUI as HTML evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_simple_gui_html(
    "Simple Web app",
    "<html><body>Ready</body></html>",
    "artifacts/simple-web.html",
    "simple-web",
    "ready"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.html)
expect(artifact.body).to_contain("simple gui html capture")
expect(artifact.scenario_id).to_equal("simple-web")
```

</details>

#### prefers HTML evidence for GUI capture when markup is available

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_gui_with_html_if_possible(
    "GUI step",
    "<html><body>Ready</body></html>",
    "fallback screenshot state",
    "artifacts/gui.html",
    "gui",
    "step"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.html)
expect(artifact.body).to_contain("visible text: Ready")
```

</details>

#### falls back to GUI evidence when HTML is unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_gui_with_html_if_possible(
    "GUI step",
    "",
    "button highlighted",
    "artifacts/gui.png",
    "gui",
    "step"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.gui)
expect(artifact.mime).to_equal("image/png")
expect(artifact.body).to_contain("visible state: button highlighted")
```

</details>

#### records html checker tool results

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = html_check_result(
    ScenarioHtmlCheckTool.axe_core,
    "Accessible page",
    "<main><h1>Ready</h1></main>",
    true,
    "no serious violations",
    ""
)
expect(result.passed).to_equal(true)
expect(scenario_html_check_manual_summary(result)).to_contain("axe_core passed: no serious violations")
```

</details>

#### captures basic API response evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_api_response(
    "Login API",
    "POST",
    "/login",
    200,
    "token issued"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.api)
expect(artifact.body).to_contain("POST /login")
expect(artifact.body).to_contain("status: 200")
expect(artifact.body).to_contain("token issued")
```

</details>

#### captures protocol provider details with redaction notes

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_api_protocol(
    "MCP tools call",
    "POST",
    "/mcp",
    "method=tools/call id=7",
    "authorization=<redacted>; content-type=application/json",
    "result.content[0].text; isError=false",
    "authorization token"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.protocol)
expect(artifact.redacted).to_equal(true)
expect(artifact.body).to_contain("params: method=tools/call id=7")
expect(artifact.body).to_contain("headers: authorization=<redacted>; content-type=application/json")
expect(artifact.body).to_contain("response fields: result.content[0].text; isError=false")
expect(artifact.body).to_contain("redacted: authorization token")
```

</details>

#### detects sensitive api fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_sensitive_api_field("authorization")).to_equal(true)
expect(is_sensitive_api_field("access_token")).to_equal(true)
expect(is_sensitive_api_field("content-type")).to_equal(false)
```

</details>

#### redacts sensitive field summaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(api_field_summary("authorization", "Bearer secret")).to_equal("authorization=<redacted>")
expect(api_field_summary("content-type", "application/json")).to_equal("content-type=application/json")
```

</details>

#### summarizes aligned api field lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = ["method", "id", "access_token"]
val values = ["tools/call", "7", "secret-token"]
val summary = api_field_list_summary(names, values)
expect(summary).to_equal("method=tools/call; id=7; access_token=<redacted>")
```

</details>

#### summarizes only available name value pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = ["method", "id", "extra"]
val values = ["tools/list", "8"]
expect(api_field_list_summary(names, values)).to_equal("method=tools/list; id=8")
```

</details>

#### lists redacted api field names without values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = ["content-type", "authorization", "cookie"]
expect(redacted_api_field_names(names)).to_equal("authorization; cookie")
```

</details>

#### lists redacted api field names with group prefixes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = ["content-type", "authorization", "cookie"]
expect(redacted_api_field_group_names("headers", names)).to_equal("headers.authorization; headers.cookie")
```

</details>

#### lists redacted protocol fields across params headers and response

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = ["method", "access_token"]
val headers = ["authorization", "content-type"]
val response_fields = ["result", "refresh_token"]
expect(redacted_api_protocol_field_names(params, headers, response_fields)).to_equal("params.access_token; headers.authorization; response.refresh_token")
```

</details>

#### captures protocol provider details from structured fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_api_protocol_fields(
    "MCP tools call",
    "POST",
    "/mcp",
    ["method", "id"],
    ["tools/call", "7"],
    ["authorization", "content-type"],
    ["Bearer secret", "application/json"],
    ["result.content[0].text", "isError"],
    ["ok", "false"]
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.protocol)
expect(artifact.redacted).to_equal(true)
expect(artifact.body).to_contain("params: method=tools/call; id=7")
expect(artifact.body).to_contain("headers: authorization=<redacted>; content-type=application/json")
expect(artifact.body).to_contain("response fields: result.content[0].text=ok; isError=false")
expect(artifact.body).to_contain("redacted: headers.authorization")
```

</details>

#### captures redaction notes for params headers and response fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_api_protocol_fields(
    "Token refresh",
    "POST",
    "/oauth/token",
    ["grant_type", "refresh_token"],
    ["refresh_token", "old-token"],
    ["authorization", "content-type"],
    ["Bearer client-secret", "application/json"],
    ["access_token", "expires_in"],
    ["new-token", "3600"]
)
expect(artifact.redacted).to_equal(true)
expect(artifact.body).to_contain("params: grant_type=refresh_token; refresh_token=<redacted>")
expect(artifact.body).to_contain("headers: authorization=<redacted>; content-type=application/json")
expect(artifact.body).to_contain("response fields: access_token=<redacted>; expires_in=3600")
expect(artifact.body).to_contain("redacted: params.refresh_token; headers.authorization; response.access_token")
```

</details>

#### captures protocol provider fields with scenario and step ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = capture_api_protocol_provider(
    "MCP tools call",
    "JSON-RPC",
    "stdio:tools/call",
    ["method", "id", "access_token"],
    ["tools/call", "7", "secret-token"],
    ["authorization", "transport"],
    ["Bearer secret", "stdio"],
    ["result.content", "isError"],
    ["present", "false"],
    "mcp-stdio",
    "tools-call"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.protocol)
expect(artifact.redacted).to_equal(true)
expect(artifact.scenario_id).to_equal("mcp-stdio")
expect(artifact.step_id).to_equal("tools-call")
expect(artifact.body).to_contain("params: method=tools/call; id=7; access_token=<redacted>")
expect(artifact.body).to_contain("headers: authorization=<redacted>; transport=stdio")
expect(artifact.body).to_contain("response fields: result.content=present; isError=false")
expect(artifact.body).to_contain("redacted: params.access_token; headers.authorization")
```

</details>

### scenario step result

#### creates a passing step result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = step_result("Login succeeds", true)
expect(sr.description).to_equal("Login succeeds")
expect(sr.passed).to_equal(true)
```

</details>

#### creates a failing step result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = step_result("Token valid", false)
expect(sr.passed).to_equal(false)
```

</details>

#### renders passing step result summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = step_result("API returns 200", true)
expect(step_result_summary(sr)).to_equal("API returns 200 (passed)")
```

</details>

#### renders failing step result summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = step_result("File exists", false)
expect(step_result_summary(sr)).to_equal("File exists (failed)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/spec/scenario_helpers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scenario checker helpers
- scenario checker evidence helpers
- scenario capture helpers
- scenario step result

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 53 |
| Active scenarios | 53 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
