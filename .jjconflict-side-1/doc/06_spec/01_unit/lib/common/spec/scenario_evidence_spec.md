# Scenario Evidence Specification

> Tests covering scenario evidence capture policy, scenario evidence artifact.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scenario Evidence Specification

## Scenarios

### scenario evidence capture policy

#### keeps root capture off by default

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps root capture off by default
   - Expected: policy.enabled is false
   - Expected: scenario_policy_manual_summary(policy) equals `capture off`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps root capture off by default")
val policy = scenario_capture_off()
expect(policy.enabled).to_equal(false)
expect(scenario_policy_manual_summary(policy)).to_equal("capture off")
```

</details>

#### treats bare capture as after step tui capture

- treats bare capture as after step tui capture
   - Expected: policy.enabled is true
   - Expected: scenario_policy_manual_summary(policy) equals `capture tui after_step`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("treats bare capture as after step tui capture")
val policy = scenario_capture_bare()
expect(policy.enabled).to_equal(true)
expect(scenario_policy_manual_summary(policy)).to_equal("capture tui after_step")
```

</details>

#### allows explicit enum based api capture

- allows explicit enum based api capture
   - Expected: policy.enabled is true
   - Expected: scenario_policy_manual_summary(policy) equals `capture api after_scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("allows explicit enum based api capture")
val policy = scenario_capture_policy(
    ScenarioCaptureMode.after_scenario,
    ScenarioCaptureKind.api
)
expect(policy.enabled).to_equal(true)
expect(scenario_policy_manual_summary(policy)).to_equal("capture api after_scenario")
```

</details>

#### uses built in off when no capture policy scope is present

- uses built in off when no capture policy scope is present
   - Expected: resolution.source equals `built-in`
   - Expected: resolution.policy.enabled is false
   - Expected: scenario_policy_resolution_manual_summary(resolution) equals `capture off from built-in`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses built in off when no capture policy scope is present")
val absent = scenario_capture_policy_absent()
val resolution = resolve_scenario_capture_policy(
    absent,
    absent,
    absent,
    absent,
    absent,
    absent
)
expect(resolution.source).to_equal("built-in")
expect(resolution.policy.enabled).to_equal(false)
expect(scenario_policy_resolution_manual_summary(resolution)).to_equal("capture off from built-in")
```

</details>

#### resolves root policy when no closer scope is present

- resolves root policy when no closer scope is present
   - Expected: resolution.source equals `root`
   - Expected: scenario_policy_manual_summary(resolution.policy) equals `capture log on_failure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves root policy when no closer scope is present")
val absent = scenario_capture_policy_absent()
val root = scenario_capture_policy_override(
    scenario_capture_policy(
        ScenarioCaptureMode.on_failure,
        ScenarioCaptureKind.log
    )
)
val resolution = resolve_scenario_capture_policy(
    absent,
    absent,
    absent,
    absent,
    absent,
    root
)
expect(resolution.source).to_equal("root")
expect(scenario_policy_manual_summary(resolution.policy)).to_equal("capture log on_failure")
```

</details>

#### resolves folder policy before root policy

- resolves folder policy before root policy
   - Expected: resolution.source equals `folder`
   - Expected: scenario_policy_manual_summary(resolution.policy) equals `capture exec after_scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves folder policy before root policy")
val absent = scenario_capture_policy_absent()
val folder = scenario_capture_policy_override(
    scenario_capture_policy(
        ScenarioCaptureMode.after_scenario,
        ScenarioCaptureKind.exec
    )
)
val root = scenario_capture_policy_override(
    scenario_capture_policy(
        ScenarioCaptureMode.on_failure,
        ScenarioCaptureKind.log
    )
)
val resolution = resolve_scenario_capture_policy(
    absent,
    absent,
    absent,
    absent,
    folder,
    root
)
expect(resolution.source).to_equal("folder")
expect(scenario_policy_manual_summary(resolution.policy)).to_equal("capture exec after_scenario")
```

</details>

#### resolves file policy before folder policy

- resolves file policy before folder policy
   - Expected: resolution.source equals `file`
   - Expected: scenario_policy_manual_summary(resolution.policy) equals `capture api after_step`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves file policy before folder policy")
val absent = scenario_capture_policy_absent()
val file = scenario_capture_policy_override(
    scenario_capture_policy(
        ScenarioCaptureMode.after_step,
        ScenarioCaptureKind.api
    )
)
val folder = scenario_capture_policy_override(
    scenario_capture_policy(
        ScenarioCaptureMode.after_scenario,
        ScenarioCaptureKind.exec
    )
)
val resolution = resolve_scenario_capture_policy(
    absent,
    absent,
    absent,
    file,
    folder,
    absent
)
expect(resolution.source).to_equal("file")
expect(scenario_policy_manual_summary(resolution.policy)).to_equal("capture api after_step")
```

</details>

#### resolves scenario policy before file policy

- resolves scenario policy before file policy
   - Expected: resolution.source equals `scenario`
   - Expected: scenario_policy_manual_summary(resolution.policy) equals `capture protocol after_step`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves scenario policy before file policy")
val absent = scenario_capture_policy_absent()
val scenario = scenario_capture_policy_override(
    scenario_capture_policy(
        ScenarioCaptureMode.after_step,
        ScenarioCaptureKind.protocol
    )
)
val file = scenario_capture_policy_override(
    scenario_capture_policy(
        ScenarioCaptureMode.after_step,
        ScenarioCaptureKind.api
    )
)
val resolution = resolve_scenario_capture_policy(
    absent,
    absent,
    scenario,
    file,
    absent,
    absent
)
expect(resolution.source).to_equal("scenario")
expect(scenario_policy_manual_summary(resolution.policy)).to_equal("capture protocol after_step")
```

</details>

#### resolves function checker policy before scenario policy

- resolves function checker policy before scenario policy
   - Expected: resolution.source equals `function`
   - Expected: scenario_policy_manual_summary(resolution.policy) equals `capture text on_failure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves function checker policy before scenario policy")
val absent = scenario_capture_policy_absent()
val function_policy = scenario_capture_policy_override(
    scenario_capture_policy(
        ScenarioCaptureMode.on_failure,
        ScenarioCaptureKind.text
    )
)
val scenario = scenario_capture_policy_override(
    scenario_capture_policy(
        ScenarioCaptureMode.after_step,
        ScenarioCaptureKind.protocol
    )
)
val resolution = resolve_scenario_capture_policy(
    absent,
    function_policy,
    scenario,
    absent,
    absent,
    absent
)
expect(resolution.source).to_equal("function")
expect(scenario_policy_manual_summary(resolution.policy)).to_equal("capture text on_failure")
```

</details>

#### resolves step policy before function checker policy

- resolves step policy before function checker policy
   - Expected: resolution.source equals `step`
   - Expected: scenario_policy_manual_summary(resolution.policy) equals `capture tui after_step`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves step policy before function checker policy")
val absent = scenario_capture_policy_absent()
val step = scenario_capture_policy_override(scenario_capture_bare())
val function_policy = scenario_capture_policy_override(
    scenario_capture_policy(
        ScenarioCaptureMode.on_failure,
        ScenarioCaptureKind.text
    )
)
val resolution = resolve_scenario_capture_policy(
    step,
    function_policy,
    absent,
    absent,
    absent,
    absent
)
expect(resolution.source).to_equal("step")
expect(scenario_policy_manual_summary(resolution.policy)).to_equal("capture tui after_step")
```

</details>

### scenario evidence artifact

#### renders path backed evidence for manual output

- renders path backed evidence for manual output
   - Expected: scenario_evidence_manual_summary(artifact) equals `App screen after login (gui, image/png) -> artifacts/login.png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders path backed evidence for manual output")
val artifact = scenario_evidence_artifact(
    ScenarioCaptureKind.gui,
    "App screen after login",
    "image/png",
    "artifacts/login.png",
    "",
    "login",
    "submit"
)
expect(scenario_evidence_manual_summary(artifact)).to_equal("App screen after login (gui, image/png) -> artifacts/login.png")
```

</details>

#### renders redacted evidence without leaking body or path

- renders redacted evidence without leaking body or path
   - Expected: scenario_evidence_manual_summary(artifact) equals `HTTP authorization header (protocol, redacted)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders redacted evidence without leaking body or path")
val artifact = scenario_redacted_evidence_artifact(
    ScenarioCaptureKind.protocol,
    "HTTP authorization header",
    "message/http",
    "api-login",
    "request"
)
expect(scenario_evidence_manual_summary(artifact)).to_equal("HTTP authorization header (protocol, redacted)")
```

</details>

#### creates api evidence with request and status details

- creates api evidence with request and status details
   - Expected: artifact.kind equals `ScenarioCaptureKind.api`
   - Expected: comparison.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates api evidence with request and status details")
val artifact = scenario_api_evidence(
    "Login API response",
    "POST",
    "/login",
    200,
    "body: token issued",
    "login",
    "submit"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.api)
expect(artifact.body).to_contain("POST /login")
expect(artifact.body).to_contain("status: 200")
expect(artifact.body).to_contain("body: token issued")

val canonical = legacy_evidence_to_canonical(artifact)
val oracle = oracle_spec_open("scenario_api_evidence_login_response", [
    check_exact("kind", "api"),
    check_exact("title", "Login API response"),
    check_exact("body", "POST /login\nstatus: 200\nbody: token issued")
])
val comparison = compare_evidence(canonical, oracle)
expect(comparison.status).to_equal(EvidenceStatus.passed)
```

</details>

#### creates protocol evidence with params headers response fields and redaction notes

- creates protocol evidence with params headers response fields and redaction notes
   - Expected: artifact.kind equals `ScenarioCaptureKind.protocol`
   - Expected: artifact.redacted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates protocol evidence with params headers response fields and redaction notes")
val artifact = scenario_api_protocol_evidence(
    "MCP tools call",
    "POST",
    "/mcp",
    "method=tools/call id=7",
    "authorization=<redacted>; content-type=application/json",
    "result.content[0].text; isError=false",
    "authorization token",
    "mcp",
    "tools-call"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.protocol)
expect(artifact.redacted).to_equal(true)
expect(artifact.body).to_contain("POST /mcp")
expect(artifact.body).to_contain("params: method=tools/call id=7")
expect(artifact.body).to_contain("headers: authorization=<redacted>; content-type=application/json")
expect(artifact.body).to_contain("response fields: result.content[0].text; isError=false")
expect(artifact.body).to_contain("redacted: authorization token")
```

</details>

#### creates execution evidence with command and exit code

- creates execution evidence with command and exit code
   - Expected: artifact.kind equals `ScenarioCaptureKind.exec`
   - Expected: comparison.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates execution evidence with command and exit code")
val artifact = scenario_exec_evidence(
    "Bootstrap command",
    "simple test test/03_system/tools/bootstrap_mcp_spec.spl",
    0,
    "stdout: all passed",
    "bootstrap",
    "run"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.exec)
expect(artifact.body).to_contain("$ simple test test/03_system/tools/bootstrap_mcp_spec.spl")
expect(artifact.body).to_contain("exit: 0")

val canonical = legacy_evidence_to_canonical(artifact)
val oracle = oracle_spec_open("scenario_exec_evidence_bootstrap_command", [
    check_exact("kind", "exec"),
    check_exact("title", "Bootstrap command"),
    check_exact(
        "body",
        "$ simple test test/03_system/tools/bootstrap_mcp_spec.spl\nexit: 0\nstdout: all passed"
    )
])
val comparison = compare_evidence(canonical, oracle)
expect(comparison.status).to_equal(EvidenceStatus.passed)
```

</details>

#### creates detailed execution evidence with args input streams and exit code

- creates detailed execution evidence with args input streams and exit code
   - Expected: artifact.kind equals `ScenarioCaptureKind.exec`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates detailed execution evidence with args input streams and exit code")
val artifact = scenario_exec_detailed_evidence(
    "MCP stdio command",
    "simple_mcp_server",
    "--stdio --log-level warn",
    "stdin: initialize then tools/list",
    "stdout: initialize result and tools",
    "stderr: no panic",
    0,
    "mcp",
    "stdio"
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

#### creates binary evidence with format and field summary

- creates binary evidence with format and field summary
   - Expected: artifact.kind equals `ScenarioCaptureKind.binary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates binary evidence with format and field summary")
val artifact = scenario_binary_evidence(
    "ELF header",
    "ELF64",
    "e_machine: riscv64",
    "loader",
    "parse"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.binary)
expect(artifact.body).to_contain("format: ELF64")
expect(artifact.body).to_contain("e_machine: riscv64")
```

</details>

#### creates detailed binary evidence with raw bytes decoded fields and comments

- creates detailed binary evidence with raw bytes decoded fields and comments
   - Expected: artifact.kind equals `ScenarioCaptureKind.binary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates detailed binary evidence with raw bytes decoded fields and comments")
val artifact = scenario_binary_detailed_evidence(
    "ELF header",
    "ELF64",
    "7f 45 4c 46 ...",
    "e_machine=riscv64; e_type=executable",
    "e_machine selects the target architecture",
    "loader",
    "parse"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.binary)
expect(artifact.body).to_contain("format: ELF64")
expect(artifact.body).to_contain("raw bytes: 7f 45 4c 46 ...")
expect(artifact.body).to_contain("decoded fields: e_machine=riscv64; e_type=executable")
expect(artifact.body).to_contain("field comments: e_machine selects the target architecture")
```

</details>

#### creates TUI selection evidence with rectangle highlight and active menu

- creates TUI selection evidence with rectangle highlight and active menu
   - Expected: artifact.kind equals `ScenarioCaptureKind.tui`
   - Expected: artifact.mime equals `text/plain`
   - Expected: artifact.path equals `artifacts/settings-menu.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates TUI selection evidence with rectangle highlight and active menu")
val artifact = scenario_ui_selection_evidence(
    ScenarioCaptureKind.tui,
    "Settings menu after keyboard navigation",
    "x=4 y=2 w=18 h=1",
    "menu item: Save",
    "File > Save",
    "focus on Save, status Ready",
    "artifacts/settings-menu.txt",
    "settings",
    "open-menu"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.tui)
expect(artifact.mime).to_equal("text/plain")
expect(artifact.path).to_equal("artifacts/settings-menu.txt")
expect(artifact.body).to_contain("selected rectangle: x=4 y=2 w=18 h=1")
expect(artifact.body).to_contain("highlight: menu item: Save")
expect(artifact.body).to_contain("inverted active menu: File > Save")
expect(artifact.body).to_contain("visible state: focus on Save, status Ready")
```

</details>

#### creates GUI selection evidence with image mime

- creates GUI selection evidence with image mime
   - Expected: artifact.kind equals `ScenarioCaptureKind.gui`
   - Expected: artifact.mime equals `image/png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates GUI selection evidence with image mime")
val artifact = scenario_ui_selection_evidence(
    ScenarioCaptureKind.gui,
    "Toolbar button after hover",
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
expect(artifact.body).to_contain("selected rectangle: x=10 y=12 w=32 h=32")
expect(artifact.body).to_contain("highlight: Save toolbar button")
expect(artifact.body).to_contain("visible state: button highlighted")
```

</details>

#### creates Simple Web GUI HTML evidence with visible text

- creates Simple Web GUI HTML evidence with visible text
   - Expected: artifact.kind equals `ScenarioCaptureKind.html`
   - Expected: artifact.mime equals `text/html`
   - Expected: artifact.path equals `artifacts/simple-web.html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates Simple Web GUI HTML evidence with visible text")
val artifact = scenario_simple_gui_html_evidence(
    "Simple Web app",
    "<html><body><button>Save</button></body></html>",
    "Save",
    "artifacts/simple-web.html",
    "simple-web",
    "save"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.html)
expect(artifact.mime).to_equal("text/html")
expect(artifact.path).to_equal("artifacts/simple-web.html")
expect(artifact.body).to_contain("simple gui html capture")
expect(artifact.body).to_contain("visible text: Save")
expect(artifact.body).to_contain("<button>Save</button>")
```

</details>

#### summarizes html checker results with tool name

- summarizes html checker results with tool name
   - Expected: scenario_html_check_manual_summary(result) equals `simple_html_heuristic passed: main landmark present — Simple Web app (html,... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("summarizes html checker results with tool name")
val artifact = scenario_simple_gui_html_evidence(
    "Simple Web app",
    "<html><body><main>Ready</main></body></html>",
    "Ready",
    "",
    "simple-web",
    "ready"
)
val result = scenario_html_check_result(
    ScenarioHtmlCheckTool.simple_html_heuristic,
    true,
    "main landmark present",
    "",
    artifact
)
expect(scenario_html_check_manual_summary(result)).to_equal("simple_html_heuristic passed: main landmark present — Simple Web app (html, text/html)")
```

</details>

#### links checker assertion status to captured evidence

- links checker assertion status to captured evidence
   - Expected: scenario_checker_manual_summary(evidence) equals `Then tool call succeeds (passed) — Tool response (api, text/plain)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("links checker assertion status to captured evidence")
val artifact = scenario_api_evidence(
    "Tool response",
    "POST",
    "/mcp",
    200,
    "result: ok",
    "mcp",
    "call"
)
val evidence = scenario_checker_evidence("Then tool call succeeds", true, artifact)
expect(scenario_checker_manual_summary(evidence)).to_equal("Then tool call succeeds (passed) — Tool response (api, text/plain)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/spec/scenario_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scenario evidence capture policy, scenario evidence artifact.
- scenario evidence capture policy
- scenario evidence artifact

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e76f597003fbd74d414afde487dbf3403485bce8e01fb1187dca956324d72663`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e76f597003fbd74d414afde487dbf3403485bce8e01fb1187dca956324d72663`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e76f597003fbd74d414afde487dbf3403485bce8e01fb1187dca956324d72663`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/common/spec/scenario_evidence_spec.spl
mirror: doc/06_spec/01_unit/lib/common/spec/scenario_evidence_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/spec/scenario_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/spec/scenario_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/spec/scenario_evidence_spec.spl:238:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders path backed evidence for manual output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/scenario_evidence_spec.spl:252:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders redacted evidence without leaking body or path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
