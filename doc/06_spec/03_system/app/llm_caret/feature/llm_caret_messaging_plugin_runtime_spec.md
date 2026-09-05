# llm_caret_messaging_plugin_runtime_spec

> Composite plugin routes every agent through compiled messaging workers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# llm_caret_messaging_plugin_runtime_spec

Composite plugin routes every agent through compiled messaging workers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_messaging_plugin_runtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Composite plugin routes every agent through compiled messaging workers.

## Scenarios

### LLM Caret messaging composite plugin runtime

#### selects compiled MCP and hook carriers for interpreter-hosted agents

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects compiled MCP and hook carriers for interpreter-hosted agents
- Resolve the production workers independently of caller mode
   - Expected: mcp.kind equals `DatabaseArtifactKind.NativeExecutable`
   - Expected: mcp.source_path equals `src/app/llm_caret/messaging/mcp_worker.spl`
   - Expected: hook.kind equals `DatabaseArtifactKind.NativeExecutable`
   - Expected: hook.source_path equals `src/app/llm_caret/messaging/hook_worker.spl`
   - Expected: bridge.kind equals `DatabaseArtifactKind.NativeExecutable`
   - Expected: bridge.source_path equals `src/app/llm_caret/messaging/bridge_worker.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects compiled MCP and hook carriers for interpreter-hosted agents")
step("Resolve the production workers independently of caller mode")
val mcp = default_messaging_mcp_execution_plan(true)
val hook = default_messaging_hook_execution_plan(true)
val bridge = default_messaging_bridge_execution_plan(true)
expect(mcp.kind).to_equal(DatabaseArtifactKind.NativeExecutable)
expect(mcp.source_path).to_equal("src/app/llm_caret/messaging/mcp_worker.spl")
expect(hook.kind).to_equal(DatabaseArtifactKind.NativeExecutable)
expect(hook.source_path).to_equal("src/app/llm_caret/messaging/hook_worker.spl")
expect(bridge.kind).to_equal(DatabaseArtifactKind.NativeExecutable)
expect(bridge.source_path).to_equal("src/app/llm_caret/messaging/bridge_worker.spl")
```

</details>

#### packages Claude Codex and Gemini chat lifecycle commands

- packages Claude Codex and Gemini chat lifecycle commands
- Inspect the installed-source fragments used by all three agents
   - Expected: gemini_extension_hooks does not contain `hook claude`
   - Expected: file_exists(root + "gemini/gemini-extension.json") is true
   - Expected: file_exists(root + "gemini/skills/llm-caret-messaging/SKILL.md") is true
   - Expected: file_exists(root + "skills/llm-caret-messaging/SKILL.md") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("packages Claude Codex and Gemini chat lifecycle commands")
step("Inspect the installed-source fragments used by all three agents")
val root = "plugins/llm_caret_messaging/"
val claude = file_read(root + "hooks/claude/hooks.json")
val codex = file_read(root + "hooks/codex/hooks.json")
val gemini = file_read(root + "hooks/gemini/settings.fragment.json")
expect(claude).to_contain("caret messaging hook claude")
expect(claude).to_contain("UserPromptSubmit")
expect(codex).to_contain("app_server")
expect(codex).to_contain("messaging\", \"hook\", \"codex")
expect(gemini).to_contain("caret messaging hook gemini")
expect(gemini).to_contain("BeforeAgent")
val gemini_extension_hooks = file_read(root + "gemini/hooks/hooks.json")
expect(gemini_extension_hooks).to_contain("\"matcher\": \"*\"")
expect(gemini_extension_hooks).to_contain("caret messaging hook gemini BeforeAgent")
expect(gemini_extension_hooks.contains("hook claude")).to_equal(false)
expect(file_exists(root + "gemini/gemini-extension.json")).to_equal(true)
expect(file_read(root + "gemini/gemini-extension.json")).to_contain("llm-caret-messaging")
expect(file_exists(root + "gemini/skills/llm-caret-messaging/SKILL.md")).to_equal(true)
expect(file_exists(root + "skills/llm-caret-messaging/SKILL.md")).to_equal(true)
```

</details>

#### packages durable MCP configuration without transport credentials

- packages durable MCP configuration without transport credentials
   - Expected: config does not contain `SLACK_TOKEN`
   - Expected: config does not contain `TEAMS_SECRET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("packages durable MCP configuration without transport credentials")
val config = file_read("plugins/llm_caret_messaging/.mcp.json")
expect(config).to_contain("\"command\": \"caret\"")
expect(config).to_contain("\"args\": [\"messaging\", \"mcp\"]")
expect(config).to_contain("LLM_CARET_MESSAGING_DB")
expect(config.contains("SLACK_TOKEN")).to_equal(false)
expect(config.contains("TEAMS_SECRET")).to_equal(false)
```

</details>

#### does not report plugin health from hashes alone

- does not report plugin health from hashes alone


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not report plugin health from hashes alone")
val source = file_read("src/app/llm_caret/messaging/cli.spl")
expect(source).to_contain("mcp_ready")
expect(source).to_contain("hook_ready")
expect(source).to_contain("bridge_ready")
expect(source).to_contain("messaging_artifact_fresh(mcp_plan")
```

</details>

#### uses real artifact freshness for status and probes

- uses real artifact freshness for status and probes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses real artifact freshness for status and probes")
val source = file_read("src/app/llm_caret/messaging/cli.spl")
expect(source).to_contain("fn messaging_artifact_fresh(")
expect(source).to_contain("llm-caret-messaging: \" + (if ready: \"ready\" else: \"not-ready\")")
expect(source).to_contain("artifact_ready")
expect(source).to_contain("if ready: 0 else: 1")
```

</details>

#### binds inherited subprocess execution to the runtime-backed owner

- binds inherited subprocess execution to the runtime-backed owner
- Inspect the messaging CLI process import
- Resolve inherited subprocess execution through its production owner
   - Expected: source does not contain `app.io.mod." + open_brace + "env_get, process_run, process_run_inherit`
- Protect the native Caret closure from a bare unresolved symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds inherited subprocess execution to the runtime-backed owner")
step("Inspect the messaging CLI process import")
val source = file_read("src/app/llm_caret/messaging/cli.spl")
step("Resolve inherited subprocess execution through its production owner")
# Needles are concatenated: a literal `{name}` inside a text literal is
# string interpolation and fails with `variable not found` (2026-08-25).
val open_brace = "{"
expect(source).to_contain("use app.io.process_ops." + open_brace + "process_run_inherit}")
expect(source.contains("app.io.mod." + open_brace + "env_get, process_run, process_run_inherit")).to_equal(false)
step("Protect the native Caret closure from a bare unresolved symbol")
expect(file_read("src/app/io/process_ops.spl")).to_contain(
    "rt_process_run_inherit(cmd, args)"
)
```

</details>

#### publishes the Claude plugin through the repository marketplace

- publishes the Claude plugin through the repository marketplace


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("publishes the Claude plugin through the repository marketplace")
val marketplace = file_read(".claude-plugin/marketplace.json")
expect(marketplace).to_contain("\"name\": \"simple-plugins\"")
expect(marketplace).to_contain("\"name\": \"llm-caret-messaging\"")
expect(marketplace).to_contain("\"source\": \"./plugins/llm_caret_messaging\"")
```

</details>

#### plans native activation for Claude Codex and Gemini without secrets

- plans native activation for Claude Codex and Gemini without secrets
- Inspect the guarded activation plan before any native CLI mutation
   - Expected: source does not contain `SLACK_TOKEN=`
   - Expected: source does not contain `TEAMS_SECRET=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("plans native activation for Claude Codex and Gemini without secrets")
step("Inspect the guarded activation plan before any native CLI mutation")
val source = file_read("src/app/llm_caret/messaging/cli.spl")
expect(source).to_contain("fn messaging_plugin_activate(args: [text], apply: bool) -> i64:")
expect(source).to_contain("plugin must be installed before activation")
expect(source).to_contain("val apply = args.contains(\"--apply\")")
expect(source).to_contain("claude plugin install llm-caret-messaging@simple-plugins")
expect(source).to_contain("codex mcp add")
expect(source).to_contain("/gemini --consent")
expect(source).to_contain("simple.llm-caret-messaging.native-activation/v1")
expect(source.contains("SLACK_TOKEN=")).to_equal(false)
expect(source.contains("TEAMS_SECRET=")).to_equal(false)
```

</details>

#### plans ownership-guarded native deactivation without removing the shared marketplace

- plans ownership-guarded native deactivation without removing the shared marketplace
- Inspect reversible native cleanup for all three agent integrations
   - Expected: source does not contain `claude plugin marketplace remove simple-plugins`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("plans ownership-guarded native deactivation without removing the shared marketplace")
step("Inspect reversible native cleanup for all three agent integrations")
val source = file_read("src/app/llm_caret/messaging/cli.spl")
expect(source).to_contain("fn messaging_plugin_deactivate(args: [text], apply: bool) -> i64:")
expect(source).to_contain("native activation ownership record missing")
expect(source).to_contain("claude plugin uninstall llm-caret-messaging@simple-plugins")
expect(source).to_contain("codex mcp remove llm-caret-messaging")
expect(source).to_contain("gemini extensions uninstall llm-caret-messaging")
expect(source).to_contain("deactivate native agent registrations before uninstall")
expect(source.contains("claude plugin marketplace remove simple-plugins")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-MSG-007`
- `REQ-LLM-MSG-013`
- `REQ-LLM-MSG-016`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `131397da6b07d1c0cb9e22a2a673ffe900b532606c156dbd732b4586829d1393`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `131397da6b07d1c0cb9e22a2a673ffe900b532606c156dbd732b4586829d1393`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `131397da6b07d1c0cb9e22a2a673ffe900b532606c156dbd732b4586829d1393`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/app/llm_caret/feature/llm_caret_messaging_plugin_runtime_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_plugin_runtime_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_plugin_runtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_plugin_runtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_messaging_plugin_runtime_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/app/llm_caret/feature/llm_caret_messaging_plugin_runtime_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/llm_caret/feature/llm_caret_messaging_plugin_runtime_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects compiled MCP and hook carriers for interpreter-hosted agents' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_messaging_plugin_runtime_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'packages Claude Codex and Gemini chat lifecycle commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_messaging_plugin_runtime_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'packages durable MCP configuration without transport credentials' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
