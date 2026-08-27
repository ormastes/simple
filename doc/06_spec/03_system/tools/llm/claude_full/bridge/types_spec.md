# Claude Full Bridge Types

> Checks bridge protocol constants and DTO surfaces mirrored from types.ts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge Types

Checks bridge protocol constants and DTO surfaces mirrored from types.ts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bridge/types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks bridge protocol constants and DTO surfaces mirrored from types.ts.

## Scenarios

### Claude full bridge types

#### exports bridge constants and enum values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exports bridge constants and enum values
- Pin defaults and discriminated union values
   - Expected: defaultSessionTimeoutMs() equals `86400000`
   - Expected: defaultSessionTimeoutHours() equals `24`
   - Expected: remoteControlDisconnectedMsg() equals `Remote Control disconnected.`
   - Expected: sessionDoneStatuses() equals `["completed", "failed", "interrupted"]`
   - Expected: sessionActivityTypes() equals `["tool_start", "text", "result", "error"]`
   - Expected: spawnModes() equals `["single-session", "worktree", "same-dir"]`
   - Expected: bridgeWorkerTypes() equals `["claude_code", "claude_code_assistant"]`
   - Expected: workDataTypes() equals `["session", "healthcheck"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports bridge constants and enum values")
step("Pin defaults and discriminated union values")
expect(defaultSessionTimeoutMs()).to_equal(86400000)
expect(defaultSessionTimeoutHours()).to_equal(24)
expect(bridgeLoginInstruction()).to_contain("claude.ai subscriptions")
expect(bridgeLoginError()).to_contain("You must be logged in")
expect(remoteControlDisconnectedMsg()).to_equal("Remote Control disconnected.")
expect(sessionDoneStatuses()).to_equal(["completed", "failed", "interrupted"])
expect(sessionActivityTypes()).to_equal(["tool_start", "text", "result", "error"])
expect(spawnModes()).to_equal(["single-session", "worktree", "same-dir"])
expect(bridgeWorkerTypes()).to_equal(["claude_code", "claude_code_assistant"])
expect(workDataTypes()).to_equal(["session", "healthcheck"])
```

</details>

#### builds work response and secret DTOs

- builds work response and secret DTOs
- Model environment work payloads and decoded secrets
   - Expected: work.kind equals `work`
   - Expected: work.data.kind equals `session`
   - Expected: work.environmentId equals `env_1`
   - Expected: secret.sessionIngressToken equals `jwt`
   - Expected: secret.useCodeSessions is true
   - Expected: secret.hasMcpConfig is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds work response and secret DTOs")
step("Model environment work payloads and decoded secrets")
val data = WorkData.session("cse_1")
val work = WorkResponse.new("work_1", "env_1", "queued", data, "secret", "now")
expect(work.kind).to_equal("work")
expect(work.data.kind).to_equal("session")
expect(work.environmentId).to_equal("env_1")
val secret = WorkSecret.new(1, "jwt", "https://api", true).withOptionalBlocks()
expect(secret.sessionIngressToken).to_equal("jwt")
expect(secret.useCodeSessions).to_equal(true)
expect(secret.hasMcpConfig).to_equal(true)
```

</details>

#### builds bridge config with reconnect fields

- builds bridge config with reconnect fields
- Keep registration and polling config fields visible
   - Expected: config.dir equals `/repo`
   - Expected: config.maxSessions equals `4`
   - Expected: config.spawnMode equals `worktree`
   - Expected: config.workerType equals `claude_code`
   - Expected: config.reuseEnvironmentId equals `env_backend`
   - Expected: config.sessionTimeoutMs equals `defaultSessionTimeoutMs()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds bridge config with reconnect fields")
step("Keep registration and polling config fields visible")
val config = BridgeConfig.new("/repo", "host", "main", "https://git", 4, "worktree", "bridge_1", "claude_code", "env_client", "https://api", "wss://ingress").withReconnect("env_backend")
expect(config.dir).to_equal("/repo")
expect(config.maxSessions).to_equal(4)
expect(config.spawnMode).to_equal("worktree")
expect(config.workerType).to_equal("claude_code")
expect(config.reuseEnvironmentId).to_equal("env_backend")
expect(config.sessionTimeoutMs).to_equal(defaultSessionTimeoutMs())
```

</details>

#### models permission response and session handles

- models permission response and session handles
- Session handles expose kill, stdin, and access-token update operations
   - Expected: permission.kind equals `permissionResponseEventType()`
   - Expected: permission.subtype equals `permissionResponseSuccessSubtype()`
   - Expected: handle.stdin[0] equals `hello`
   - Expected: handle.accessToken equals `new`
   - Expected: handle.killed is true
   - Expected: handle.forceKilled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models permission response and session handles")
step("Session handles expose kill, stdin, and access-token update operations")
val permission = PermissionResponseEvent.success("req_1", "allow")
expect(permission.kind).to_equal(permissionResponseEventType())
expect(permission.subtype).to_equal(permissionResponseSuccessSubtype())
val handle = SessionHandle.new("cse_1", "old")
handle.writeStdin("hello")
handle.updateAccessToken("new")
handle.kill()
handle.forceKill()
expect(handle.stdin[0]).to_equal("hello")
expect(handle.accessToken).to_equal("new")
expect(handle.killed).to_equal(true)
expect(handle.forceKilled).to_equal(true)
```

</details>

#### models spawn options and logger surfaces

- models spawn options and logger surfaces
- CCR v2 spawn fields and logger method inventory match types.ts
   - Expected: opts.useCcrV2 is true
   - Expected: opts.workerEpoch equals `42`
   - Expected: sessionSpawnerMethod() equals `spawn`
   - Expected: logger.has("printBanner") is true
   - Expected: logger.has("updateSessionStatus") is true
   - Expected: logger.has("refreshDisplay") is true
   - Expected: logger.has("missing") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models spawn options and logger surfaces")
step("CCR v2 spawn fields and logger method inventory match types.ts")
val opts = SessionSpawnOpts.new("cse_1", "sdk", "jwt").ccrV2(42)
expect(opts.useCcrV2).to_equal(true)
expect(opts.workerEpoch).to_equal(42)
expect(sessionSpawnerMethod()).to_equal("spawn")
val logger = BridgeLoggerSurface.canonical()
expect(logger.has("printBanner")).to_equal(true)
expect(logger.has("updateSessionStatus")).to_equal(true)
expect(logger.has("refreshDisplay")).to_equal(true)
expect(logger.has("missing")).to_equal(false)
```

</details>

#### exports field names used across bridge modules

- exports field names used across bridge modules
- Shared names prevent drift in later slices
   - Expected: workerTypeClaudeCode() equals `claude_code`
   - Expected: workerTypeAssistant() equals `claude_code_assistant`
   - Expected: spawnModeSingleSession() equals `single-session`
   - Expected: spawnModeWorktree() equals `worktree`
   - Expected: spawnModeSameDir() equals `same-dir`
   - Expected: useCodeSessionsFieldName() equals `use_code_sessions`
   - Expected: sessionIngressTokenFieldName() equals `session_ingress_token`
   - Expected: apiBaseUrlFieldName() equals `api_base_url`
   - Expected: environmentIdFieldName() equals `environment_id`
   - Expected: environmentSecretFieldName() equals `environment_secret`
   - Expected: workerEpochFieldName() equals `workerEpoch`
   - Expected: sessionTimeoutFieldName() equals `sessionTimeoutMs`
   - Expected: bridgeMetadataWorkerTypeField() equals `metadata.worker_type`
   - Expected: bridgeConfigHasApiBaseUrl() is true
   - Expected: bridgeConfigHasSessionIngressUrl() is true
   - Expected: sessionHandleHasActivityRing() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports field names used across bridge modules")
step("Shared names prevent drift in later slices")
expect(workerTypeClaudeCode()).to_equal("claude_code")
expect(workerTypeAssistant()).to_equal("claude_code_assistant")
expect(spawnModeSingleSession()).to_equal("single-session")
expect(spawnModeWorktree()).to_equal("worktree")
expect(spawnModeSameDir()).to_equal("same-dir")
expect(useCodeSessionsFieldName()).to_equal("use_code_sessions")
expect(sessionIngressTokenFieldName()).to_equal("session_ingress_token")
expect(apiBaseUrlFieldName()).to_equal("api_base_url")
expect(environmentIdFieldName()).to_equal("environment_id")
expect(environmentSecretFieldName()).to_equal("environment_secret")
expect(workerEpochFieldName()).to_equal("workerEpoch")
expect(sessionTimeoutFieldName()).to_equal("sessionTimeoutMs")
expect(bridgeMetadataWorkerTypeField()).to_equal("metadata.worker_type")
expect(bridgeConfigHasApiBaseUrl()).to_equal(true)
expect(bridgeConfigHasSessionIngressUrl()).to_equal(true)
expect(sessionHandleHasActivityRing()).to_equal(true)
expect(bridgeApiClientMethods()).to_contain("heartbeatWork")
expect(sessionHandleMethods()).to_contain("updateAccessToken")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0051d8f8319c23522bca87bb369329db52c68b3a31f32dccdc3ce5e7133f2cdf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0051d8f8319c23522bca87bb369329db52c68b3a31f32dccdc3ce5e7133f2cdf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0051d8f8319c23522bca87bb369329db52c68b3a31f32dccdc3ce5e7133f2cdf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/bridge/types_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/bridge/types_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/bridge/types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/bridge/types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/bridge/types_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/bridge/types_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports bridge constants and enum values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/types_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds work response and secret DTOs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/types_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds bridge config with reconnect fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
