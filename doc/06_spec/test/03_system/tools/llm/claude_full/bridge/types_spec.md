# Claude Full Bridge Types

> Checks bridge protocol constants and DTO surfaces mirrored from types.ts.

<!-- sdn-diagram:id=types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

types_spec -> std
types_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks bridge protocol constants and DTO surfaces mirrored from types.ts.

## Scenarios

### Claude full bridge types

#### exports bridge constants and enum values

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

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Model environment work payloads and decoded secrets
   - Expected: work.kind equals `work`
   - Expected: work.data.kind equals `session`
   - Expected: work.environmentId equals `env_1`
   - Expected: secret.sessionIngressToken equals `jwt`
   - Expected: secret.useCodeSessions is true
   - Expected: secret.hasMcpConfig is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Keep registration and polling config fields visible
   - Expected: config.dir equals `/repo`
   - Expected: config.maxSessions equals `4`
   - Expected: config.spawnMode equals `worktree`
   - Expected: config.workerType equals `claude_code`
   - Expected: config.reuseEnvironmentId equals `env_backend`
   - Expected: config.sessionTimeoutMs equals `defaultSessionTimeoutMs()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Session handles expose kill, stdin, and access-token update operations
   - Expected: permission.kind equals `permissionResponseEventType()`
   - Expected: permission.subtype equals `permissionResponseSuccessSubtype()`
- handle writeStdin
- handle updateAccessToken
- handle kill
- handle forceKill
   - Expected: handle.stdin[0] equals `hello`
   - Expected: handle.accessToken equals `new`
   - Expected: handle.killed is true
   - Expected: handle.forceKilled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
