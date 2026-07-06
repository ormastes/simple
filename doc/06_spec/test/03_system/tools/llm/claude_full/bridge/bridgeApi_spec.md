# Claude Full Bridge API

> Mirrors bridge API request construction, OAuth retry, status mapping, and ID validation.

<!-- sdn-diagram:id=bridgeApi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bridgeApi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bridgeApi_spec -> std
bridgeApi_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bridgeApi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge API

Mirrors bridge API request construction, OAuth retry, status mapping, and ID validation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bridge/bridgeApi_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors bridge API request construction, OAuth retry, status mapping, and ID validation.

## Scenarios

### Claude full bridge api

#### validates bridge ids with the TypeScript allowlist

- Allow alphanumeric, underscore, and dash path segments
   - Expected: validateBridgeId("env_ABC-123", "environmentId") equals `env_ABC-123`
   - Expected: validateBridgeIdError("../../admin", "environmentId") equals `Invalid environmentId: contains unsafe characters`
   - Expected: validateBridgeIdError("env/123", "environmentId") equals `Invalid environmentId: contains unsafe characters`
   - Expected: validateBridgeId("", "environmentId") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Allow alphanumeric, underscore, and dash path segments")
expect(validateBridgeId("env_ABC-123", "environmentId")).to_equal("env_ABC-123")
expect(validateBridgeIdError("../../admin", "environmentId")).to_equal("Invalid environmentId: contains unsafe characters")
expect(validateBridgeIdError("env/123", "environmentId")).to_equal("Invalid environmentId: contains unsafe characters")
expect(validateBridgeId("", "environmentId")).to_equal("")
```

</details>

#### builds registration request body and headers

- Capture OAuth JSON POST shape without live HTTP
   - Expected: result.ok is true
   - Expected: result.requests[0].method equals `POST`
   - Expected: result.requests[0].url equals `https://api/v1/environments/bridge`
   - Expected: result.requests[0].timeoutMs equals `registrationTimeoutMs()`
   - Expected: result.requests[0].headers.Authorization equals `Bearer tok`
   - Expected: result.requests[0].headers.anthropic_beta equals `betaHeader()`
   - Expected: result.requests[0].headers.X_Trusted_Device_Token equals `trusted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture OAuth JSON POST shape without live HTTP")
val deps = BridgeApiDeps.new("https://api", "tok", "1.2.3").withTrustedDeviceToken("trusted")
val client = createBridgeApiClient(deps)
val config = BridgeConfig.new("bridge_1", "host", "/repo", "main", "https://git", 4, "assistant", "env_old")
val result = client.registerBridgeEnvironment(config, BridgeApiResponse.ok(200, "env_new"), BridgeApiResponse.empty(204))
expect(result.ok).to_equal(true)
expect(result.requests[0].method).to_equal("POST")
expect(result.requests[0].url).to_equal("https://api/v1/environments/bridge")
expect(result.requests[0].timeoutMs).to_equal(registrationTimeoutMs())
expect(result.requests[0].headers.Authorization).to_equal("Bearer tok")
expect(result.requests[0].headers.anthropic_beta).to_equal(betaHeader())
expect(result.requests[0].headers.X_Trusted_Device_Token).to_equal("trusted")
expect(result.requests[0].body).to_contain("\"max_sessions\":4")
expect(result.requests[0].body).to_contain("\"worker_type\":\"assistant\"")
expect(result.requests[0].body).to_contain("\"environment_id\":\"env_old\"")
```

</details>

#### retries OAuth requests once after a 401 refresh

- First request uses stale token and retry uses refreshed token
   - Expected: result.ok is true
   - Expected: result.requests.len() equals `2`
   - Expected: result.requests[0].headers.Authorization equals `Bearer old`
   - Expected: result.requests[1].headers.Authorization equals `Bearer new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("First request uses stale token and retry uses refreshed token")
val deps = BridgeApiDeps.new("https://api", "old", "1.2.3").withRefresh("new", true)
val client = createBridgeApiClient(deps)
val config = BridgeConfig.new("bridge_1", "host", "/repo", "main", "https://git", 2, "assistant", "")
val result = client.registerBridgeEnvironment(config, BridgeApiResponse.failed(401, "expired"), BridgeApiResponse.ok(204, "env"))
expect(result.ok).to_equal(true)
expect(result.requests.len()).to_equal(2)
expect(result.requests[0].headers.Authorization).to_equal("Bearer old")
expect(result.requests[1].headers.Authorization).to_equal("Bearer new")
```

</details>

#### maps fatal authentication and permission statuses

- 401 includes login instructions; 403/410 preserve expiry semantics
   - Expected: auth.ok is false
   - Expected: auth.fatal.status equals `401`
   - Expected: expired.fatal.status equals `403`
   - Expected: expired.fatal.isExpired() is true
   - Expected: gone.fatal.errorType equals `environment_expired`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("401 includes login instructions; 403/410 preserve expiry semantics")
val client = createBridgeApiClient(BridgeApiDeps.new("https://api", "tok", "1.2.3"))
val auth = client.deregisterEnvironment("env_1", BridgeApiResponse.failed(401, "bad token"), BridgeApiResponse.empty(204))
expect(auth.ok).to_equal(false)
expect(auth.fatal.status).to_equal(401)
expect(auth.fatal.message).to_contain(bridgeLoginInstruction())
val expired = client.deregisterEnvironment("env_1", BridgeApiResponse.typed(403, "", "environment_lifetime_expired"), BridgeApiResponse.empty(204))
expect(expired.fatal.status).to_equal(403)
expect(expired.fatal.isExpired()).to_equal(true)
val gone = client.deregisterEnvironment("env_1", BridgeApiResponse.empty(410), BridgeApiResponse.empty(204))
expect(gone.fatal.errorType).to_equal("environment_expired")
```

</details>

#### maps nonfatal rate limit and server errors

- 429 stays retryable and 500 includes detail
   - Expected: limited.ok is false
   - Expected: limited.errorMessage equals `ArchiveSession: Rate limited (429). Polling too frequently.`
   - Expected: failed.errorMessage equals `ArchiveSession: Failed with status 500: down`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("429 stays retryable and 500 includes detail")
val client = createBridgeApiClient(BridgeApiDeps.new("https://api", "tok", "1.2.3"))
val limited = client.archiveSession("cse_1", BridgeApiResponse.empty(429), BridgeApiResponse.empty(204))
expect(limited.ok).to_equal(false)
expect(limited.errorMessage).to_equal("ArchiveSession: Rate limited (429). Polling too frequently.")
val failed = client.archiveSession("cse_1", BridgeApiResponse.failed(500, "down"), BridgeApiResponse.empty(204))
expect(failed.errorMessage).to_equal("ArchiveSession: Failed with status 500: down")
```

</details>

#### tracks empty polls and resets when work arrives

- Poll request includes optional reclaim parameter
   - Expected: empty.hasWork is false
   - Expected: empty.emptyPolls equals `1`
   - Expected: empty.call.requests[0].params equals `reclaim_older_than_ms=5000`
   - Expected: work.hasWork is true
   - Expected: work.work.id equals `work_1`
   - Expected: client.consecutiveEmptyPolls equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Poll request includes optional reclaim parameter")
val client = createBridgeApiClient(BridgeApiDeps.new("https://api", "tok", "1.2.3"))
val empty = client.pollForWork("env_1", "secret", 5000, BridgeApiResponse.empty(204))
expect(empty.hasWork).to_equal(false)
expect(empty.emptyPolls).to_equal(1)
expect(empty.call.requests[0].params).to_equal("reclaim_older_than_ms=5000")
expect(client.logs[0]).to_contain("no work")
val work = client.pollForWork("env_1", "secret", -1, BridgeApiResponse.ok(200, "work_1"))
expect(work.hasWork).to_equal(true)
expect(work.work.id).to_equal("work_1")
expect(client.consecutiveEmptyPolls).to_equal(0)
```

</details>

#### builds remaining endpoint request shapes

- Ack, reconnect, heartbeat, archive, and session events mirror bridgeApi.ts
   - Expected: ack.requests[0].url equals `https://api/v1/environments/env_1/work/work_1/ack`
   - Expected: stop.requests[0].body equals `{"force":true}`
   - Expected: reconnect.requests[0].body equals `{"session_id":"cse_1"}`
   - Expected: heartbeat.leaseExtended is true
   - Expected: archive.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Ack, reconnect, heartbeat, archive, and session events mirror bridgeApi.ts")
val client = createBridgeApiClient(BridgeApiDeps.new("https://api", "tok", "1.2.3"))
val ack = client.acknowledgeWork("env_1", "work_1", "session", BridgeApiResponse.empty(204))
expect(ack.requests[0].url).to_equal("https://api/v1/environments/env_1/work/work_1/ack")
val stop = client.stopWork("env_1", "work_1", true, BridgeApiResponse.empty(204), BridgeApiResponse.empty(204))
expect(stop.requests[0].body).to_equal("{\"force\":true}")
val reconnect = client.reconnectSession("env_1", "cse_1", BridgeApiResponse.empty(204), BridgeApiResponse.empty(204))
expect(reconnect.requests[0].body).to_equal("{\"session_id\":\"cse_1\"}")
val heartbeat = client.heartbeatWork("env_1", "work_1", "session", BridgeApiResponse.ok(200, "extended"))
expect(heartbeat.leaseExtended).to_equal(true)
val archive = client.archiveSession("cse_1", BridgeApiResponse.empty(409), BridgeApiResponse.empty(204))
expect(archive.ok).to_equal(true)
val permissionEvent = client.sendPermissionResponseEvent("cse_1", "{\"type\":\"permission_response\"}", "session", BridgeApiResponse.empty(204))
expect(permissionEvent.requests[0].body).to_contain("\"permission_response\"")
```

</details>

#### identifies suppressible 403 permission errors

- Only selected 403 scope failures are hidden from users
   - Expected: isSuppressible403(BridgeFatalError.new("missing external_poll_sessions", 403, "")) is true
   - Expected: isSuppressible403(BridgeFatalError.new("missing environments:manage", 403, "")) is true
   - Expected: isSuppressible403(BridgeFatalError.new("auth", 401, "")) is false
   - Expected: isExpiredErrorType("environment_lifetime_expired") is true
   - Expected: isExpiredErrorType("permission_denied") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Only selected 403 scope failures are hidden from users")
expect(isSuppressible403(BridgeFatalError.new("missing external_poll_sessions", 403, ""))).to_equal(true)
expect(isSuppressible403(BridgeFatalError.new("missing environments:manage", 403, ""))).to_equal(true)
expect(isSuppressible403(BridgeFatalError.new("auth", 401, ""))).to_equal(false)
expect(isExpiredErrorType("environment_lifetime_expired")).to_equal(true)
expect(isExpiredErrorType("permission_denied")).to_equal(false)
```

</details>

#### exports endpoint and status constants

- Keep bridge path helpers and header constants source-backed
   - Expected: registrationPath("https://api") equals `https://api/v1/environments/bridge`
   - Expected: pollPath("https://api", "env") equals `https://api/v1/environments/env/work/poll`
   - Expected: acknowledgePath("https://api", "env", "work") equals `https://api/v1/environments/env/work/work/ack`
   - Expected: stopPath("https://api", "env", "work") equals `https://api/v1/environments/env/work/work/stop`
   - Expected: heartbeatPath("https://api", "env", "work") equals `https://api/v1/environments/env/work/work/heartbeat`
   - Expected: deregisterPath("https://api", "env") equals `https://api/v1/environments/bridge/env`
   - Expected: archivePath("https://api", "cse") equals `https://api/v1/sessions/cse/archive`
   - Expected: reconnectPath("https://api", "env") equals `https://api/v1/environments/env/bridge/reconnect`
   - Expected: sessionEventsPath("https://api", "cse") equals `https://api/v1/sessions/cse/events`
   - Expected: validateStatusForAxios(499) is true
   - Expected: validateStatusForAxios(500) is false
   - Expected: bridgeSuccessStatus(204) is true
   - Expected: archiveAlreadyArchivedStatus(409) is true
   - Expected: anthropicVersion() equals `2023-06-01`
   - Expected: bridgeApiRetryLimit() equals `1`
   - Expected: bridgeApiEmptyPollDebugInterval() equals `100`
   - Expected: trustedDeviceHeaderName() equals `X-Trusted-Device-Token`
   - Expected: betaHeaderName() equals `anthropic-beta`
   - Expected: runnerVersionHeaderName() equals `x-environment-runner-version`
   - Expected: contentTypeHeaderName() equals `Content-Type`
   - Expected: authorizationHeaderName() equals `Authorization`
   - Expected: registrationDebugLine("bridge_1") equals `[bridge:api] POST /v1/environments/bridge bridgeId=bridge_1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep bridge path helpers and header constants source-backed")
expect(registrationPath("https://api")).to_equal("https://api/v1/environments/bridge")
expect(pollPath("https://api", "env")).to_equal("https://api/v1/environments/env/work/poll")
expect(acknowledgePath("https://api", "env", "work")).to_equal("https://api/v1/environments/env/work/work/ack")
expect(stopPath("https://api", "env", "work")).to_equal("https://api/v1/environments/env/work/work/stop")
expect(heartbeatPath("https://api", "env", "work")).to_equal("https://api/v1/environments/env/work/work/heartbeat")
expect(deregisterPath("https://api", "env")).to_equal("https://api/v1/environments/bridge/env")
expect(archivePath("https://api", "cse")).to_equal("https://api/v1/sessions/cse/archive")
expect(reconnectPath("https://api", "env")).to_equal("https://api/v1/environments/env/bridge/reconnect")
expect(sessionEventsPath("https://api", "cse")).to_equal("https://api/v1/sessions/cse/events")
expect(validateStatusForAxios(499)).to_equal(true)
expect(validateStatusForAxios(500)).to_equal(false)
expect(bridgeSuccessStatus(204)).to_equal(true)
expect(archiveAlreadyArchivedStatus(409)).to_equal(true)
expect(anthropicVersion()).to_equal("2023-06-01")
expect(bridgeApiRetryLimit()).to_equal(1)
expect(bridgeApiEmptyPollDebugInterval()).to_equal(100)
expect(trustedDeviceHeaderName()).to_equal("X-Trusted-Device-Token")
expect(betaHeaderName()).to_equal("anthropic-beta")
expect(runnerVersionHeaderName()).to_equal("x-environment-runner-version")
expect(contentTypeHeaderName()).to_equal("Content-Type")
expect(authorizationHeaderName()).to_equal("Authorization")
expect(registrationDebugLine("bridge_1")).to_equal("[bridge:api] POST /v1/environments/bridge bridgeId=bridge_1")
expect(pollEmptyDebugLine(204, 1)).to_contain("no work")
expect(oauth401RefreshDebugLine("Registration")).to_contain("attempting token refresh")
expect(oauthRetryDebugLine("Registration")).to_contain("retrying request")
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
