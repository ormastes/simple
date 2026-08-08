# Claude Full Create Direct Connect Session

> Checks direct-connect request construction and error handling.

<!-- sdn-diagram:id=createDirectConnectSession_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=createDirectConnectSession_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

createDirectConnectSession_spec -> std
createDirectConnectSession_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=createDirectConnectSession_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Create Direct Connect Session

Checks direct-connect request construction and error handling.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/server/createDirectConnectSession_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks direct-connect request construction and error handling.

## Scenarios

### Claude full createDirectConnectSession

#### should construct DirectConnectError with stable name

- Create a direct-connect error
   - Expected: error.name equals `DirectConnectError`
   - Expected: error.message equals `bad`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a direct-connect error")
val error = DirectConnectError.new("bad")
expect(error.name).to_equal("DirectConnectError")
expect(error.message).to_equal("bad")
```

</details>

#### should create successful direct connect config

- Create session from a valid response
   - Expected: result.ok is true
   - Expected: result.requestUrl equals `https://server/sessions`
   - Expected: result.requestBody equals `{"cwd":"/repo","dangerously_skip_permissions":true}`
   - Expected: result.authorizationHeader equals `Bearer tok`
   - Expected: result.config.sessionId equals `sess-1`
   - Expected: result.config.wsUrl equals `wss://server/ws`
   - Expected: result.workDir equals `/work`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create session from a valid response")
val request = directConnectRequest("https://server", "tok", "/repo", true)
val result = createDirectConnectSession(request, true, true, 200, "OK", "sess-1", "wss://server/ws", "/work", true, "")
expect(result.ok).to_equal(true)
expect(result.requestUrl).to_equal("https://server/sessions")
expect(result.requestBody).to_equal("{\"cwd\":\"/repo\",\"dangerously_skip_permissions\":true}")
expect(result.authorizationHeader).to_equal("Bearer tok")
expect(result.config.sessionId).to_equal("sess-1")
expect(result.config.wsUrl).to_equal("wss://server/ws")
expect(result.workDir).to_equal("/work")
```

</details>

#### should omit auth and skip-permission fields when absent

- Create request without optional fields
   - Expected: result.requestBody equals `{"cwd":"/repo"}`
   - Expected: result.authorizationHeader equals ``
   - Expected: result.config.authToken equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create request without optional fields")
val request = directConnectRequest("http://localhost:8000", "", "/repo", false)
val result = createDirectConnectSession(request, true, true, 201, "Created", "s", "ws://x", "", true, "")
expect(result.requestBody).to_equal("{\"cwd\":\"/repo\"}")
expect(result.authorizationHeader).to_equal("")
expect(result.config.authToken).to_equal("")
```

</details>

#### should fail on network errors

- Simulate fetch failure
   - Expected: result.ok is false
   - Expected: error.message equals `Failed to connect to server at https://server: ECONNREFUSED`
   - Expected: "missing" equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Simulate fetch failure")
val request = directConnectRequest("https://server", "", "/repo", false)
val result = createDirectConnectSession(request, false, false, 0, "", "", "", "", false, "ECONNREFUSED")
expect(result.ok).to_equal(false)
if val Some(error) = result.error:
    expect(error.message).to_equal("Failed to connect to server at https://server: ECONNREFUSED")
else:
    expect("missing").to_equal("error")
```

</details>

#### should fail on non-ok HTTP responses

- Simulate HTTP failure
   - Expected: result.ok is false
   - Expected: error.message equals `Failed to create session: 500 Server Error`
   - Expected: "missing" equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Simulate HTTP failure")
val request = directConnectRequest("https://server", "", "/repo", false)
val result = createDirectConnectSession(request, true, false, 500, "Server Error", "", "", "", false, "")
expect(result.ok).to_equal(false)
if val Some(error) = result.error:
    expect(error.message).to_equal("Failed to create session: 500 Server Error")
else:
    expect("missing").to_equal("error")
```

</details>

#### should fail on invalid response schema

- Simulate invalid response
   - Expected: result.ok is false
   - Expected: error.message equals `Invalid session response: schema validation failed`
   - Expected: "missing" equals `error`
   - Expected: createDirectConnectSessionSourceLinesModeled() equals `88`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Simulate invalid response")
val request = directConnectRequest("https://server", "", "/repo", false)
val result = createDirectConnectSession(request, true, true, 200, "OK", "", "", "", false, "")
expect(result.ok).to_equal(false)
if val Some(error) = result.error:
    expect(error.message).to_equal("Invalid session response: schema validation failed")
else:
    expect("missing").to_equal("error")
expect(createDirectConnectSessionSourceLinesModeled()).to_equal(88)
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
