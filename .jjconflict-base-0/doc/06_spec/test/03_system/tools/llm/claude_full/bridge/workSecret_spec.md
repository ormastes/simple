# Claude Full Bridge Work Secret

> Checks work secret validation, session URL building, ID comparison, and worker registration parsing.

<!-- sdn-diagram:id=workSecret_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=workSecret_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

workSecret_spec -> std
workSecret_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=workSecret_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge Work Secret

Checks work secret validation, session URL building, ID comparison, and worker registration parsing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bridge/workSecret_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks work secret validation, session URL building, ID comparison, and worker registration parsing.

## Scenarios

### Claude full bridge work secret

#### validates decoded work secrets

- Accept version 1 with required session token and API base URL
   - Expected: ok.ok is true
   - Expected: ok.version equals `workSecretVersion()`
   - Expected: ok.sessionIngressToken equals `jwt`
   - Expected: ok.apiBaseUrl equals `https://api`
   - Expected: ok.useCodeSessions is true
   - Expected: decodeWorkSecret(2, "jwt", "https://api", false).error equals `Unsupported work secret version: 2`
   - Expected: decodeWorkSecretUnknownVersion().error equals `Unsupported work secret version: unknown`
   - Expected: decodeWorkSecret(1, "", "https://api", false).error equals `Invalid work secret: missing or empty session_ingress_token`
   - Expected: decodeWorkSecret(1, "jwt", "", false).error equals `Invalid work secret: missing api_base_url`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accept version 1 with required session token and API base URL")
val ok = decodeWorkSecret(1, "jwt", "https://api", true)
expect(ok.ok).to_equal(true)
expect(ok.version).to_equal(workSecretVersion())
expect(ok.sessionIngressToken).to_equal("jwt")
expect(ok.apiBaseUrl).to_equal("https://api")
expect(ok.useCodeSessions).to_equal(true)
expect(decodeWorkSecret(2, "jwt", "https://api", false).error).to_equal("Unsupported work secret version: 2")
expect(decodeWorkSecretUnknownVersion().error).to_equal("Unsupported work secret version: unknown")
expect(decodeWorkSecret(1, "", "https://api", false).error).to_equal("Invalid work secret: missing or empty session_ingress_token")
expect(decodeWorkSecret(1, "jwt", "", false).error).to_equal("Invalid work secret: missing api_base_url")
```

</details>

#### builds SDK websocket URLs

- Use ws/v2 for localhost and wss/v1 for production
   - Expected: buildSdkUrl("http://localhost:8080/", "cse_1") equals `ws://localhost:8080/v2/session_ingress/ws/cse_1`
   - Expected: buildSdkUrl("http://127.0.0.1:8080//", "cse_1") equals `ws://127.0.0.1:8080/v2/session_ingress/ws/cse_1`
   - Expected: buildSdkUrl("https://api.anthropic.com/", "cse_1") equals `wss://api.anthropic.com/v1/session_ingress/ws/cse_1`
   - Expected: stripHttpProtocol("https://api") equals `api`
   - Expected: trimTrailingSlashes("https://api///") equals `https://api`
   - Expected: isLocalhost("https://api") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use ws/v2 for localhost and wss/v1 for production")
expect(buildSdkUrl("http://localhost:8080/", "cse_1")).to_equal("ws://localhost:8080/v2/session_ingress/ws/cse_1")
expect(buildSdkUrl("http://127.0.0.1:8080//", "cse_1")).to_equal("ws://127.0.0.1:8080/v2/session_ingress/ws/cse_1")
expect(buildSdkUrl("https://api.anthropic.com/", "cse_1")).to_equal("wss://api.anthropic.com/v1/session_ingress/ws/cse_1")
expect(stripHttpProtocol("https://api")).to_equal("api")
expect(trimTrailingSlashes("https://api///")).to_equal("https://api")
expect(isLocalhost("https://api")).to_equal(false)
```

</details>

#### compares tagged session ids by UUID body

- Handle plain and staging tags without matching tiny suffixes
   - Expected: sameSessionId("cse_abcd", "session_abcd") is true
   - Expected: sameSessionId("cse_staging_abcd", "session_staging_abcd") is true
   - Expected: sameSessionId("cse_abc", "session_abc") is false
   - Expected: sameSessionId("bare", "bare") is true
   - Expected: afterLastUnderscore("session_staging_abcd") equals `abcd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Handle plain and staging tags without matching tiny suffixes")
expect(sameSessionId("cse_abcd", "session_abcd")).to_equal(true)
expect(sameSessionId("cse_staging_abcd", "session_staging_abcd")).to_equal(true)
expect(sameSessionId("cse_abc", "session_abc")).to_equal(false)
expect(sameSessionId("bare", "bare")).to_equal(true)
expect(afterLastUnderscore("session_staging_abcd")).to_equal("abcd")
```

</details>

#### builds CCR v2 session URLs and worker register requests

- Keep HTTP session URL separate from websocket ingress URL
   - Expected: buildCCRv2SdkUrl("https://api/", "cse_1") equals `https://api/v1/code/sessions/cse_1`
   - Expected: ccrV2SessionPath("cse_1") equals `/v1/code/sessions/cse_1`
   - Expected: sdkIngressPath("cse_1") equals `/session_ingress/ws/cse_1`
   - Expected: req.url equals `workerRegisterPath("https://api/v1/code/sessions/cse_1")`
   - Expected: req.Authorization equals `Bearer jwt`
   - Expected: req.Content_Type equals `application/json`
   - Expected: req.anthropic_version equals `anthropicVersion()`
   - Expected: req.timeoutMs equals `workerRegisterTimeoutMs()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep HTTP session URL separate from websocket ingress URL")
expect(buildCCRv2SdkUrl("https://api/", "cse_1")).to_equal("https://api/v1/code/sessions/cse_1")
expect(ccrV2SessionPath("cse_1")).to_equal("/v1/code/sessions/cse_1")
expect(sdkIngressPath("cse_1")).to_equal("/session_ingress/ws/cse_1")
val req = registerWorkerRequest("https://api/v1/code/sessions/cse_1", "jwt")
expect(req.url).to_equal(workerRegisterPath("https://api/v1/code/sessions/cse_1"))
expect(req.Authorization).to_equal("Bearer jwt")
expect(req.Content_Type).to_equal("application/json")
expect(req.anthropic_version).to_equal(anthropicVersion())
expect(req.timeoutMs).to_equal(workerRegisterTimeoutMs())
```

</details>

#### parses safe worker epochs

- Reject non-numeric and unsafe int64-as-JS-number responses
   - Expected: registerWorker("42").ok is true
   - Expected: registerWorker("42").workerEpoch equals `42`
   - Expected: registerWorkerNumber(42).workerEpoch equals `42`
   - Expected: registerWorker("").ok is false
   - Expected: registerWorker("nope").ok is false
   - Expected: registerWorker("9007199254740992").ok is false
   - Expected: registerWorkerNumber(maxSafeInteger() + 1).ok is false
   - Expected: parseSafeInteger("9007199254740991") equals `maxSafeInteger()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject non-numeric and unsafe int64-as-JS-number responses")
expect(registerWorker("42").ok).to_equal(true)
expect(registerWorker("42").workerEpoch).to_equal(42)
expect(registerWorkerNumber(42).workerEpoch).to_equal(42)
expect(registerWorker("").ok).to_equal(false)
expect(registerWorker("nope").ok).to_equal(false)
expect(registerWorker("9007199254740992").ok).to_equal(false)
expect(registerWorkerNumber(maxSafeInteger() + 1).ok).to_equal(false)
expect(parseSafeInteger("9007199254740991")).to_equal(maxSafeInteger())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
