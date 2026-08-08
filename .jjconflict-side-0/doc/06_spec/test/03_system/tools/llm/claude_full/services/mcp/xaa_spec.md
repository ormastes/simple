# Claude Full MCP XAA

> Checks the XAA / SEP-990 flow: URL normalization, token redaction, PRM and authorization-server validation, ID-JAG token exchange error semantics, JWT bearer grant behavior, auth method selection, and full orchestrator output.

<!-- sdn-diagram:id=xaa_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=xaa_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

xaa_spec -> std
xaa_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=xaa_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full MCP XAA

Checks the XAA / SEP-990 flow: URL normalization, token redaction, PRM and authorization-server validation, ID-JAG token exchange error semantics, JWT bearer grant behavior, auth method selection, and full orchestrator output.

## At a Glance

| Field | Value |
|-------|-------|
| Category | MCP |
| Status | Active |
| Requirements | N/A - strict llm_caret Claude CLI parity lane. |
| Plan | N/A - target selected from strict checker output. |
| Design | N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/xaa.ts`. |
| Research | N/A - upstream TypeScript file is the source reference. |
| Source | `test/03_system/tools/llm/claude_full/services/mcp/xaa_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Checks the XAA / SEP-990 flow: URL normalization, token redaction,
PRM and authorization-server validation, ID-JAG token exchange error semantics,
JWT bearer grant behavior, auth method selection, and full orchestrator output.

**Requirements:** N/A - strict llm_caret Claude CLI parity lane.
**Plan:** N/A - target selected from strict checker output.
**Design:** N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/xaa.ts`.
**Research:** N/A - upstream TypeScript file is the source reference.

## Scenarios

### Claude full MCP XAA

#### should create timeout fetch and normalize URLs

- Compose abort signal and strip trailing slash
   - Expected: fetch.timeoutMs equals `30000`
   - Expected: fetch.composedAbort is true
   - Expected: normalizeUrl("HTTPS://Example.com/") equals `https://Example.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compose abort signal and strip trailing slash")
val fetch = makeXaaFetch(true)
expect(fetch.timeoutMs).to_equal(30000)
expect(fetch.composedAbort).to_equal(true)
expect(normalizeUrl("HTTPS://Example.com/")).to_equal("https://Example.com")
```

</details>

#### should redact sensitive token fields

- Redact tokens from raw JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Redact tokens from raw JSON")
val redacted = redactTokens("{\"access_token\":\"a\",\"subject_token\":\"b\",\"client_secret\":\"c\"}")
expect(redacted).to_contain("\"access_token\":\"[REDACTED]\"")
expect(redacted).to_contain("\"subject_token\":\"[REDACTED]\"")
expect(redacted).to_contain("\"client_secret\":\"[REDACTED]\"")
```

</details>

#### should validate protected resource discovery

- Detect PRM resource mismatch
   - Expected: ok.authorizationServers[0] equals `https://as.example`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Detect PRM resource mismatch")
val ok = discoverProtectedResource("https://mcp.example/mcp", ProtectedResourceMetadata.new("https://mcp.example/mcp/", ["https://as.example"]))
expect(ok.authorizationServers[0]).to_equal("https://as.example")
val bad = discoverProtectedResource("https://mcp.example/mcp", ProtectedResourceMetadata.new("https://other.example", ["https://as.example"]))
expect(bad.resource).to_contain("ERROR: PRM resource mismatch")
```

</details>

#### should validate authorization server metadata

- Reject non-HTTPS token endpoint
   - Expected: ok.tokenEndpoint equals `https://as.example/token`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject non-HTTPS token endpoint")
val ok = discoverAuthorizationServer("https://as.example", AuthorizationServerMetadata.new("https://as.example/", "https://as.example/token"))
expect(ok.tokenEndpoint).to_equal("https://as.example/token")
val bad = discoverAuthorizationServer("https://as.example", AuthorizationServerMetadata.new("https://as.example", "http://as.example/token"))
expect(bad.issuer).to_contain("ERROR: refusing non-HTTPS")
```

</details>

#### should classify token exchange failures by clear-cache semantics

- Compare 4xx and 5xx token exchange failures
   - Expected: badGrant.error.shouldClearIdToken is true
   - Expected: outage.error.shouldClearIdToken is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare 4xx and 5xx token exchange failures")
val badGrant = requestJwtAuthorizationGrant(400, "{\"id_token\":\"secret\"}", TokenExchangeResponse.new("", "", 0, ""))
expect(badGrant.error.shouldClearIdToken).to_equal(true)
expect(badGrant.error.message).to_contain("[REDACTE")
val outage = requestJwtAuthorizationGrant(503, "down", TokenExchangeResponse.new("", "", 0, ""))
expect(outage.error.shouldClearIdToken).to_equal(false)
```

</details>

#### should require ID-JAG token type

- Reject unexpected issued_token_type
   - Expected: bad.error.name equals `XaaTokenExchangeError`
   - Expected: bad.error.shouldClearIdToken is true
   - Expected: ok.jwtAuthGrant equals `jag`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject unexpected issued_token_type")
val bad = requestJwtAuthorizationGrant(200, "", TokenExchangeResponse.new("jag", "wrong", 60, "read"))
expect(bad.error.name).to_equal("XaaTokenExchangeError")
expect(bad.error.shouldClearIdToken).to_equal(true)
val ok = requestJwtAuthorizationGrant(200, "", TokenExchangeResponse.new("jag", idJagTokenType(), 60, "read"))
expect(ok.jwtAuthGrant).to_equal("jag")
```

</details>

#### should exchange jwt bearer grants with default bearer token type

- Accept missing token_type as Bearer
   - Expected: token.tokenType equals `Bearer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accept missing token_type as Bearer")
val token = exchangeJwtAuthGrant(200, "", JwtBearerResponse.new("access", "", 300, "read", "refresh"), "client_secret_basic")
expect(token.tokenType).to_equal("Bearer")
val failed = exchangeJwtAuthGrant(500, "{\"assertion\":\"secret\"}", JwtBearerResponse.new("", "", 0, "", ""), "client_secret_post")
expect(failed.error).to_contain("[REDACTE")
```

</details>

#### should select AS auth method from metadata

- Prefer post only when basic is absent
   - Expected: selectAuthMethod(["client_secret_post"]) equals `client_secret_post`
   - Expected: selectAuthMethod(["client_secret_basic", "client_secret_post"]) equals `client_secret_basic`
   - Expected: selectAuthMethod([]) equals `client_secret_basic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prefer post only when basic is absent")
expect(selectAuthMethod(["client_secret_post"])).to_equal("client_secret_post")
expect(selectAuthMethod(["client_secret_basic", "client_secret_post"])).to_equal("client_secret_basic")
expect(selectAuthMethod([])).to_equal("client_secret_basic")
```

</details>

#### should perform full cross-app access flow

- Compose PRM, AS metadata, ID-JAG, and access token
- asMeta grantTypesSupported = [jwtBearerGrant
   - Expected: result.accessToken equals `access`
   - Expected: result.authorizationServerUrl equals `https://as.example`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compose PRM, AS metadata, ID-JAG, and access token")
val prm = ProtectedResourceMetadata.new("https://mcp.example/mcp", ["https://as.example"])
val asMeta = AuthorizationServerMetadata.new("https://as.example", "https://as.example/token")
asMeta.grantTypesSupported = [jwtBearerGrant()]
val config = XaaConfig.new("client", "secret", "idp-client", "id-token", "https://idp.example/token")
val result = performCrossAppAccess("https://mcp.example/mcp", config, prm, [asMeta], TokenExchangeResponse.new("jag", idJagTokenType(), 60, "read"), JwtBearerResponse.new("access", "", 300, "read", "refresh"))
expect(result.accessToken).to_equal("access")
expect(result.authorizationServerUrl).to_equal("https://as.example")
```

</details>

#### should expose source-backed constants

- Pin source surface
   - Expected: error.name equals `XaaTokenExchangeError`
   - Expected: xaaSourceLinesModeled() equals `511`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin source surface")
val error = XaaTokenExchangeError.new("bad", true)
expect(error.name).to_equal("XaaTokenExchangeError")
expect(tokenExchangeGrant()).to_contain("token-exchange")
expect(xaaSourceLinesModeled()).to_equal(511)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [N/A - strict llm_caret Claude CLI parity lane.](N/A - strict llm_caret Claude CLI parity lane.)
- **Plan:** [N/A - target selected from strict checker output.](N/A - target selected from strict checker output.)
- **Design:** [N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/xaa.ts`.](N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/xaa.ts`.)
- **Research:** [N/A - upstream TypeScript file is the source reference.](N/A - upstream TypeScript file is the source reference.)


</details>
