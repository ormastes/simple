# Claude Full OAuth Service

> Checks OAuthService authorization-code PKCE flow behavior.

<!-- sdn-diagram:id=index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

index_spec -> std
index_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full OAuth Service

Checks OAuthService authorization-code PKCE flow behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/services/oauth/index_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks OAuthService authorization-code PKCE flow behavior.

## Scenarios

### Claude full OAuthService

#### should create verifier and build manual and automatic URLs

- Start automatic flow
   - Expected: result.openedBrowser is true
   - Expected: result.handlerReceivedAutomaticUrl is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Start automatic flow")
val service = OAuthService.new()
val response = OAuthTokenExchangeResponse.new("access", "refresh", 10, "read user")
val result = service.startOAuthFlow(OAuthFlowOptions.defaults(), "CODE", response, "pro", "tier1", "profile")
expect(result.manualFlowUrl).to_contain("manual=true")
expect(result.automaticFlowUrl).to_contain("manual=false")
expect(result.openedBrowser).to_equal(true)
expect(result.handlerReceivedAutomaticUrl).to_equal(false)
```

</details>

#### should hand both URLs to caller when browser open is skipped

- Start SDK-controlled flow
- var options = OAuthFlowOptions defaults
   - Expected: result.openedBrowser is false
   - Expected: result.handlerReceivedAutomaticUrl is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Start SDK-controlled flow")
val service = OAuthService.new()
var options = OAuthFlowOptions.defaults()
options.skipBrowserOpen = true
options.loginWithClaudeAi = true
options.orgUUID = "org"
val result = service.startOAuthFlow(options, "CODE", OAuthTokenExchangeResponse.new("a", "r", 1, "claude"), "sub", "tier", "")
expect(result.openedBrowser).to_equal(false)
expect(result.handlerReceivedAutomaticUrl).to_equal(true)
expect(result.manualFlowUrl).to_contain("claude_ai=true")
expect(result.manualFlowUrl).to_contain("org=org")
```

</details>

#### should format token responses with scopes and account

- Format OAuth tokens
- var response = OAuthTokenExchangeResponse new
   - Expected: tokens.accessToken equals `access`
   - Expected: tokens.expiresAt equals `160000`
   - Expected: tokens.scopes equals `["read", "write"]`
   - Expected: tokens.tokenAccountUuid equals `acct`
   - Expected: tokens.organizationUuid equals `org`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Format OAuth tokens")
val service = OAuthService.new()
var response = OAuthTokenExchangeResponse.new("access", "refresh", 60, "read write")
response.accountUuid = "acct"
response.accountEmail = "a@example.com"
response.organizationUuid = "org"
val tokens = service.formatTokens(response, "max", "tier2", "raw")
expect(tokens.accessToken).to_equal("access")
expect(tokens.expiresAt).to_equal(160000)
expect(tokens.scopes).to_equal(["read", "write"])
expect(tokens.tokenAccountUuid).to_equal("acct")
expect(tokens.organizationUuid).to_equal("org")
```

</details>

#### should resolve manual authorization code and close listener

- Use manual pasted code
- service authCodeListener = AuthCodeListener new
- service handleManualAuthCodeInput
   - Expected: service.manualAuthorizationCode equals `MANUAL`
   - Expected: service.manualAuthCodeResolverReady is false
   - Expected: service.authCodeListener.closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use manual pasted code")
val service = OAuthService.new()
service.hasListener = true
service.authCodeListener = AuthCodeListener.new("/callback")
service.manualAuthCodeResolverReady = true
service.handleManualAuthCodeInput("MANUAL", "state")
expect(service.manualAuthorizationCode).to_equal("MANUAL")
expect(service.manualAuthCodeResolverReady).to_equal(false)
expect(service.authCodeListener.closed).to_equal(true)
```

</details>

#### should log automatic auth and redirect on successful automatic flow

- Complete automatic flow
   - Expected: result.automaticFlow is true
   - Expected: result.logs[0] equals `tengu_oauth_auth_code_received:true`
   - Expected: service.cleanedUp is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Complete automatic flow")
val service = OAuthService.new()
val result = service.startOAuthFlow(OAuthFlowOptions.defaults(), "AUTO", OAuthTokenExchangeResponse.new("access", "refresh", 10, "read:user"), "pro", "tier", "")
expect(result.automaticFlow).to_equal(true)
expect(result.logs[0]).to_equal("tengu_oauth_auth_code_received:true")
expect(result.logs[1]).to_contain("tengu_oauth_automatic_redirect")
expect(service.cleanedUp).to_equal(true)
```

</details>

#### should cleanup listener and manual resolver

- Cleanup resources
- service authCodeListener = AuthCodeListener new
- service cleanup
   - Expected: service.manualAuthCodeResolverReady is false
   - Expected: service.authCodeListener.closed is true
   - Expected: service.cleanedUp is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Cleanup resources")
val service = OAuthService.new()
service.hasListener = true
service.authCodeListener = AuthCodeListener.new("/callback")
service.manualAuthCodeResolverReady = true
service.cleanup()
expect(service.manualAuthCodeResolverReady).to_equal(false)
expect(service.authCodeListener.closed).to_equal(true)
expect(service.cleanedUp).to_equal(true)
```

</details>

#### should expose source-backed helpers

- Pin helper surface
   - Expected: generateCodeVerifier() equals `verifier`
   - Expected: generateCodeChallenge("v") equals `challenge:v`
   - Expected: parseScopes("a b") equals `["a", "b"]`
   - Expected: oauthServiceSourceLinesModeled() equals `198`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin helper surface")
expect(generateCodeVerifier()).to_equal("verifier")
expect(generateCodeChallenge("v")).to_equal("challenge:v")
expect(parseScopes("a b")).to_equal(["a", "b"])
expect(oauthServiceSourceLinesModeled()).to_equal(198)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
