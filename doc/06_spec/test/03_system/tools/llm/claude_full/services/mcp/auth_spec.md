# Claude Full MCP Auth

> Checks deterministic parity for the Claude CLI MCP OAuth auth surface: sensitive URL redaction, OAuth error normalization, server-keyed token/config storage, XAA discovery bypass, cancellation class, step-up scope detection, `ClaudeAuthProvider` token behavior, client secret helpers, and scope extraction.

<!-- sdn-diagram:id=auth_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=auth_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

auth_spec -> std
auth_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=auth_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full MCP Auth

Checks deterministic parity for the Claude CLI MCP OAuth auth surface: sensitive URL redaction, OAuth error normalization, server-keyed token/config storage, XAA discovery bypass, cancellation class, step-up scope detection, `ClaudeAuthProvider` token behavior, client secret helpers, and scope extraction.

## At a Glance

| Field | Value |
|-------|-------|
| Category | MCP |
| Status | Active |
| Requirements | N/A - strict llm_caret Claude CLI parity lane. |
| Plan | N/A - target selected from strict checker output. |
| Design | N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/auth.ts`. |
| Research | N/A - upstream TypeScript file is the source reference. |
| Source | `test/03_system/tools/llm/claude_full/services/mcp/auth_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Checks deterministic parity for the Claude CLI MCP OAuth auth surface: sensitive
URL redaction, OAuth error normalization, server-keyed token/config storage,
XAA discovery bypass, cancellation class, step-up scope detection,
`ClaudeAuthProvider` token behavior, client secret helpers, and scope extraction.

**Requirements:** N/A - strict llm_caret Claude CLI parity lane.
**Plan:** N/A - target selected from strict checker output.
**Design:** N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/auth.ts`.
**Research:** N/A - upstream TypeScript file is the source reference.

## Scenarios

### Claude full MCP auth

#### should redact sensitive OAuth URL params

- Redact state, code, and verifier-like params


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Redact state, code, and verifier-like params")
val redacted = redactSensitiveUrlParams("https://a/cb?state=s&code=c&safe=ok&nonce=n")
expect(redacted).to_contain("state=[REDACTED]")
expect(redacted).to_contain("code=[REDACTED]")
expect(redacted).to_contain("nonce=[REDACTED]")
expect(redacted).to_contain("safe=ok")
```

</details>

#### should normalize OAuth error bodies returned with 2xx status

- Rewrite nonstandard invalid grant aliases
   - Expected: response.status equals `400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Rewrite nonstandard invalid grant aliases")
val response = normalizeOAuthErrorBody(AuthResponse.new(200, "{\"error\":\"expired_refresh_token\"}"))
expect(response.status).to_equal(400)
expect(response.body).to_contain("invalid_grant")
```

</details>

#### should build server keys and detect discovery without token

- Use config material in server key
- storage discoveryKeys push
   - Expected: hasMcpDiscoveryButNoToken(storage, "srv", config, false) is true
   - Expected: hasMcpDiscoveryButNoToken(storage, "srv", config, true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use config material in server key")
val storage = AuthStorage.new()
val config = McpServerConfig.new("http", "https://mcp.example/path")
val key = getServerKey("srv", config)
storage.discoveryKeys.push(key)
expect(key).to_contain("srv|http|https://mcp.example/path")
expect(hasMcpDiscoveryButNoToken(storage, "srv", config, false)).to_equal(true)
config.oauthXaa = true
expect(hasMcpDiscoveryButNoToken(storage, "srv", config, true)).to_equal(false)
```

</details>

#### should expose cancellation and metadata discovery fallback

- Create cancellation error and fallback metadata
   - Expected: err.name equals `AuthenticationCancelledError`
   - Expected: fetchAuthServerMetadata("srv", "https://mcp.example/path", false) equals `legacy-metadata:/path`
   - Expected: fetchAuthServerMetadata("srv", "https://mcp.example/", false) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create cancellation error and fallback metadata")
val err = abort()
expect(err.name).to_equal("AuthenticationCancelledError")
expect(fetchAuthServerMetadata("srv", "https://mcp.example/path", false)).to_equal("legacy-metadata:/path")
expect(fetchAuthServerMetadata("srv", "https://mcp.example/", false)).to_equal("")
```

</details>

#### should key credential storage consistently

- Read client secret and token by server key
   - Expected: getMcpClientConfig(storage, "srv", config) equals `secret`
   - Expected: storage.getToken(key).accessToken equals `access`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read client secret and token by server key")
val config = McpServerConfig.new("sse", "https://mcp.example/sse")
val key = getServerKey("srv", config)
val storage = AuthStorage(tokenKeys: [key], tokens: [OAuthTokens.new("access", "refresh", 1000, "read")], clientInfoKeys: [], clientInfos: [], clientConfigKeys: [key], clientSecrets: ["secret"], discoveryKeys: [], updates: [])
expect(getMcpClientConfig(storage, "srv", config)).to_equal("secret")
expect(storage.getToken(key).accessToken).to_equal("access")
```

</details>

#### should provide client metadata and client information

- Use stored client info before configured client id
- provider setMetadata
- provider saveClientInformation
   - Expected: provider.clientInformation().clientId equals `stored`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use stored client info before configured client id")
val storage = AuthStorage.new()
val config = McpServerConfig.new("http", "https://mcp.example")
val provider = ClaudeAuthProvider.new("srv", config, "http://localhost/callback", storage)
val metadata = OAuthMetadata.new()
metadata.scope = "read write"
provider.setMetadata(metadata)
expect(provider.clientMetadata()).to_contain("scope=read write")
provider.saveClientInformation(OAuthClientInfo.new("stored", "stored-secret"))
expect(provider.clientInformation().clientId).to_equal("stored")
```

</details>

#### should omit refresh token when step-up scope is pending

- Mark step-up after insufficient_scope response
- storage setToken
   - Expected: wwwAuthScope(response.wwwAuthenticate) equals `read write`
- provider markStepUpPending
   - Expected: provider.pendingStepUpScope equals `read write`
   - Expected: tokens.refreshToken equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Mark step-up after insufficient_scope response")
val storage = AuthStorage.new()
val config = McpServerConfig.new("http", "https://mcp.example")
val provider = ClaudeAuthProvider.new("srv", config, "http://localhost/callback", storage)
provider.nowMs = 1000
storage.setToken(getServerKey("srv", config), OAuthTokens.new("access", "refresh", 1000000, "read"))
val response = AuthResponse(status: 403, body: "", wwwAuthenticate: "Bearer error=\"insufficient_scope\", scope=\"read write\"")
expect(wwwAuthScope(response.wwwAuthenticate)).to_equal("read write")
provider.markStepUpPending(wwwAuthScope(response.wwwAuthenticate))
val tokens = provider.tokens()
expect(provider.pendingStepUpScope).to_equal("read write")
expect(tokens.refreshToken).to_equal("")
```

</details>

#### should run XAA auth only for cached XAA-capable servers

- Silent exchange with cached id token
   - Expected: token.accessToken equals `xaa-access`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Silent exchange with cached id token")
val storage = AuthStorage.new()
val config = McpServerConfig.new("http", "https://mcp.example")
config.oauthXaa = true
val provider = ClaudeAuthProvider.new("srv", config, "http://localhost/callback", storage)
val token = performMCPXaaAuth(provider, true)
expect(token.accessToken).to_equal("xaa-access")
```

</details>

#### should handle authorization code state and client secret input

- Resolve OAuth redirect and secret helpers
   - Expected: performMCPOAuthFlow(provider, "code", state) equals `token_exchange`
   - Expected: authorizationCode("http://localhost/callback?code=abc&state=s") equals `abc`
   - Expected: readClientSecret("env-secret", false, "") equals `env-secret`
   - Expected: onData("abc", "\u007F") equals `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve OAuth redirect and secret helpers")
val provider = ClaudeAuthProvider.new("srv", McpServerConfig.new("http", "https://mcp.example"), "http://localhost/callback", AuthStorage.new())
val state = provider.state()
expect(performMCPOAuthFlow(provider, "code", state)).to_equal("token_exchange")
expect(authorizationCode("http://localhost/callback?code=abc&state=s")).to_equal("abc")
expect(readClientSecret("env-secret", false, "")).to_equal("env-secret")
expect(onData("abc", "\u007F")).to_equal("ab")
```

</details>

#### should expose scope extraction and source-backed constants

- Pin source surface
   - Expected: getScopeFromMetadata(metadata) equals `read write`
   - Expected: mcpAuthSourceLinesModeled() equals `2465`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin source surface")
val metadata = OAuthMetadata.new()
metadata.scopesSupported = ["read", "write"]
expect(getScopeFromMetadata(metadata)).to_equal("read write")
expect(mcpAuthSourceLinesModeled()).to_equal(2465)
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
- **Design:** [N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/auth.ts`.](N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/auth.ts`.)
- **Research:** [N/A - upstream TypeScript file is the source reference.](N/A - upstream TypeScript file is the source reference.)


</details>
