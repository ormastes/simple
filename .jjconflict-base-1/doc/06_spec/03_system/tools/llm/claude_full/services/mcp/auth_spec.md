# Claude Full MCP Auth Owner Boundaries

> Deterministic supporting parts-bin evidence for credential mutation and
> pure OAuth owners.

| Field | Value |
|---|---|
| Source | `test/03_system/tools/llm/claude_full/services/mcp/auth_spec.spl` |
| Executable scenarios | 24 |
| Execution in this tranche | 0 scenarios executed |
| Result | Not executed; no PASS is claimed |
| Requirement | N/A; supporting Claude-full parts-bin evidence |

## Scope and claim boundary

This manual mirrors server-scoped state/effect behavior and deterministic OAuth
owner behavior from `services/mcp/auth.spl`. The retained mutation scenarios
cover `revokeToken`, `revokeServerTokens`,
`clearServerTokensFromLocalStorage`, `saveMcpClientSecret`,
`clearMcpClientConfig`, and `ClaudeAuthProvider.invalidateCredentials`.

The added direct-owner scenarios cover `redactSensitiveUrlParams`,
`normalizeOAuthErrorBody`, `createAuthFetch`, `abort`, `cleanup`,
`fetchAuthServerMetadata`, `getServerKey`, `hasMcpDiscoveryButNoToken`,
provider client metadata/information/token state, `performMCPXaaAuth`,
`performMCPOAuthFlow`, `readClientSecret`, `onData`,
`getScopeFromMetadata`, and `wrapFetchWithStepUpDetection`.

It does not claim shipped CLI/TUI reachability, keychain access, browser flow,
network access, process execution, or upstream-exact behavior while the pinned
upstream source tree is absent. `McpAuthMutationTrace.effects` is a
deterministic storage-effect record, not evidence of an external credential
store.

## Frozen fixture and checker contract

`setup_mcp_auth_fixture` creates independent `alpha` and `beta` token/secret
records. `run_mcp_auth_mutation` applies one named mutation through
`McpAuthMutationModel`. `check_mcp_auth_mutation` asserts exact owner, success,
token-change flag, secret-change flag, effect list, and error.

Every displayed scenario uses the frozen visible flow:

1. Set up isolated MCP authentication storage
2. Apply one credential mutation
3. Check exact server-scoped storage effects

`setup_mcp_oauth_fixture` creates an isolated provider, configuration, and
in-memory storage owner. `run_mcp_oauth_flow` invokes the direct OAuth-flow
owner. `check_mcp_oauth_flow` asserts the exact result, generated/preserved
state, and authorization URL mutation.

Every added direct-owner scenario uses the frozen visible flow:

1. Set up isolated MCP OAuth state
2. Evaluate one OAuth owner boundary
3. Check exact response and provider state

## Scenarios

### should revoke one server token through revokeToken

- Start with independent `alpha` and `beta` credentials.
- Apply `revoke-token` to `alpha`.
- Assert the `revokeToken` owner, one exact `clear-token:<alpha-key>` effect,
  cleared alpha token fields, unchanged alpha secret, and unchanged beta token.

### should revoke one server credential set through revokeServerTokens

- Start with independent `alpha` and `beta` credentials.
- Apply `revoke-server-tokens` to `alpha`.
- Assert the `revokeServerTokens` owner, one exact token-clear effect, cleared
  alpha access/refresh tokens, and retained alpha client secret.

### should clear only local tokens through clearServerTokensFromLocalStorage

- Start with independent `alpha` and `beta` credentials.
- Apply `clear-local-tokens` to `alpha`.
- Assert the `clearServerTokensFromLocalStorage` owner, one exact token-clear
  effect, cleared alpha token fields, and retained alpha secret.

### should save one server secret through saveMcpClientSecret

- Start with independent `alpha` and `beta` credentials.
- Save `alpha-secret-next` for `alpha`.
- Assert the `saveMcpClientSecret` owner, one exact client-secret effect,
  before/after alpha secret values, no token change, and unchanged beta secret.

### should clear one server secret through clearMcpClientConfig

- Start with independent `alpha` and `beta` credentials.
- Clear the `alpha` client configuration.
- Assert the `clearMcpClientConfig` owner, one exact config-clear effect,
  cleared alpha secret, and retained alpha access token.

### should invalidate one server token and secret through the provider owner

- Start with independent `alpha` and `beta` credentials.
- Apply `invalidate-all` to `alpha`.
- Assert the `ClaudeAuthProvider.invalidateCredentials` owner, ordered token
  and secret clear effects, empty alpha credentials, and unchanged beta
  credentials.

### should preserve exact server isolation across sequential mutations

- Start with independent `alpha` and `beta` credentials.
- Update only the alpha secret.
- Assert exact alpha effect, unchanged beta token/secret values, and unchanged
  token-key order.

### should make repeated identical credential mutations idempotent

- Start with independent `alpha` and `beta` credentials.
- Clear the alpha client configuration twice.
- Assert one effect and state change on the first mutation; assert success with
  no state change and no effect on the repeated mutation.

### should reject unsupported credential mutations without storage effects

- Start with independent `alpha` and `beta` credentials.
- Apply `unknown-operation` to alpha.
- Assert failure, exact error text, no owner, no state flags, no effects, and
  unchanged alpha token/secret fields.

### should redact every sensitive URL parameter including repeats and the final value

- Redact a URL containing a non-sensitive `upstate`, multiple sensitive keys,
  two exact `state` values, and a final-position authorization code.
- Assert every sensitive value becomes `[REDACTED]` in place while `upstate`
  remains unchanged.

### should normalize successful OAuth error bodies and pass other responses through

- Pass a 2xx refresh-token error through `createAuthFetch`.
- Assert refresh expiry maps to `invalid_grant`, another 2xx OAuth error keeps
  its body with status 400, and non-2xx/success responses pass through.

### should return deterministic cancellation cleanup and metadata fallback values

- Assert the exact cancellation type/message and cleanup marker.
- Assert successful discovery, legacy path fallback, and root fallback values.

### should derive a stable server key and distinguish discovery from token state

- Assert the key includes server name, type, URL, and ordered headers.
- Assert discovery-without-token is true, then false after token storage, and
  false when the enabled XAA owner bypasses discovery.

### should expose provider metadata URLs and persisted client information

- Assert exact client metadata including supported scopes.
- Assert default/overridden client-metadata URLs, stored client identity, one
  storage effect, and exact diagnostic logs.

### should fall back to configured client identity and apply token expiry and step-up rules

- Assert configured-client fallback and secret lookup.
- Assert current token state, refresh-token omission during step-up, and empty
  token state when an expired token has no refresh token.

### should exchange a cached XAA identity token into stored MCP access state

- Assert missing identity produces no token.
- Assert cached identity produces and stores exact access, expiry, and scope.

### should cancel an OAuth flow before generating state

- Invoke the frozen flow helper without an authorization code.
- Assert cancellation, no generated state, and no authorization URL mutation.

### should reject an OAuth flow with a mismatched state

- Invoke the frozen flow helper with a mismatched state.
- Assert `state_mismatch`, one generated state, and no authorization mutation.

### should mutate authorization state after a successful OAuth flow

- Invoke the frozen flow helper with the generated state witness.
- Assert `token_exchange`, retained state, and exact `authorized` mutation.

### should source client secrets and edit prompt data without external input

- Assert environment, non-TTY, and typed-secret branches.
- Assert append, delete, and empty-delete prompt editing behavior.

### should resolve OAuth scope metadata in explicit default and supported order

- Assert `scope`, `defaultScope`, joined `scopesSupported`, and empty fallback
  precedence in one isolated matrix.

### should mark step-up state for a 403 insufficient-scope response with scope

- Return the original response object.
- Assert scope extraction, provider mutation, and exact diagnostic log.

### should preserve provider state for a 403 insufficient-scope response without scope

- Return the original response object.
- Assert no provider mutation when the challenge has no scope.

### should preserve provider state for a non-403 response with scope metadata

- Return the original response object.
- Assert no provider mutation when a scoped challenge is not status 403.

## Deterministic seams

`McpAuthMutationModel.apply` records the target server key and snapshots token
and client-secret fields before invoking one real mutation owner. It then
snapshots the same key, derives exact change flags, and copies only storage
effects added during that call into `McpAuthMutationTrace`.

Storage writes and clears are idempotent: writing an identical token, client
info, or secret and clearing an already-empty token or secret do not append a
second update record.

The OAuth scenarios invoke the exported pure owners directly. They use only
in-memory values and provider state; they do not introduce sentinels or invoke
network, browser, keychain, environment, terminal, or process adapters. The
repeated-sensitive-parameter scenario demonstrates the production redactor
defect fixed by offset-based repeated scanning and exact query-parameter
boundaries.

<details>
<summary>Executable helper source</summary>

```simple
fn setup_mcp_auth_fixture() -> McpAuthMutationModel:
    val storage = AuthStorage.new()
    val alphaConfig = mcp_auth_fixture_config("alpha")
    val betaConfig = mcp_auth_fixture_config("beta")
    val alphaKey = getServerKey("alpha", alphaConfig)
    val betaKey = getServerKey("beta", betaConfig)
    storage.setToken(alphaKey, OAuthTokens.new("alpha-access", "alpha-refresh", 1000, "read"))
    storage.setToken(betaKey, OAuthTokens.new("beta-access", "beta-refresh", 2000, "write"))
    storage.saveClientSecret(alphaKey, "alpha-secret")
    storage.saveClientSecret(betaKey, "beta-secret")
    McpAuthMutationModel.new(storage)

fn run_mcp_auth_mutation(model: McpAuthMutationModel, operation: text, serverName: text, clientSecret: text) -> McpAuthMutationTrace:
    model.apply(operation, serverName, mcp_auth_fixture_config(serverName), clientSecret)

fn check_mcp_auth_mutation(trace: McpAuthMutationTrace, expectedOwner: text, expectedSuccess: bool, expectedTokenChanged: bool, expectedClientSecretChanged: bool, expectedEffects: [text], expectedError: text):
    expect(trace.owner).to_equal(expectedOwner)
    expect(trace.success).to_equal(expectedSuccess)
    expect(trace.tokenChanged).to_equal(expectedTokenChanged)
    expect(trace.clientSecretChanged).to_equal(expectedClientSecretChanged)
    expect(trace.effects).to_equal(expectedEffects)
    expect(trace.error).to_equal(expectedError)

fn setup_mcp_oauth_fixture() -> ClaudeAuthProvider:
    val storage = AuthStorage.new()
    val config = McpServerConfig.new("http", "https://mcp.example/oauth")
    config.headers = ["x-fixture=isolated"]
    ClaudeAuthProvider.new("oauth-owner", config, "http://127.0.0.1/callback", storage)

fn run_mcp_oauth_flow(provider: ClaudeAuthProvider, authorizationCodeValue: text, stateValue: text) -> text:
    performMCPOAuthFlow(provider, authorizationCodeValue, stateValue)

fn check_mcp_oauth_flow(provider: ClaudeAuthProvider, result: text, expectedResult: text, expectedState: text, expectedAuthorizationUrl: text):
    expect(result).to_equal(expectedResult)
    expect(provider.stateValue).to_equal(expectedState)
    expect(provider.authorizationUrlValue).to_equal(expectedAuthorizationUrl)
```

</details>

## Execution

Run when a qualified pure-Simple runtime is available:

```sh
bin/simple spipe-docgen \
  test/03_system/tools/llm/claude_full/services/mcp/auth_spec.spl \
  --output doc/06_spec --no-index

bin/simple test \
  test/03_system/tools/llm/claude_full/services/mcp/auth_spec.spl \
  --mode=interpreter
```

A missing runtime, nonzero exit, unresolved symbol, no-examples result, or
docgen stub result is a failure. This hand-maintained mirror records zero
executed scenarios and must not be presented as runtime PASS evidence. The
manual is an exact 24-scenario source mirror by title, owner boundary, visible
step vocabulary, and expected state/response behavior; docgen parity remains
unverified until the qualified runtime is restored.
