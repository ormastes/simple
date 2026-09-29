# Claude Full OAuth Service

> Purpose: should create verifier and build manual and automatic URLs

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full OAuth Service

Purpose: should create verifier and build manual and automatic URLs

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/services/oauth/index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should create verifier and build manual and automatic URLs
Audience: compiler and tooling engineers who maintain this spec

# Claude Full OAuth Service

Checks OAuthService authorization-code PKCE flow behavior.

## Scenarios

### Claude full OAuthService

#### should create verifier and build manual and automatic URLs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should create verifier and build manual and automatic URLs
- Verify: should create verifier and build manual and automatic URLs
- Start automatic flow
   - Expected: result.openedBrowser is true
   - Expected: result.handlerReceivedAutomaticUrl is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create verifier and build manual and automatic URLs")
step("Verify: should create verifier and build manual and automatic URLs")
# @req: REQ-TOOLS-Inde-001
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

- should hand both URLs to caller when browser open is skipped
- Verify: should hand both URLs to caller when browser open is skipped
- Start SDK-controlled flow
   - Expected: result.openedBrowser is false
   - Expected: result.handlerReceivedAutomaticUrl is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should hand both URLs to caller when browser open is skipped")
step("Verify: should hand both URLs to caller when browser open is skipped")
# @req: REQ-TOOLS-Inde-001
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

- should format token responses with scopes and account
- Verify: should format token responses with scopes and account
- Format OAuth tokens
   - Expected: tokens.accessToken equals `access`
   - Expected: tokens.expiresAt equals `160000`
   - Expected: tokens.scopes equals `["read", "write"]`
   - Expected: tokens.tokenAccountUuid equals `acct`
   - Expected: tokens.organizationUuid equals `org`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should format token responses with scopes and account")
step("Verify: should format token responses with scopes and account")
# @req: REQ-TOOLS-Inde-001
step("Format OAuth tokens")
val service = OAuthService.new()
var response = OAuthTokenExchangeResponse.new("access", "refresh", 60, "read write")
response.accountUuid = "acct"
response.accountEmail = "a@example.com"
response.organizationUuid = "org"
val tokens = service.formatTokens(response, "max", "tier2", "raw")
expect(tokens.accessToken).to_equal("access")
expect(tokens.expiresAt).to_equal(160000)  # oracle: value fixed by the spec contract
expect(tokens.scopes).to_equal(["read", "write"])
expect(tokens.tokenAccountUuid).to_equal("acct")
expect(tokens.organizationUuid).to_equal("org")
```

</details>

#### should resolve manual authorization code and close listener

- should resolve manual authorization code and close listener
- Verify: should resolve manual authorization code and close listener
- Use manual pasted code
   - Expected: service.manualAuthorizationCode equals `MANUAL`
   - Expected: service.manualAuthCodeResolverReady is false
   - Expected: service.authCodeListener.closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should resolve manual authorization code and close listener")
step("Verify: should resolve manual authorization code and close listener")
# @req: REQ-TOOLS-Inde-001
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

- should log automatic auth and redirect on successful automatic flow
- Verify: should log automatic auth and redirect on successful automatic flow
- Complete automatic flow
   - Expected: result.automaticFlow is true
   - Expected: result.logs[0] equals `tengu_oauth_auth_code_received:true`
   - Expected: service.cleanedUp is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should log automatic auth and redirect on successful automatic flow")
step("Verify: should log automatic auth and redirect on successful automatic flow")
# @req: REQ-TOOLS-Inde-001
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

- should cleanup listener and manual resolver
- Verify: should cleanup listener and manual resolver
- Cleanup resources
   - Expected: service.manualAuthCodeResolverReady is false
   - Expected: service.authCodeListener.closed is true
   - Expected: service.cleanedUp is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cleanup listener and manual resolver")
step("Verify: should cleanup listener and manual resolver")
# @req: REQ-TOOLS-Inde-001
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

- should expose source-backed helpers
- Verify: should expose source-backed helpers
- Pin helper surface
   - Expected: generateCodeVerifier() equals `verifier`
   - Expected: generateCodeChallenge("v") equals `challenge:v`
   - Expected: parseScopes("a b") equals `["a", "b"]`
   - Expected: oauthServiceSourceLinesModeled() equals `198`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose source-backed helpers")
step("Verify: should expose source-backed helpers")
# @req: REQ-TOOLS-Inde-001
step("Pin helper surface")
expect(generateCodeVerifier()).to_equal("verifier")
expect(generateCodeChallenge("v")).to_equal("challenge:v")
expect(parseScopes("a b")).to_equal(["a", "b"])
expect(oauthServiceSourceLinesModeled()).to_equal(198)  # oracle: value fixed by the spec contract
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Inde-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2a65e8c0439a29a8d07867d0f4ede3984382d583718f9179508484967d9a7733`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2a65e8c0439a29a8d07867d0f4ede3984382d583718f9179508484967d9a7733`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2a65e8c0439a29a8d07867d0f4ede3984382d583718f9179508484967d9a7733`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/services/oauth/index_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/services/oauth/index_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/services/oauth/index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/services/oauth/index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/services/oauth/index_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create verifier and build manual and automatic URLs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/oauth/index_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create verifier and build manual and automatic URLs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/oauth/index_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should hand both URLs to caller when browser open is skipped' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/oauth/index_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should hand both URLs to caller when browser open is skipped' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/oauth/index_spec.spl:55:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should format token responses with scopes and account' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/oauth/index_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should format token responses with scopes and account' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/oauth/index_spec.spl:73:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should resolve manual authorization code and close listener' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/oauth/index_spec.spl:88:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should log automatic auth and redirect on successful automatic flow' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/oauth/index_spec.spl:101:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should cleanup listener and manual resolver' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
