# Claude Full CLI Auth Handler

> Checks auth login, status, logout, and token install decisions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CLI Auth Handler

Checks auth login, status, logout, and token install decisions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/handlers/auth_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks auth login, status, logout, and token install decisions.

## Scenarios

### Claude full cli auth handler

#### installs OAuth tokens and chooses Claude.ai versus Console work

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- installs OAuth tokens and chooses Claude.ai versus Console work
- Claude.ai tokens fetch first token date; Console tokens create API key
   - Expected: shouldUseClaudeAIAuth(claudeTokens.scopes) is true
   - Expected: claude.loggedOutFirst is true
   - Expected: claude.usedProfile is true
   - Expected: claude.loggedStorageWarning is true
   - Expected: claude.fetchedFirstTokenDate is true
   - Expected: claude.createdApiKey is false
   - Expected: console.usedTokenAccountFallback is true
   - Expected: console.createdApiKey is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("installs OAuth tokens and chooses Claude.ai versus Console work")
step("Claude.ai tokens fetch first token date; Console tokens create API key")
val claudeTokens = OAuthTokens.new("tok", ["user:profile", "user:sessions:claude_code"]).withProfile().withWarning("disk")
val claude = installOAuthTokens(claudeTokens, true)
expect(shouldUseClaudeAIAuth(claudeTokens.scopes)).to_equal(true)
expect(claude.loggedOutFirst).to_equal(true)
expect(claude.usedProfile).to_equal(true)
expect(claude.loggedStorageWarning).to_equal(true)
expect(claude.fetchedFirstTokenDate).to_equal(true)
expect(claude.createdApiKey).to_equal(false)
val consoleTokens = OAuthTokens.new("tok", ["user:inference"]).withTokenAccount()
val console = installOAuthTokens(consoleTokens, true)
expect(console.usedTokenAccountFallback).to_equal(true)
expect(console.createdApiKey).to_equal(true)
expect(installOAuthTokens(consoleTokens, false).error).to_contain("Unable to create API key")
```

</details>

#### handles login flag conflicts and method resolution

- handles login flag conflicts and method resolution
- Console and Claude.ai conflict; enterprise force method wins
   - Expected: conflict.code equals `1`
   - Expected: conflict.stderr equals `forceLoginConflictMessage()`
   - Expected: resolveLoginWithClaudeAi("", false) is true
   - Expected: resolveLoginWithClaudeAi("", true) is false
   - Expected: resolveLoginWithClaudeAi("claudeai", true) is true
   - Expected: resolveLoginWithClaudeAi("console", false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles login flag conflicts and method resolution")
step("Console and Claude.ai conflict; enterprise force method wins")
val conflict = authLogin(AuthLoginRequest.new().withConsole().withClaudeAiFlag())
expect(conflict.code).to_equal(1)
expect(conflict.stderr).to_equal(forceLoginConflictMessage())
expect(resolveLoginWithClaudeAi("", false)).to_equal(true)
expect(resolveLoginWithClaudeAi("", true)).to_equal(false)
expect(resolveLoginWithClaudeAi("claudeai", true)).to_equal(true)
expect(resolveLoginWithClaudeAi("console", false)).to_equal(false)
```

</details>

#### handles refresh-token login path

- handles refresh-token login path
- Env refresh token requires scopes, validates org, and marks onboarding complete
   - Expected: missingScopes.code equals `1`
   - Expected: missingScopes.stderr equals `missingEnvScopesMessage()`
   - Expected: ok.code equals `0`
   - Expected: ok.stdout equals `loginSuccessMessage()`
   - Expected: ok.usedEnvRefreshToken is true
   - Expected: ok.markedOnboardingComplete is true
   - Expected: ok.cleanedUpOAuthService is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles refresh-token login path")
step("Env refresh token requires scopes, validates org, and marks onboarding complete")
val missingScopes = authLogin(AuthLoginRequest.new().withEnvRefresh("refresh", ""))
expect(missingScopes.code).to_equal(1)
expect(missingScopes.stderr).to_equal(missingEnvScopesMessage())
val ok = authLogin(AuthLoginRequest.new().withEnvRefresh("refresh", "user:inference"))
expect(ok.code).to_equal(0)
expect(ok.stdout).to_equal(loginSuccessMessage())
expect(ok.usedEnvRefreshToken).to_equal(true)
expect(ok.markedOnboardingComplete).to_equal(true)
expect(ok.cleanedUpOAuthService).to_equal(false)
```

</details>

#### handles browser OAuth path

- handles browser OAuth path
- Browser flow uses SSO hint and cleans OAuth service
   - Expected: ok.code equals `0`
   - Expected: ok.loginWithClaudeAi is true
   - Expected: ok.loginMethod equals `sso`
   - Expected: ok.cleanedUpOAuthService is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles browser OAuth path")
step("Browser flow uses SSO hint and cleans OAuth service")
val ok = authLogin(AuthLoginRequest.new().withEmail("a@example.com").withSso())
expect(ok.code).to_equal(0)
expect(ok.loginWithClaudeAi).to_equal(true)
expect(ok.loginMethod).to_equal("sso")
expect(ok.cleanedUpOAuthService).to_equal(true)
```

</details>

#### resolves auth status methods and output

- resolves auth status methods and output
- Status chooses third-party, Claude.ai, helper, token, API key, or none
   - Expected: authMethod(AuthStatusInput.none().withThirdParty()) equals `third_party`
   - Expected: authMethod(AuthStatusInput.none().withClaudeAi("a@b", "org", "Org", "pro")) equals `claude.ai`
   - Expected: authMethod(AuthStatusInput.none().withApiKeyEnv()) equals `api_key`
   - Expected: resolvedApiKeySource(AuthStatusInput.none().withApiKeyEnv()) equals `ANTHROPIC_API_KEY`
   - Expected: json.code equals `0`
   - Expected: text.code equals `1`
   - Expected: text.output equals `notLoggedInMessage()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves auth status methods and output")
step("Status chooses third-party, Claude.ai, helper, token, API key, or none")
expect(authMethod(AuthStatusInput.none().withThirdParty())).to_equal("third_party")
expect(authMethod(AuthStatusInput.none().withClaudeAi("a@b", "org", "Org", "pro"))).to_equal("claude.ai")
expect(authMethod(AuthStatusInput.none().withApiKeyEnv())).to_equal("api_key")
expect(resolvedApiKeySource(AuthStatusInput.none().withApiKeyEnv())).to_equal("ANTHROPIC_API_KEY")
val json = authStatus(AuthStatusInput.none().withClaudeAi("a@b", "org", "Org", "pro"), false)
expect(json.code).to_equal(0)
expect(json.output).to_contain("\"authMethod\":\"claude.ai\"")
expect(json.output).to_contain("\"email\":\"a@b\"")
val text = authStatus(AuthStatusInput.none(), true)
expect(text.code).to_equal(1)
expect(text.output).to_equal(notLoggedInMessage())
```

</details>

#### handles logout and exports source-backed constants

- handles logout and exports source-backed constants
- Logout success/failure and event/env constants stay pinned
   - Expected: authLogout(true).stdout equals `logoutSuccessMessage()`
   - Expected: authLogout(false).stderr equals `logoutFailedMessage()`
   - Expected: oauthFlowStartEvent() equals `tengu_oauth_flow_start`
   - Expected: oauthSuccessEvent() equals `tengu_oauth_success`
   - Expected: oauthStorageWarningEvent() equals `tengu_oauth_storage_warning`
   - Expected: loginFromRefreshTokenEvent() equals `tengu_login_from_refresh_token`
   - Expected: refreshTokenEnvName() equals `CLAUDE_CODE_OAUTH_REFRESH_TOKEN`
   - Expected: refreshScopesEnvName() equals `CLAUDE_CODE_OAUTH_SCOPES`
   - Expected: apiKeyEnvName() equals `ANTHROPIC_API_KEY`
   - Expected: clearOnboardingOnLogout() is false
   - Expected: envRefreshMarksOnboardingComplete() is true
   - Expected: oauthServiceCleanupInFinally() is true
   - Expected: rolesFailureIsNonFatal() is true
   - Expected: firstTokenDateFailureIsNonFatal() is true
   - Expected: consoleApiKeyCreationIsCritical() is true
   - Expected: homespaceIgnoresApiKeyEnvVar() is true
   - Expected: textStatusUsesAccountAndProviderProperties() is true
   - Expected: jsonStatusIncludesClaudeAiAccountFields() is true
   - Expected: authStatusExitCode(false) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles logout and exports source-backed constants")
step("Logout success/failure and event/env constants stay pinned")
expect(authLogout(true).stdout).to_equal(logoutSuccessMessage())
expect(authLogout(false).stderr).to_equal(logoutFailedMessage())
expect(oauthFlowStartEvent()).to_equal("tengu_oauth_flow_start")
expect(oauthSuccessEvent()).to_equal("tengu_oauth_success")
expect(oauthStorageWarningEvent()).to_equal("tengu_oauth_storage_warning")
expect(loginFromRefreshTokenEvent()).to_equal("tengu_login_from_refresh_token")
expect(refreshTokenEnvName()).to_equal("CLAUDE_CODE_OAUTH_REFRESH_TOKEN")
expect(refreshScopesEnvName()).to_equal("CLAUDE_CODE_OAUTH_SCOPES")
expect(apiKeyEnvName()).to_equal("ANTHROPIC_API_KEY")
expect(clearOnboardingOnLogout()).to_equal(false)
expect(envRefreshMarksOnboardingComplete()).to_equal(true)
expect(oauthServiceCleanupInFinally()).to_equal(true)
expect(rolesFailureIsNonFatal()).to_equal(true)
expect(firstTokenDateFailureIsNonFatal()).to_equal(true)
expect(consoleApiKeyCreationIsCritical()).to_equal(true)
expect(homespaceIgnoresApiKeyEnvVar()).to_equal(true)
expect(textStatusUsesAccountAndProviderProperties()).to_equal(true)
expect(jsonStatusIncludesClaudeAiAccountFields()).to_equal(true)
expect(authStatusExitCode(false)).to_equal(1)
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

- Canonical SPipe generation for source `a81634389f67bfb5e803c3a46ab1068f1b25fc17ec705d2cf537c79080023899`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a81634389f67bfb5e803c3a46ab1068f1b25fc17ec705d2cf537c79080023899`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a81634389f67bfb5e803c3a46ab1068f1b25fc17ec705d2cf537c79080023899`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/cli/handlers/auth_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/cli/handlers/auth_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/cli/handlers/auth_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/cli/handlers/auth_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/cli/handlers/auth_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/cli/handlers/auth_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'installs OAuth tokens and chooses Claude.ai versus Console work' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/handlers/auth_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles login flag conflicts and method resolution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/handlers/auth_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles refresh-token login path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
