# Claude Full Remote Setup API

> Checks redacted GitHub token handling and remote setup API response mapping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Remote Setup API

Checks redacted GitHub token handling and remote setup API response mapping.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/remote-setup/api_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks redacted GitHub token handling and remote setup API response mapping.

## Scenarios

### Claude full remote setup api

#### redacts GitHub token outside reveal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- redacts GitHub token outside reveal
- String, JSON, and inspect views hide the raw token
   - Expected: token.reveal() equals `ghp-secret`
   - Expected: token.toString() equals `redactedGithubTokenText()`
   - Expected: token.toJSON() equals `redactedGithubTokenText()`
   - Expected: token.inspect() equals `redactedGithubTokenText()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("redacts GitHub token outside reveal")
step("String, JSON, and inspect views hide the raw token")
val token = RedactedGithubToken.new("ghp-secret")
expect(token.reveal()).to_equal("ghp-secret")
expect(token.toString()).to_equal(redactedGithubTokenText())
expect(token.toJSON()).to_equal(redactedGithubTokenText())
expect(token.inspect()).to_equal(redactedGithubTokenText())
```

</details>

#### maps import token responses

- maps import token responses
- Prepare failure, status codes, and network failures map to typed errors
   - Expected: importGithubToken(RedactedGithubToken.new("tok"), false, 200, false, "me").errorKind equals `not_signed_in`
   - Expected: importGithubToken(RedactedGithubToken.new("tok"), true, 200, false, "me").github_username equals `me`
   - Expected: importGithubToken(RedactedGithubToken.new("tok"), true, 400, false, "").errorKind equals `invalid_token`
   - Expected: importGithubToken(RedactedGithubToken.new("tok"), true, 401, false, "").errorKind equals `not_signed_in`
   - Expected: importGithubToken(RedactedGithubToken.new("tok"), true, 503, false, "").errorKind equals `server`
   - Expected: importGithubToken(RedactedGithubToken.new("tok"), true, 200, true, "").errorKind equals `network`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps import token responses")
step("Prepare failure, status codes, and network failures map to typed errors")
expect(importGithubToken(RedactedGithubToken.new("tok"), false, 200, false, "me").errorKind).to_equal("not_signed_in")
expect(importGithubToken(RedactedGithubToken.new("tok"), true, 200, false, "me").github_username).to_equal("me")
expect(importGithubToken(RedactedGithubToken.new("tok"), true, 400, false, "").errorKind).to_equal("invalid_token")
expect(importGithubToken(RedactedGithubToken.new("tok"), true, 401, false, "").errorKind).to_equal("not_signed_in")
expect(importGithubToken(RedactedGithubToken.new("tok"), true, 503, false, "").errorKind).to_equal("server")
expect(importGithubToken(RedactedGithubToken.new("tok"), true, 200, true, "").errorKind).to_equal("network")
```

</details>

#### maps environment and sign-in helpers

- maps environment and sign-in helpers
- Default environment creation is best-effort
   - Expected: hasExistingEnvironment(true, 1) is true
   - Expected: hasExistingEnvironment(false, 9) is false
   - Expected: createDefaultEnvironment(false, 0, 201, false) is false
   - Expected: createDefaultEnvironment(true, 1, 500, false) is true
   - Expected: createDefaultEnvironment(true, 0, 201, false) is true
   - Expected: createDefaultEnvironment(true, 0, 500, false) is false
   - Expected: isSignedIn(true) is true
   - Expected: getCodeWebUrl("https://claude.ai") equals `https://claude.ai/code`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps environment and sign-in helpers")
step("Default environment creation is best-effort")
expect(hasExistingEnvironment(true, 1)).to_equal(true)
expect(hasExistingEnvironment(false, 9)).to_equal(false)
expect(createDefaultEnvironment(false, 0, 201, false)).to_equal(false)
expect(createDefaultEnvironment(true, 1, 500, false)).to_equal(true)
expect(createDefaultEnvironment(true, 0, 201, false)).to_equal(true)
expect(createDefaultEnvironment(true, 0, 500, false)).to_equal(false)
expect(isSignedIn(true)).to_equal(true)
expect(getCodeWebUrl("https://claude.ai")).to_equal("https://claude.ai/code")
```

</details>

#### exports source-backed constants

- exports source-backed constants
- Pin endpoints, headers, and default environment body
   - Expected: importTokenUrl("https://api") equals `https://api/v1/code/github/import-token`
   - Expected: createEnvironmentUrl("https://api") equals `https://api/v1/environment_providers/cloud/create`
   - Expected: ccrByocBetaHeader() equals `ccr-byoc-2025-07-29`
   - Expected: importTokenTimeoutMs() equals `15000`
   - Expected: createEnvironmentTimeoutMs() equals `15000`
   - Expected: defaultEnvironmentName() equals `Default`
   - Expected: defaultEnvironmentKind() equals `anthropic_cloud`
   - Expected: defaultEnvironmentType() equals `anthropic`
   - Expected: defaultEnvironmentCwd() equals `/home/user`
   - Expected: defaultPythonVersion() equals `3.11`
   - Expected: defaultNodeVersion() equals `20`
   - Expected: allowDefaultHosts() is true
   - Expected: rawTokenOnlyRevealedInHttpBody() is true
   - Expected: networkErrorLogsCodeOnly() is true
   - Expected: tokenStoredEncryptedServerSide() is true
   - Expected: createEnvironmentFailuresNonFatal() is true
   - Expected: remoteSetupApiSourceLinesModeled() equals `174`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed constants")
step("Pin endpoints, headers, and default environment body")
expect(importTokenUrl("https://api")).to_equal("https://api/v1/code/github/import-token")
expect(createEnvironmentUrl("https://api")).to_equal("https://api/v1/environment_providers/cloud/create")
expect(ccrByocBetaHeader()).to_equal("ccr-byoc-2025-07-29")
expect(importTokenTimeoutMs()).to_equal(15000)
expect(createEnvironmentTimeoutMs()).to_equal(15000)
expect(defaultEnvironmentName()).to_equal("Default")
expect(defaultEnvironmentKind()).to_equal("anthropic_cloud")
expect(defaultEnvironmentDescription()).to_contain("trusted network")
expect(defaultEnvironmentType()).to_equal("anthropic")
expect(defaultEnvironmentCwd()).to_equal("/home/user")
expect(defaultPythonVersion()).to_equal("3.11")
expect(defaultNodeVersion()).to_equal("20")
expect(allowDefaultHosts()).to_equal(true)
expect(rawTokenOnlyRevealedInHttpBody()).to_equal(true)
expect(networkErrorLogsCodeOnly()).to_equal(true)
expect(tokenStoredEncryptedServerSide()).to_equal(true)
expect(createEnvironmentFailuresNonFatal()).to_equal(true)
expect(remoteSetupApiSourceLinesModeled()).to_equal(174)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `04fd9b751332d0cb4406b5c2c2e601c19b92ed7ff11d4838174501f814518069`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `04fd9b751332d0cb4406b5c2c2e601c19b92ed7ff11d4838174501f814518069`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `04fd9b751332d0cb4406b5c2c2e601c19b92ed7ff11d4838174501f814518069`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/commands/remote-setup/api_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/remote-setup/api_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/remote-setup/api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/remote-setup/api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/remote-setup/api_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/commands/remote-setup/api_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'redacts GitHub token outside reveal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/remote-setup/api_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps import token responses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/remote-setup/api_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps environment and sign-in helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
