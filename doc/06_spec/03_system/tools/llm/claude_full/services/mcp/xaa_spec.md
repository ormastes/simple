# Claude Full MCP XAA

> Purpose: should create timeout fetch and normalize URLs

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full MCP XAA

Purpose: should create timeout fetch and normalize URLs

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should create timeout fetch and normalize URLs
Audience: compiler and tooling engineers who maintain this spec

# Claude Full MCP XAA

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should create timeout fetch and normalize URLs
- Verify: should create timeout fetch and normalize URLs
- Compose abort signal and strip trailing slash
   - Expected: fetch.timeoutMs equals `30000`
   - Expected: fetch.composedAbort is true
   - Expected: normalizeUrl("HTTPS://Example.com/") equals `https://Example.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create timeout fetch and normalize URLs")
step("Verify: should create timeout fetch and normalize URLs")
# @req: REQ-TOOLS-Xaa-001
step("Compose abort signal and strip trailing slash")
val fetch = makeXaaFetch(true)
expect(fetch.timeoutMs).to_equal(30000)  # oracle: value fixed by the spec contract
expect(fetch.composedAbort).to_equal(true)
expect(normalizeUrl("HTTPS://Example.com/")).to_equal("https://Example.com")
```

</details>

#### should redact sensitive token fields

- should redact sensitive token fields
- Verify: should redact sensitive token fields
- Redact tokens from raw JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should redact sensitive token fields")
step("Verify: should redact sensitive token fields")
# @req: REQ-TOOLS-Xaa-001
step("Redact tokens from raw JSON")
val redacted = redactTokens("{\"access_token\":\"a\",\"subject_token\":\"b\",\"client_secret\":\"c\"}")
expect(redacted).to_contain("\"access_token\":\"[REDACTED]\"")
expect(redacted).to_contain("\"subject_token\":\"[REDACTED]\"")
expect(redacted).to_contain("\"client_secret\":\"[REDACTED]\"")
```

</details>

#### should validate protected resource discovery

- should validate protected resource discovery
- Verify: should validate protected resource discovery
- Detect PRM resource mismatch
   - Expected: ok.authorizationServers[0] equals `https://as.example`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should validate protected resource discovery")
step("Verify: should validate protected resource discovery")
# @req: REQ-TOOLS-Xaa-001
step("Detect PRM resource mismatch")
val ok = discoverProtectedResource("https://mcp.example/mcp", ProtectedResourceMetadata.new("https://mcp.example/mcp/", ["https://as.example"]))
expect(ok.authorizationServers[0]).to_equal("https://as.example")
val bad = discoverProtectedResource("https://mcp.example/mcp", ProtectedResourceMetadata.new("https://other.example", ["https://as.example"]))
expect(bad.resource).to_contain("ERROR: PRM resource mismatch")
```

</details>

#### should validate authorization server metadata

- should validate authorization server metadata
- Verify: should validate authorization server metadata
- Reject non-HTTPS token endpoint
   - Expected: ok.tokenEndpoint equals `https://as.example/token`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should validate authorization server metadata")
step("Verify: should validate authorization server metadata")
# @req: REQ-TOOLS-Xaa-001
step("Reject non-HTTPS token endpoint")
val ok = discoverAuthorizationServer("https://as.example", AuthorizationServerMetadata.new("https://as.example/", "https://as.example/token"))
expect(ok.tokenEndpoint).to_equal("https://as.example/token")
val bad = discoverAuthorizationServer("https://as.example", AuthorizationServerMetadata.new("https://as.example", "http://as.example/token"))
expect(bad.issuer).to_contain("ERROR: refusing non-HTTPS")
```

</details>

#### should classify token exchange failures by clear-cache semantics

- should classify token exchange failures by clear-cache semantics
- Verify: should classify token exchange failures by clear-cache semantics
- Compare 4xx and 5xx token exchange failures
   - Expected: badGrant.error.shouldClearIdToken is true
   - Expected: outage.error.shouldClearIdToken is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should classify token exchange failures by clear-cache semantics")
step("Verify: should classify token exchange failures by clear-cache semantics")
# @req: REQ-TOOLS-Xaa-001
step("Compare 4xx and 5xx token exchange failures")
val badGrant = requestJwtAuthorizationGrant(400, "{\"id_token\":\"secret\"}", TokenExchangeResponse.new("", "", 0, ""))
expect(badGrant.error.shouldClearIdToken).to_equal(true)
expect(badGrant.error.message).to_contain("[REDACTE")
val outage = requestJwtAuthorizationGrant(503, "down", TokenExchangeResponse.new("", "", 0, ""))
expect(outage.error.shouldClearIdToken).to_equal(false)
```

</details>

#### should require ID-JAG token type

- should require ID-JAG token type
- Verify: should require ID-JAG token type
- Reject unexpected issued_token_type
   - Expected: bad.error.name equals `XaaTokenExchangeError`
   - Expected: bad.error.shouldClearIdToken is true
   - Expected: ok.jwtAuthGrant equals `jag`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require ID-JAG token type")
step("Verify: should require ID-JAG token type")
# @req: REQ-TOOLS-Xaa-001
step("Reject unexpected issued_token_type")
val bad = requestJwtAuthorizationGrant(200, "", TokenExchangeResponse.new("jag", "wrong", 60, "read"))
expect(bad.error.name).to_equal("XaaTokenExchangeError")
expect(bad.error.shouldClearIdToken).to_equal(true)
val ok = requestJwtAuthorizationGrant(200, "", TokenExchangeResponse.new("jag", idJagTokenType(), 60, "read"))
expect(ok.jwtAuthGrant).to_equal("jag")
```

</details>

#### should exchange jwt bearer grants with default bearer token type

- should exchange jwt bearer grants with default bearer token type
- Verify: should exchange jwt bearer grants with default bearer token type
- Accept missing token_type as Bearer
   - Expected: token.tokenType equals `Bearer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should exchange jwt bearer grants with default bearer token type")
step("Verify: should exchange jwt bearer grants with default bearer token type")
# @req: REQ-TOOLS-Xaa-001
step("Accept missing token_type as Bearer")
val token = exchangeJwtAuthGrant(200, "", JwtBearerResponse.new("access", "", 300, "read", "refresh"), "client_secret_basic")
expect(token.tokenType).to_equal("Bearer")
val failed = exchangeJwtAuthGrant(500, "{\"assertion\":\"secret\"}", JwtBearerResponse.new("", "", 0, "", ""), "client_secret_post")
expect(failed.error).to_contain("[REDACTE")
```

</details>

#### should select AS auth method from metadata

- should select AS auth method from metadata
- Verify: should select AS auth method from metadata
- Prefer post only when basic is absent
   - Expected: selectAuthMethod(["client_secret_post"]) equals `client_secret_post`
   - Expected: selectAuthMethod(["client_secret_basic", "client_secret_post"]) equals `client_secret_basic`
   - Expected: selectAuthMethod([]) equals `client_secret_basic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should select AS auth method from metadata")
step("Verify: should select AS auth method from metadata")
# @req: REQ-TOOLS-Xaa-001
step("Prefer post only when basic is absent")
expect(selectAuthMethod(["client_secret_post"])).to_equal("client_secret_post")
expect(selectAuthMethod(["client_secret_basic", "client_secret_post"])).to_equal("client_secret_basic")
expect(selectAuthMethod([])).to_equal("client_secret_basic")
```

</details>

#### should perform full cross-app access flow

- should perform full cross-app access flow
- Verify: should perform full cross-app access flow
- Compose PRM, AS metadata, ID-JAG, and access token
   - Expected: result.accessToken equals `access`
   - Expected: result.authorizationServerUrl equals `https://as.example`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should perform full cross-app access flow")
step("Verify: should perform full cross-app access flow")
# @req: REQ-TOOLS-Xaa-001
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

- should expose source-backed constants
- Verify: should expose source-backed constants
- Pin source surface
   - Expected: error.name equals `XaaTokenExchangeError`
   - Expected: xaaSourceLinesModeled() equals `511`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose source-backed constants")
step("Verify: should expose source-backed constants")
# @req: REQ-TOOLS-Xaa-001
step("Pin source surface")
val error = XaaTokenExchangeError.new("bad", true)
expect(error.name).to_equal("XaaTokenExchangeError")
expect(tokenExchangeGrant()).to_contain("token-exchange")
expect(xaaSourceLinesModeled()).to_equal(511)  # oracle: value fixed by the spec contract
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

- **Requirements:** `N/A - strict llm_caret Claude CLI parity lane.`
- **Plan:** `N/A - target selected from strict checker output.`
- **Design:** `N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/xaa.ts`.`
- **Research:** `N/A - upstream TypeScript file is the source reference.`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Xaa-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `922bc05f1a867d4965fa1364ac17f5fa8af724ea32e397884886b599a04ff0f9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `922bc05f1a867d4965fa1364ac17f5fa8af724ea32e397884886b599a04ff0f9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `922bc05f1a867d4965fa1364ac17f5fa8af724ea32e397884886b599a04ff0f9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/services/mcp/xaa_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/services/mcp/xaa_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/services/mcp/xaa_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/services/mcp/xaa_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/services/mcp/xaa_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create timeout fetch and normalize URLs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/xaa_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create timeout fetch and normalize URLs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/mcp/xaa_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should redact sensitive token fields' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/xaa_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should redact sensitive token fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/mcp/xaa_spec.spl:55:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should validate protected resource discovery' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/xaa_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should validate protected resource discovery' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/mcp/xaa_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should validate authorization server metadata' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/xaa_spec.spl:77:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify token exchange failures by clear-cache semantics' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/xaa_spec.spl:89:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require ID-JAG token type' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
