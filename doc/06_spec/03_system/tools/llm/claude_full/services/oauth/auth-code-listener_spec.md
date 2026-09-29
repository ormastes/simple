# Claude Full OAuth Auth Code Listener

> Purpose: should start on requested or assigned port

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full OAuth Auth Code Listener

Purpose: should start on requested or assigned port

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/services/oauth/auth-code-listener_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should start on requested or assigned port
Audience: compiler and tooling engineers who maintain this spec

# Claude Full OAuth Auth Code Listener

Checks OAuth localhost callback listener lifecycle and redirect behavior.

## Scenarios

### Claude full OAuth AuthCodeListener

#### should start on requested or assigned port

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should start on requested or assigned port
- Verify: should start on requested or assigned port
- Start listener
   - Expected: assigned.start(0) equals `49152`
   - Expected: assigned.getPort() equals `49152`
   - Expected: fixed.start(4317) equals `4317`
   - Expected: fixed.listening is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should start on requested or assigned port")
step("Verify: should start on requested or assigned port")
# @req: REQ-TOOLS-AuthCodeList-001
step("Start listener")
val assigned = AuthCodeListener.new("")
expect(assigned.start(0)).to_equal(49152)  # oracle: value fixed by the spec contract
expect(assigned.getPort()).to_equal(49152)  # oracle: value fixed by the spec contract
val fixed = AuthCodeListener.new("/cb")
expect(fixed.start(4317)).to_equal(4317)  # oracle: value fixed by the spec contract
expect(fixed.listening).to_equal(true)
```

</details>

#### should prepare authorization wait state and call ready

- should prepare authorization wait state and call ready
- Verify: should prepare authorization wait state and call ready
- Wait for authorization
   - Expected: listener.promiseResolverReady is true
   - Expected: listener.promiseRejecterReady is true
   - Expected: listener.expectedState equals `state-1`
   - Expected: listener.readyCalled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should prepare authorization wait state and call ready")
step("Verify: should prepare authorization wait state and call ready")
# @req: REQ-TOOLS-AuthCodeList-001
step("Wait for authorization")
val listener = AuthCodeListener.new("/callback")
listener.waitForAuthorization("state-1")
expect(listener.promiseResolverReady).to_equal(true)
expect(listener.promiseRejecterReady).to_equal(true)
expect(listener.expectedState).to_equal("state-1")
expect(listener.readyCalled).to_equal(true)
```

</details>

#### should reject non-callback paths with 404

- should reject non-callback paths with 404
- Verify: should reject non-callback paths with 404
- Handle wrong path
   - Expected: res.status equals `404`
   - Expected: res.ended is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject non-callback paths with 404")
step("Verify: should reject non-callback paths with 404")
# @req: REQ-TOOLS-AuthCodeList-001
step("Handle wrong path")
val listener = AuthCodeListener.new("/callback")
val res = AuthCodeResponse.new()
listener.handleRedirect(AuthCodeRequest.new("/wrong?code=a&state=s", "localhost"), res)
expect(res.status).to_equal(404)  # oracle: value fixed by the spec contract
expect(res.ended).to_equal(true)
```

</details>

#### should reject missing code and invalid state

- should reject missing code and invalid state
- Verify: should reject missing code and invalid state
- Validate callback errors
   - Expected: noCode.status equals `400`
   - Expected: listener.rejectedError equals `No authorization code received`
   - Expected: badState.body equals `Invalid state parameter`
   - Expected: listener.rejectedError equals `Invalid state parameter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing code and invalid state")
step("Verify: should reject missing code and invalid state")
# @req: REQ-TOOLS-AuthCodeList-001
step("Validate callback errors")
val listener = AuthCodeListener.new("/callback")
listener.waitForAuthorization("expected")
val noCode = AuthCodeResponse.new()
listener.handleRedirect(AuthCodeRequest.new("/callback?state=expected", "localhost"), noCode)
expect(noCode.status).to_equal(400)  # oracle: value fixed by the spec contract
expect(listener.rejectedError).to_equal("No authorization code received")
listener.waitForAuthorization("expected")
val badState = AuthCodeResponse.new()
listener.handleRedirect(AuthCodeRequest.new("/callback?code=abc&state=bad", "localhost"), badState)
expect(badState.body).to_equal("Invalid state parameter")
expect(listener.rejectedError).to_equal("Invalid state parameter")
```

</details>

#### should resolve valid code and retain pending response

- should resolve valid code and retain pending response
- Verify: should resolve valid code and retain pending response
- Validate successful callback
   - Expected: listener.resolvedCode equals `AUTH`
   - Expected: listener.hasPendingResponse() is true
   - Expected: listener.promiseResolverReady is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should resolve valid code and retain pending response")
step("Verify: should resolve valid code and retain pending response")
# @req: REQ-TOOLS-AuthCodeList-001
step("Validate successful callback")
val listener = AuthCodeListener.new("/callback")
listener.waitForAuthorization("state")
val res = AuthCodeResponse.new()
listener.handleRedirect(AuthCodeRequest.new("/callback?code=AUTH&state=state", "localhost"), res)
expect(listener.resolvedCode).to_equal("AUTH")
expect(listener.hasPendingResponse()).to_equal(true)
expect(listener.promiseResolverReady).to_equal(false)
```

</details>

#### should redirect success based on scopes

- should redirect success based on scopes
- Verify: should redirect success based on scopes
- Complete browser redirect
   - Expected: listener.pendingResponse.status equals `302`
   - Expected: listener.pendingResponse.location equals `https://console.anthropic.com/oauth/success`
   - Expected: listener.hasPendingResponse() is false
   - Expected: listener.logs[0] equals `tengu_oauth_automatic_redirect`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should redirect success based on scopes")
step("Verify: should redirect success based on scopes")
# @req: REQ-TOOLS-AuthCodeList-001
step("Complete browser redirect")
val listener = AuthCodeListener.new("/callback")
listener.waitForAuthorization("s")
listener.handleRedirect(AuthCodeRequest.new("/callback?code=AUTH&state=s", "localhost"), AuthCodeResponse.new())
listener.handleSuccessRedirect(["console"], false)
expect(listener.pendingResponse.status).to_equal(302)  # oracle: value fixed by the spec contract
expect(listener.pendingResponse.location).to_equal("https://console.anthropic.com/oauth/success")
expect(listener.hasPendingResponse()).to_equal(false)
expect(listener.logs[0]).to_equal("tengu_oauth_automatic_redirect")
```

</details>

#### should use custom handler when provided

- should use custom handler when provided
- Verify: should use custom handler when provided
- Complete custom redirect
   - Expected: listener.pendingResponse.status equals `200`
   - Expected: listener.pendingResponse.body equals `custom`
   - Expected: listener.logs[0] equals `tengu_oauth_automatic_redirect:custom_handler`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should use custom handler when provided")
step("Verify: should use custom handler when provided")
# @req: REQ-TOOLS-AuthCodeList-001
step("Complete custom redirect")
val listener = AuthCodeListener.new("/callback")
listener.waitForAuthorization("s")
listener.handleRedirect(AuthCodeRequest.new("/callback?code=AUTH&state=s", "localhost"), AuthCodeResponse.new())
listener.handleSuccessRedirect(["claude"], true)
expect(listener.pendingResponse.status).to_equal(200)  # oracle: value fixed by the spec contract
expect(listener.pendingResponse.body).to_equal("custom")
expect(listener.logs[0]).to_equal("tengu_oauth_automatic_redirect:custom_handler")
```

</details>

#### should redirect pending response on close and handle errors

- should redirect pending response on close and handle errors
- Verify: should redirect pending response on close and handle errors
- Close with pending response
   - Expected: listener.pendingResponse.location equals `https://claude.ai/oauth/success`
   - Expected: listener.closed is true
   - Expected: failed.rejectedError equals `boom`
   - Expected: failed.closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should redirect pending response on close and handle errors")
step("Verify: should redirect pending response on close and handle errors")
# @req: REQ-TOOLS-AuthCodeList-001
step("Close with pending response")
val listener = AuthCodeListener.new("/callback")
listener.waitForAuthorization("s")
listener.handleRedirect(AuthCodeRequest.new("/callback?code=AUTH&state=s", "localhost"), AuthCodeResponse.new())
listener.close()
expect(listener.pendingResponse.location).to_equal("https://claude.ai/oauth/success")
expect(listener.closed).to_equal(true)
val failed = AuthCodeListener.new("/callback")
failed.waitForAuthorization("s")
failed.handleError("boom")
expect(failed.rejectedError).to_equal("boom")
expect(failed.closed).to_equal(true)
```

</details>

#### should expose source-backed helpers

- should expose source-backed helpers
- Verify: should expose source-backed helpers
- Pin helper behavior
   - Expected: requestPath("/callback?x=1") equals `/callback`
   - Expected: queryParam("/callback?code=A&state=B", "state") equals `B`
   - Expected: shouldUseClaudeAIAuth(["read:user"]) is true
   - Expected: authCodeListenerSourceLinesModeled() equals `211`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose source-backed helpers")
step("Verify: should expose source-backed helpers")
# @req: REQ-TOOLS-AuthCodeList-001
step("Pin helper behavior")
expect(requestPath("/callback?x=1")).to_equal("/callback")
expect(queryParam("/callback?code=A&state=B", "state")).to_equal("B")
expect(shouldUseClaudeAIAuth(["read:user"])).to_equal(true)
expect(authCodeListenerSourceLinesModeled()).to_equal(211)  # oracle: value fixed by the spec contract
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-AuthCodeList-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `51fccdcd1cad896887e32e00526ae7885dbbcd7a6cf8e0898ef1dca7c0be83f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `51fccdcd1cad896887e32e00526ae7885dbbcd7a6cf8e0898ef1dca7c0be83f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `51fccdcd1cad896887e32e00526ae7885dbbcd7a6cf8e0898ef1dca7c0be83f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/services/oauth/auth-code-listener_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/services/oauth/auth-code-listener_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/services/oauth/auth-code-listener_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/services/oauth/auth-code-listener_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/services/oauth/auth-code-listener_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should start on requested or assigned port' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/oauth/auth-code-listener_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should start on requested or assigned port' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/oauth/auth-code-listener_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should prepare authorization wait state and call ready' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/oauth/auth-code-listener_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should prepare authorization wait state and call ready' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/oauth/auth-code-listener_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject non-callback paths with 404' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/oauth/auth-code-listener_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject non-callback paths with 404' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/oauth/auth-code-listener_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing code and invalid state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/oauth/auth-code-listener_spec.spl:80:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should resolve valid code and retain pending response' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/oauth/auth-code-listener_spec.spl:94:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should redirect success based on scopes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
