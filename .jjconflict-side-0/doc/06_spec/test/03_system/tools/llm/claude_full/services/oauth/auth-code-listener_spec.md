# Claude Full OAuth Auth Code Listener

> Checks OAuth localhost callback listener lifecycle and redirect behavior.

<!-- sdn-diagram:id=auth-code-listener_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=auth-code-listener_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

auth-code-listener_spec -> std
auth-code-listener_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=auth-code-listener_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full OAuth Auth Code Listener

Checks OAuth localhost callback listener lifecycle and redirect behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/services/oauth/auth-code-listener_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks OAuth localhost callback listener lifecycle and redirect behavior.

## Scenarios

### Claude full OAuth AuthCodeListener

#### should start on requested or assigned port

- Start listener
   - Expected: assigned.start(0) equals `49152`
   - Expected: assigned.getPort() equals `49152`
   - Expected: fixed.start(4317) equals `4317`
   - Expected: fixed.listening is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Start listener")
val assigned = AuthCodeListener.new("")
expect(assigned.start(0)).to_equal(49152)
expect(assigned.getPort()).to_equal(49152)
val fixed = AuthCodeListener.new("/cb")
expect(fixed.start(4317)).to_equal(4317)
expect(fixed.listening).to_equal(true)
```

</details>

#### should prepare authorization wait state and call ready

- Wait for authorization
- listener waitForAuthorization
   - Expected: listener.promiseResolverReady is true
   - Expected: listener.promiseRejecterReady is true
   - Expected: listener.expectedState equals `state-1`
   - Expected: listener.readyCalled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Handle wrong path
- listener handleRedirect
   - Expected: res.status equals `404`
   - Expected: res.ended is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Handle wrong path")
val listener = AuthCodeListener.new("/callback")
val res = AuthCodeResponse.new()
listener.handleRedirect(AuthCodeRequest.new("/wrong?code=a&state=s", "localhost"), res)
expect(res.status).to_equal(404)
expect(res.ended).to_equal(true)
```

</details>

#### should reject missing code and invalid state

- Validate callback errors
- listener waitForAuthorization
- listener handleRedirect
   - Expected: noCode.status equals `400`
   - Expected: listener.rejectedError equals `No authorization code received`
- listener waitForAuthorization
- listener handleRedirect
   - Expected: badState.body equals `Invalid state parameter`
   - Expected: listener.rejectedError equals `Invalid state parameter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate callback errors")
val listener = AuthCodeListener.new("/callback")
listener.waitForAuthorization("expected")
val noCode = AuthCodeResponse.new()
listener.handleRedirect(AuthCodeRequest.new("/callback?state=expected", "localhost"), noCode)
expect(noCode.status).to_equal(400)
expect(listener.rejectedError).to_equal("No authorization code received")
listener.waitForAuthorization("expected")
val badState = AuthCodeResponse.new()
listener.handleRedirect(AuthCodeRequest.new("/callback?code=abc&state=bad", "localhost"), badState)
expect(badState.body).to_equal("Invalid state parameter")
expect(listener.rejectedError).to_equal("Invalid state parameter")
```

</details>

#### should resolve valid code and retain pending response

- Validate successful callback
- listener waitForAuthorization
- listener handleRedirect
   - Expected: listener.resolvedCode equals `AUTH`
   - Expected: listener.hasPendingResponse() is true
   - Expected: listener.promiseResolverReady is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Complete browser redirect
- listener waitForAuthorization
- listener handleRedirect
- listener handleSuccessRedirect
   - Expected: listener.pendingResponse.status equals `302`
   - Expected: listener.pendingResponse.location equals `https://console.anthropic.com/oauth/success`
   - Expected: listener.hasPendingResponse() is false
   - Expected: listener.logs[0] equals `tengu_oauth_automatic_redirect`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Complete browser redirect")
val listener = AuthCodeListener.new("/callback")
listener.waitForAuthorization("s")
listener.handleRedirect(AuthCodeRequest.new("/callback?code=AUTH&state=s", "localhost"), AuthCodeResponse.new())
listener.handleSuccessRedirect(["console"], false)
expect(listener.pendingResponse.status).to_equal(302)
expect(listener.pendingResponse.location).to_equal("https://console.anthropic.com/oauth/success")
expect(listener.hasPendingResponse()).to_equal(false)
expect(listener.logs[0]).to_equal("tengu_oauth_automatic_redirect")
```

</details>

#### should use custom handler when provided

- Complete custom redirect
- listener waitForAuthorization
- listener handleRedirect
- listener handleSuccessRedirect
   - Expected: listener.pendingResponse.status equals `200`
   - Expected: listener.pendingResponse.body equals `custom`
   - Expected: listener.logs[0] equals `tengu_oauth_automatic_redirect:custom_handler`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Complete custom redirect")
val listener = AuthCodeListener.new("/callback")
listener.waitForAuthorization("s")
listener.handleRedirect(AuthCodeRequest.new("/callback?code=AUTH&state=s", "localhost"), AuthCodeResponse.new())
listener.handleSuccessRedirect(["claude"], true)
expect(listener.pendingResponse.status).to_equal(200)
expect(listener.pendingResponse.body).to_equal("custom")
expect(listener.logs[0]).to_equal("tengu_oauth_automatic_redirect:custom_handler")
```

</details>

#### should redirect pending response on close and handle errors

- Close with pending response
- listener waitForAuthorization
- listener handleRedirect
- listener close
   - Expected: listener.pendingResponse.location equals `https://claude.ai/oauth/success`
   - Expected: listener.closed is true
- failed waitForAuthorization
- failed handleError
   - Expected: failed.rejectedError equals `boom`
   - Expected: failed.closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Pin helper behavior
   - Expected: requestPath("/callback?x=1") equals `/callback`
   - Expected: queryParam("/callback?code=A&state=B", "state") equals `B`
   - Expected: shouldUseClaudeAIAuth(["read:user"]) is true
   - Expected: authCodeListenerSourceLinesModeled() equals `211`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin helper behavior")
expect(requestPath("/callback?x=1")).to_equal("/callback")
expect(queryParam("/callback?code=A&state=B", "state")).to_equal("B")
expect(shouldUseClaudeAIAuth(["read:user"])).to_equal(true)
expect(authCodeListenerSourceLinesModeled()).to_equal(211)
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
