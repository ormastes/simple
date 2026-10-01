# Claude Full Create Direct Connect Session

> Checks direct-connect request construction and error handling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Create Direct Connect Session

Checks direct-connect request construction and error handling.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/server/createDirectConnectSession_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks direct-connect request construction and error handling.

## Scenarios

### Claude full createDirectConnectSession

#### should construct DirectConnectError with stable name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should construct DirectConnectError with stable name
- Create a direct-connect error
   - Expected: error.name equals `DirectConnectError`
   - Expected: error.message equals `bad`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should construct DirectConnectError with stable name")
step("Create a direct-connect error")
val error = DirectConnectError.new("bad")
expect(error.name).to_equal("DirectConnectError")
expect(error.message).to_equal("bad")
```

</details>

#### should create successful direct connect config

- should create successful direct connect config
- Create session from a valid response
   - Expected: result.ok is true
   - Expected: result.requestUrl equals `https://server/sessions`
   - Expected: result.requestBody equals `{"cwd":"/repo","dangerously_skip_permissions":true}`
   - Expected: result.authorizationHeader equals `Bearer tok`
   - Expected: result.config.sessionId equals `sess-1`
   - Expected: result.config.wsUrl equals `wss://server/ws`
   - Expected: result.workDir equals `/work`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create successful direct connect config")
step("Create session from a valid response")
val request = directConnectRequest("https://server", "tok", "/repo", true)
val result = createDirectConnectSession(request, true, true, 200, "OK", "sess-1", "wss://server/ws", "/work", true, "")
expect(result.ok).to_equal(true)
expect(result.requestUrl).to_equal("https://server/sessions")
expect(result.requestBody).to_equal("{\"cwd\":\"/repo\",\"dangerously_skip_permissions\":true}")
expect(result.authorizationHeader).to_equal("Bearer tok")
expect(result.config.sessionId).to_equal("sess-1")
expect(result.config.wsUrl).to_equal("wss://server/ws")
expect(result.workDir).to_equal("/work")
```

</details>

#### should omit auth and skip-permission fields when absent

- should omit auth and skip-permission fields when absent
- Create request without optional fields
   - Expected: result.requestBody equals `{"cwd":"/repo"}`
   - Expected: result.authorizationHeader equals ``
   - Expected: result.config.authToken equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should omit auth and skip-permission fields when absent")
step("Create request without optional fields")
val request = directConnectRequest("http://localhost:8000", "", "/repo", false)
val result = createDirectConnectSession(request, true, true, 201, "Created", "s", "ws://x", "", true, "")
expect(result.requestBody).to_equal("{\"cwd\":\"/repo\"}")
expect(result.authorizationHeader).to_equal("")
expect(result.config.authToken).to_equal("")
```

</details>

#### should fail on network errors

- should fail on network errors
- Simulate fetch failure
   - Expected: result.ok is false
   - Expected: error.message equals `Failed to connect to server at https://server: ECONNREFUSED`
   - Expected: "missing" equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fail on network errors")
step("Simulate fetch failure")
val request = directConnectRequest("https://server", "", "/repo", false)
val result = createDirectConnectSession(request, false, false, 0, "", "", "", "", false, "ECONNREFUSED")
expect(result.ok).to_equal(false)
if val Some(error) = result.error:
    expect(error.message).to_equal("Failed to connect to server at https://server: ECONNREFUSED")
else:
    expect("missing").to_equal("error")
```

</details>

#### should fail on non-ok HTTP responses

- should fail on non-ok HTTP responses
- Simulate HTTP failure
   - Expected: result.ok is false
   - Expected: error.message equals `Failed to create session: 500 Server Error`
   - Expected: "missing" equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fail on non-ok HTTP responses")
step("Simulate HTTP failure")
val request = directConnectRequest("https://server", "", "/repo", false)
val result = createDirectConnectSession(request, true, false, 500, "Server Error", "", "", "", false, "")
expect(result.ok).to_equal(false)
if val Some(error) = result.error:
    expect(error.message).to_equal("Failed to create session: 500 Server Error")
else:
    expect("missing").to_equal("error")
```

</details>

#### should fail on invalid response schema

- should fail on invalid response schema
- Simulate invalid response
   - Expected: result.ok is false
   - Expected: error.message equals `Invalid session response: schema validation failed`
   - Expected: "missing" equals `error`
   - Expected: createDirectConnectSessionSourceLinesModeled() equals `88`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fail on invalid response schema")
step("Simulate invalid response")
val request = directConnectRequest("https://server", "", "/repo", false)
val result = createDirectConnectSession(request, true, true, 200, "OK", "", "", "", false, "")
expect(result.ok).to_equal(false)
if val Some(error) = result.error:
    expect(error.message).to_equal("Invalid session response: schema validation failed")
else:
    expect("missing").to_equal("error")
expect(createDirectConnectSessionSourceLinesModeled()).to_equal(88)
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

- Canonical SPipe generation for source `f0809166f4d80409276a79699faaf8b2693ce6f1b8b2804c48b43ec72f2a27e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f0809166f4d80409276a79699faaf8b2693ce6f1b8b2804c48b43ec72f2a27e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f0809166f4d80409276a79699faaf8b2693ce6f1b8b2804c48b43ec72f2a27e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/server/createDirectConnectSession_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/server/createDirectConnectSession_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/server/createDirectConnectSession_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/server/createDirectConnectSession_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/server/createDirectConnectSession_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/server/createDirectConnectSession_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct DirectConnectError with stable name' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/server/createDirectConnectSession_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should construct DirectConnectError with stable name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/server/createDirectConnectSession_spec.spl:26:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create successful direct connect config' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/server/createDirectConnectSession_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create successful direct connect config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/server/createDirectConnectSession_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should omit auth and skip-permission fields when absent' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/server/createDirectConnectSession_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should omit auth and skip-permission fields when absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/server/createDirectConnectSession_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail on network errors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/server/createDirectConnectSession_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail on non-ok HTTP responses' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/server/createDirectConnectSession_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail on invalid response schema' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
