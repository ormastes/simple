# Claude Full Bridge JWT Utils

> Mirrors JWT expiry decoding and deterministic token refresh scheduling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge JWT Utils

Mirrors JWT expiry decoding and deterministic token refresh scheduling.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bridge/jwtUtils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors JWT expiry decoding and deterministic token refresh scheduling.

## Scenarios

### Claude full bridge JWT utils

#### decodes JWT payloads and exp claims

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- decodes JWT payloads and exp claims
- Strip session ingress prefix and decode the payload segment
   - Expected: stripSessionIngressPrefix("sk-ant-si-h.{\"exp\":12345}.s") equals `h.{"exp":12345}.s`
   - Expected: jwtPayloadSegment("h.{\"exp\":12345}.s") equals `{"exp":12345}`
   - Expected: decodeJwtPayload("h.eyJleHAiOjEyMzQ1fQ.s") equals `{"exp":12345}`
   - Expected: decodeJwtExpiry("sk-ant-si-h.eyJleHAiOjEyMzQ1fQ.s") equals `12345`
   - Expected: decodeJwtExpiry("bad-token") equals `0`
   - Expected: decodeJwtExpiry("h..s") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("decodes JWT payloads and exp claims")
step("Strip session ingress prefix and decode the payload segment")
expect(stripSessionIngressPrefix("sk-ant-si-h.{\"exp\":12345}.s")).to_equal("h.{\"exp\":12345}.s")
expect(jwtPayloadSegment("h.{\"exp\":12345}.s")).to_equal("{\"exp\":12345}")
expect(decodeJwtPayload("h.eyJleHAiOjEyMzQ1fQ.s")).to_equal("{\"exp\":12345}")
expect(decodeJwtExpiry("sk-ant-si-h.eyJleHAiOjEyMzQ1fQ.s")).to_equal(12345)
expect(decodeJwtExpiry("bad-token")).to_equal(0)
expect(decodeJwtExpiry("h..s")).to_equal(0)
```

</details>

#### formats refresh delays like the TypeScript helper

- formats refresh delays like the TypeScript helper
- Format seconds and minute-second durations
   - Expected: formatDuration(12000) equals `12s`
   - Expected: formatDuration(65000) equals `1m 5s`
   - Expected: formatDuration(1800000) equals `30m`
   - Expected: tokenRefreshBufferMs() equals `300000`
   - Expected: fallbackRefreshIntervalMs() equals `1800000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats refresh delays like the TypeScript helper")
step("Format seconds and minute-second durations")
expect(formatDuration(12000)).to_equal("12s")
expect(formatDuration(65000)).to_equal("1m 5s")
expect(formatDuration(1800000)).to_equal("30m")
expect(tokenRefreshBufferMs()).to_equal(300000)
expect(fallbackRefreshIntervalMs()).to_equal(1800000)
```

</details>

#### schedules JWT refresh before expiry and keeps existing timer for opaque tokens

- schedules JWT refresh before expiry and keeps existing timer for opaque tokens
- Schedule using exp minus current time and buffer
   - Expected: scheduler.timerDelay("cse_1") equals `300000`
   - Expected: scheduler.timerGeneration("cse_1") equals `1`
   - Expected: scheduler.timerDelay("cse_1") equals `300000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("schedules JWT refresh before expiry and keeps existing timer for opaque tokens")
step("Schedule using exp minus current time and buffer")
val scheduler = createTokenRefreshScheduler("bridge", 1000000)
scheduler.schedule("cse_1", "h.{\"exp\":1600}.s")
expect(scheduler.timerDelay("cse_1")).to_equal(300000)
expect(scheduler.timerGeneration("cse_1")).to_equal(1)
scheduler.schedule("cse_1", "opaque")
expect(scheduler.timerDelay("cse_1")).to_equal(300000)
expect(scheduler.logs[scheduler.logs.len() - 1]).to_contain("Could not decode JWT expiry")
```

</details>

#### refreshes immediately when token is inside the buffer

- refreshes immediately when token is inside the buffer
- Call onRefresh synchronously in the deterministic model
   - Expected: scheduler.refreshedToken("cse_2") equals `oauth`
   - Expected: scheduler.timerDelay("cse_2") equals `1800000`
   - Expected: scheduler.analytics[0] equals `tengu_bridge_token_refreshed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refreshes immediately when token is inside the buffer")
step("Call onRefresh synchronously in the deterministic model")
val scheduler = createTokenRefreshScheduler("bridge", 1000000)
scheduler.setOAuthToken("oauth")
scheduler.schedule("cse_2", "h.{\"exp\":1200}.s")
expect(scheduler.refreshedToken("cse_2")).to_equal("oauth")
expect(scheduler.timerDelay("cse_2")).to_equal(1800000)
expect(scheduler.analytics[0]).to_equal("tengu_bridge_token_refreshed")
```

</details>

#### uses expires_in with a 30s floor

- uses expires_in with a 30s floor
- Clamp very short TTLs to avoid a tight loop
   - Expected: scheduler.timerDelay("cse_short") equals `30000`
   - Expected: scheduler.timerDelay("cse_long") equals `600000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses expires_in with a 30s floor")
step("Clamp very short TTLs to avoid a tight loop")
val scheduler = createTokenRefreshSchedulerWithBuffer("bridge", 0, 300000)
scheduler.scheduleFromExpiresIn("cse_short", 60)
expect(scheduler.timerDelay("cse_short")).to_equal(30000)
scheduler.scheduleFromExpiresIn("cse_long", 900)
expect(scheduler.timerDelay("cse_long")).to_equal(600000)
```

</details>

#### retries missing OAuth tokens and stops after max failures

- retries missing OAuth tokens and stops after max failures
- Retry no-token refreshes with diagnostics and cap failures
   - Expected: scheduler.failureCount("cse_3") equals `1`
   - Expected: scheduler.timerDelay("cse_3") equals `refreshRetryDelayMs()`
   - Expected: scheduler.diagnostics[0] equals `bridge_token_refresh_no_oauth`
   - Expected: scheduler.failureCount("cse_3") equals `maxRefreshFailures()`
   - Expected: scheduler.hasTimer("cse_3") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retries missing OAuth tokens and stops after max failures")
step("Retry no-token refreshes with diagnostics and cap failures")
val scheduler = createTokenRefreshScheduler("bridge", 0)
val gen = scheduler.nextGeneration("cse_3")
scheduler.doRefresh("cse_3", gen)
expect(scheduler.failureCount("cse_3")).to_equal(1)
expect(scheduler.timerDelay("cse_3")).to_equal(refreshRetryDelayMs())
expect(scheduler.diagnostics[0]).to_equal("bridge_token_refresh_no_oauth")
scheduler.doRefresh("cse_3", gen)
scheduler.doRefresh("cse_3", gen)
expect(scheduler.failureCount("cse_3")).to_equal(maxRefreshFailures())
expect(scheduler.hasTimer("cse_3")).to_equal(false)
```

</details>

#### skips stale refresh generations and supports cancel

- skips stale refresh generations and supports cancel
- Invalidate in-flight refresh work
   - Expected: scheduler.refreshedToken("cse_4") equals ``
   - Expected: scheduler.hasTimer("cse_4") is true
   - Expected: scheduler.hasTimer("cse_4") is false
   - Expected: scheduler.failureCount("cse_4") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips stale refresh generations and supports cancel")
step("Invalidate in-flight refresh work")
val scheduler = createTokenRefreshScheduler("bridge", 0)
val gen = scheduler.nextGeneration("cse_4")
scheduler.nextGeneration("cse_4")
scheduler.setOAuthToken("oauth")
scheduler.doRefresh("cse_4", gen)
expect(scheduler.refreshedToken("cse_4")).to_equal("")
expect(scheduler.logs[0]).to_contain("stale")
scheduler.scheduleFromExpiresIn("cse_4", 900)
expect(scheduler.hasTimer("cse_4")).to_equal(true)
scheduler.cancel("cse_4")
expect(scheduler.hasTimer("cse_4")).to_equal(false)
expect(scheduler.failureCount("cse_4")).to_equal(0)
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `23af24302117ff6c2ec6535a71683d4e01e9cc9acc101a71f658b8a8239ed9b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `23af24302117ff6c2ec6535a71683d4e01e9cc9acc101a71f658b8a8239ed9b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `23af24302117ff6c2ec6535a71683d4e01e9cc9acc101a71f658b8a8239ed9b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/bridge/jwtUtils_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/bridge/jwtUtils_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/bridge/jwtUtils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/bridge/jwtUtils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/bridge/jwtUtils_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/bridge/jwtUtils_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes JWT payloads and exp claims' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/jwtUtils_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats refresh delays like the TypeScript helper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/jwtUtils_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'schedules JWT refresh before expiry and keeps existing timer for opaque tokens' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
