# Claude Full Bridge JWT Utils

> Mirrors JWT expiry decoding and deterministic token refresh scheduling.

<!-- sdn-diagram:id=jwtUtils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jwtUtils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jwtUtils_spec -> std
jwtUtils_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jwtUtils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors JWT expiry decoding and deterministic token refresh scheduling.

## Scenarios

### Claude full bridge JWT utils

#### decodes JWT payloads and exp claims

- Strip session ingress prefix and decode the payload segment
   - Expected: stripSessionIngressPrefix("sk-ant-si-h.{\"exp\":12345}.s") equals `h.{"exp":12345}.s`
   - Expected: jwtPayloadSegment("h.{\"exp\":12345}.s") equals `{"exp":12345}`
   - Expected: decodeJwtPayload("h.eyJleHAiOjEyMzQ1fQ.s") equals `{"exp":12345}`
   - Expected: decodeJwtExpiry("sk-ant-si-h.eyJleHAiOjEyMzQ1fQ.s") equals `12345`
   - Expected: decodeJwtExpiry("bad-token") equals `0`
   - Expected: decodeJwtExpiry("h..s") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Format seconds and minute-second durations
   - Expected: formatDuration(12000) equals `12s`
   - Expected: formatDuration(65000) equals `1m 5s`
   - Expected: formatDuration(1800000) equals `30m`
   - Expected: tokenRefreshBufferMs() equals `300000`
   - Expected: fallbackRefreshIntervalMs() equals `1800000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Format seconds and minute-second durations")
expect(formatDuration(12000)).to_equal("12s")
expect(formatDuration(65000)).to_equal("1m 5s")
expect(formatDuration(1800000)).to_equal("30m")
expect(tokenRefreshBufferMs()).to_equal(300000)
expect(fallbackRefreshIntervalMs()).to_equal(1800000)
```

</details>

#### schedules JWT refresh before expiry and keeps existing timer for opaque tokens

- Schedule using exp minus current time and buffer
- scheduler schedule
   - Expected: scheduler.timerDelay("cse_1") equals `300000`
   - Expected: scheduler.timerGeneration("cse_1") equals `1`
- scheduler schedule
   - Expected: scheduler.timerDelay("cse_1") equals `300000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Call onRefresh synchronously in the deterministic model
- scheduler setOAuthToken
- scheduler schedule
   - Expected: scheduler.refreshedToken("cse_2") equals `oauth`
   - Expected: scheduler.timerDelay("cse_2") equals `1800000`
   - Expected: scheduler.analytics[0] equals `tengu_bridge_token_refreshed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Clamp very short TTLs to avoid a tight loop
- scheduler scheduleFromExpiresIn
   - Expected: scheduler.timerDelay("cse_short") equals `30000`
- scheduler scheduleFromExpiresIn
   - Expected: scheduler.timerDelay("cse_long") equals `600000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Clamp very short TTLs to avoid a tight loop")
val scheduler = createTokenRefreshSchedulerWithBuffer("bridge", 0, 300000)
scheduler.scheduleFromExpiresIn("cse_short", 60)
expect(scheduler.timerDelay("cse_short")).to_equal(30000)
scheduler.scheduleFromExpiresIn("cse_long", 900)
expect(scheduler.timerDelay("cse_long")).to_equal(600000)
```

</details>

#### retries missing OAuth tokens and stops after max failures

- Retry no-token refreshes with diagnostics and cap failures
- scheduler doRefresh
   - Expected: scheduler.failureCount("cse_3") equals `1`
   - Expected: scheduler.timerDelay("cse_3") equals `refreshRetryDelayMs()`
   - Expected: scheduler.diagnostics[0] equals `bridge_token_refresh_no_oauth`
- scheduler doRefresh
- scheduler doRefresh
   - Expected: scheduler.failureCount("cse_3") equals `maxRefreshFailures()`
   - Expected: scheduler.hasTimer("cse_3") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Invalidate in-flight refresh work
- scheduler nextGeneration
- scheduler setOAuthToken
- scheduler doRefresh
   - Expected: scheduler.refreshedToken("cse_4") equals ``
- scheduler scheduleFromExpiresIn
   - Expected: scheduler.hasTimer("cse_4") is true
- scheduler cancel
   - Expected: scheduler.hasTimer("cse_4") is false
   - Expected: scheduler.failureCount("cse_4") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
