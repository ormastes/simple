# Claude Full With Retry

> Pins deterministic behavior for the Claude CLI `withRetry.ts` retry utility: foreground/background 529 policy, retry delay calculation, context overflow adjustment, fallback errors, provider auth retry decisions, and reset-delay helpers.

<!-- sdn-diagram:id=withRetry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=withRetry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

withRetry_spec -> std
withRetry_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=withRetry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full With Retry

Pins deterministic behavior for the Claude CLI `withRetry.ts` retry utility: foreground/background 529 policy, retry delay calculation, context overflow adjustment, fallback errors, provider auth retry decisions, and reset-delay helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A - strict llm_caret Claude CLI parity lane. |
| Plan | N/A - target selected from strict checker output. |
| Design | N/A - source mirror for `tmp/claude/claude-code-main/src/services/api/withRetry.ts`. |
| Research | N/A - upstream TypeScript file is the source reference. |
| Source | `test/03_system/tools/llm/claude_full/services/api/withRetry_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Pins deterministic behavior for the Claude CLI `withRetry.ts` retry utility:
foreground/background 529 policy, retry delay calculation, context overflow
adjustment, fallback errors, provider auth retry decisions, and reset-delay
helpers.

**Requirements:** N/A - strict llm_caret Claude CLI parity lane.
**Plan:** N/A - target selected from strict checker output.
**Design:** N/A - source mirror for `tmp/claude/claude-code-main/src/services/api/withRetry.ts`.
**Research:** N/A - upstream TypeScript file is the source reference.

## Scenarios

### Claude full withRetry

#### should classify foreground 529 retry sources

- Compare foreground and background query sources
   - Expected: shouldRetry529("") is true
   - Expected: shouldRetry529("repl_main_thread") is true
   - Expected: shouldRetry529("title") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare foreground and background query sources")
expect(shouldRetry529("")).to_equal(true)
expect(shouldRetry529("repl_main_thread")).to_equal(true)
expect(shouldRetry529("title")).to_equal(false)
```

</details>

#### should build retry errors with source names

- Create CannotRetryError and fallback error
   - Expected: cannot.name equals `RetryError`
   - Expected: fallback.name equals `FallbackTriggeredError`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create CannotRetryError and fallback error")
val context = RetryContext.new("opus")
val cannot = CannotRetryError.new("nope", context)
val fallback = FallbackTriggeredError.new("opus", "sonnet")
expect(cannot.name).to_equal("RetryError")
expect(fallback.name).to_equal("FallbackTriggeredError")
expect(fallback.message).to_contain("opus -> sonnet")
```

</details>

#### should compute retry delay from retry-after or exponential backoff

- Check header override and default exponential delay
   - Expected: getRetryDelay(4, "7", 32000, 0) equals `7000`
   - Expected: getRetryDelay(3, "", 32000, 25) equals `2025`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check header override and default exponential delay")
expect(getRetryDelay(4, "7", 32000, 0)).to_equal(7000)
expect(getRetryDelay(3, "", 32000, 25)).to_equal(2025)
```

</details>

#### should parse context overflow errors and adjust max tokens

- Handle max token overflow
   - Expected: outcome.status equals `retry`
   - Expected: outcome.context.maxTokensOverride equals `10941`
   - Expected: model.logs[0] equals `tengu_max_tokens_context_overflow_adjustment`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Handle max token overflow")
val options = RetryOptions.new("opus")
val model = WithRetryModel.new(options)
val error = ApiError.new(400, "input length and `max_tokens` exceed context limit: 188059 + 20000 > 200000")
val outcome = model.handleError(error, 1)
expect(outcome.status).to_equal("retry")
expect(outcome.context.maxTokensOverride).to_equal(10941)
expect(model.logs[0]).to_equal("tengu_max_tokens_context_overflow_adjustment")
```

</details>

#### should drop background 529 without retry amplification

- Use non-foreground query source
   - Expected: outcome.status equals `fail`
   - Expected: outcome.errorName equals `RetryError`
   - Expected: model.logs[0] equals `tengu_api_529_background_dropped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use non-foreground query source")
val options = RetryOptions.new("opus")
options.querySource = "title"
val model = WithRetryModel.new(options)
val outcome = model.handleError(ApiError.new(529, "overloaded"), 1)
expect(outcome.status).to_equal("fail")
expect(outcome.errorName).to_equal("RetryError")
expect(model.logs[0]).to_equal("tengu_api_529_background_dropped")
```

</details>

#### should trigger fallback after repeated 529 errors

- Seed two prior 529s and provide fallback model
   - Expected: outcome.status equals `fail`
   - Expected: outcome.errorName equals `FallbackTriggeredError`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed two prior 529s and provide fallback model")
val options = RetryOptions.new("opus")
options.initialConsecutive529Errors = 2
options.fallbackModel = "sonnet"
val model = WithRetryModel.new(options)
val outcome = model.handleError(ApiError.new(529, "overloaded"), 1)
expect(outcome.status).to_equal("fail")
expect(outcome.errorName).to_equal("FallbackTriggeredError")
```

</details>

#### should honor shouldRetry header and subscriber gates

- Check retry header decisions
   - Expected: shouldRetryWithOptions(err, external) is false
   - Expected: shouldRetryWithOptions(err, ant) is true
   - Expected: shouldRetryWithOptions(rate, sub) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check retry header decisions")
val err = ApiError.new(500, "server")
err.shouldRetryHeader = "false"
val external = RetryOptions.new("opus")
expect(shouldRetryWithOptions(err, external)).to_equal(false)
val ant = RetryOptions.new("opus")
ant.antUser = true
expect(shouldRetryWithOptions(err, ant)).to_equal(true)
val rate = ApiError.new(429, "rate")
val sub = RetryOptions.new("opus")
sub.claudeAiSubscriber = true
expect(shouldRetryWithOptions(rate, sub)).to_equal(false)
```

</details>

#### should classify provider auth and stale connection errors

- Check cloud and connection helpers
   - Expected: isStaleConnectionError(ApiError.connection("ECONNRESET")) is true
   - Expected: isBedrockAuthError(ApiError.new(403, "bad"), true, false) is true
   - Expected: isGoogleAuthLibraryCredentialError("Could not refresh access token") is true
   - Expected: isVertexAuthError(ApiError.new(401, "expired"), true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check cloud and connection helpers")
expect(isStaleConnectionError(ApiError.connection("ECONNRESET"))).to_equal(true)
expect(isBedrockAuthError(ApiError.new(403, "bad"), true, false)).to_equal(true)
expect(isGoogleAuthLibraryCredentialError("Could not refresh access token")).to_equal(true)
expect(isVertexAuthError(ApiError.new(401, "expired"), true)).to_equal(true)
```

</details>

#### should cap rate-limit reset delay

- Compute reset delay
   - Expected: getRateLimitResetDelayMs(err, 99000) equals `1000`
   - Expected: getRateLimitResetDelayMs(err, 0) equals `21600000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compute reset delay")
val err = ApiError.new(429, "rate")
err.resetUnixSec = 100
expect(getRateLimitResetDelayMs(err, 99000)).to_equal(1000)
err.resetUnixSec = 999999
expect(getRateLimitResetDelayMs(err, 0)).to_equal(21600000)
```

</details>

#### should expose source-backed constants

- Pin source surface
   - Expected: abortError() equals `APIUserAbortError`
   - Expected: baseDelayMs() equals `500`
   - Expected: withRetrySourceLinesModeled() equals `822`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin source surface")
expect(abortError()).to_equal("APIUserAbortError")
expect(baseDelayMs()).to_equal(500)
expect(withRetrySourceLinesModeled()).to_equal(822)
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

- **Requirements:** [N/A - strict llm_caret Claude CLI parity lane.](N/A - strict llm_caret Claude CLI parity lane.)
- **Plan:** [N/A - target selected from strict checker output.](N/A - target selected from strict checker output.)
- **Design:** [N/A - source mirror for `tmp/claude/claude-code-main/src/services/api/withRetry.ts`.](N/A - source mirror for `tmp/claude/claude-code-main/src/services/api/withRetry.ts`.)
- **Research:** [N/A - upstream TypeScript file is the source reference.](N/A - upstream TypeScript file is the source reference.)


</details>
