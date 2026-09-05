# Claude Full withRetry

> Deterministic supporting parts-bin evidence for Claude-full retry policy,
> sequences, provider recovery effects, and context-overflow boundaries.

| Field | Value |
|---|---|
| Source | `test/03_system/tools/llm/claude_full/services/api/withRetry_spec.spl` |
| Executable scenarios | 18 |
| Execution in this tranche | 0 scenarios executed |
| Result | Not executed; no PASS is claimed |
| Requirement | N/A; supporting Claude-full parts-bin evidence |

## Scope and Claim Boundary

This manual mirrors deterministic behavior from `withRetry.spl`: foreground and
background policy, bounded and persistent retry sequences, exact modeled delay
and heartbeat traces, provider cache/cooldown effects, overflow limits,
fallback, and retry headers. It does not claim shipped CLI/TUI reachability,
live provider behavior, wall-clock sleeps, network access, or process execution.

Capping Retry-After at `maxDelayMs` is intentional deterministic hardening. The
upstream TypeScript source is absent, so this manual does not claim that
boundary as proven upstream-exact parity.

The scenarios call the real exported `WithRetryModel.handleError` decision path
through `run_retry_sequence`; trace arrays are deterministic effect records, not
evidence that external effects occurred.

`handleError` caches the whole outcome by attempt ID. Immediate or
nonconsecutive reuse returns the same outcome object and must not duplicate any
log, status, sleep, heartbeat, cache-clear, or cooldown record.

## Fixture and Checker Contracts

`setup_retry_sequence_fixture(status, count, retryAfter)` creates exactly
`count` `ApiError` values with the requested status and Retry-After text.
`run_retry_sequence(model, errors)` is the exported source seam: it assigns
one-based attempts, invokes `handleError`, stops on a terminal result, and
aggregates retry delay and heartbeat counts. `check_retry_sequence(...)`
asserts the complete aggregate envelope.

<details>
<summary>Executable helper source</summary>

```simple
fn setup_retry_sequence_fixture(status: i64, count: i64, retryAfter: text) -> [ApiError]:
    var errors: [ApiError] = []
    var i = 0
    while i < count:
        val error = ApiError.new(status, "retry fixture")
        error.retryAfter = retryAfter
        errors.push(error)
        i = i + 1
    errors

fn run_retry_sequence(model: WithRetryModel, errors: [ApiError]) -> RetrySequenceResult:
    val result = RetrySequenceResult.new()
    var i = 0
    while i < errors.len():
        val outcome = model.handleError(errors[i], i + 1)
        result.outcomes.push(outcome)
        if outcome.status == "retry":
            result.totalDelayMs = result.totalDelayMs + outcome.delayMs
            result.yieldedHeartbeats = result.yieldedHeartbeats + outcome.yieldedHeartbeats
        else:
            result.terminalStatus = outcome.status
            result.terminalError = outcome.errorMessage
            return result
        i = i + 1
    if result.outcomes.len() > 0:
        result.terminalStatus = result.outcomes[result.outcomes.len() - 1].status
    result

fn check_retry_sequence(result: RetrySequenceResult, expectedOutcomeCount: i64, expectedTotalDelayMs: i64, expectedHeartbeats: i64, expectedTerminalStatus: text, expectedTerminalError: text):
    expect(result.outcomes.len()).to_equal(expectedOutcomeCount)
    expect(result.totalDelayMs).to_equal(expectedTotalDelayMs)
    expect(result.yieldedHeartbeats).to_equal(expectedHeartbeats)
    expect(result.terminalStatus).to_equal(expectedTerminalStatus)
    expect(result.terminalError).to_equal(expectedTerminalError)
```

</details>

## Scenarios

### Supporting source-policy parts-bin behavior

#### should classify foreground and background 529 sources

- Compare foreground, SDK, and background query sources

<details>
<summary>Executable SSpec</summary>

```simple
it "should classify foreground and background 529 sources":
    step("Compare foreground, SDK, and background query sources")
    expect(shouldRetry529("")).to_equal(true)
    expect(shouldRetry529("repl_main_thread")).to_equal(true)
    expect(shouldRetry529("sdk")).to_equal(true)
    expect(shouldRetry529("title")).to_equal(false)
```

</details>

#### should preserve retry and fallback error identities

- Create terminal retry and fallback errors

<details>
<summary>Executable SSpec</summary>

```simple
it "should preserve retry and fallback error identities":
    step("Create terminal retry and fallback errors")
    val context = RetryContext.new("opus")
    val cannot = CannotRetryError.new("nope", context)
    val fallback = FallbackTriggeredError.new("opus", "sonnet")
    expect(cannot.name).to_equal("RetryError")
    expect(cannot.originalMessage).to_equal("nope")
    expect(fallback.name).to_equal("FallbackTriggeredError")
    expect(fallback.message).to_equal("Model fallback triggered: opus -> sonnet")
```

</details>

#### should compute bounded retry delays without overflow

- Check Retry-After, invalid headers, and saturated exponential delay

<details>
<summary>Executable SSpec</summary>

```simple
it "should compute bounded retry delays without overflow":
    step("Check Retry-After, invalid headers, and saturated exponential delay")
    expect(getRetryDelay(4, "7", 32000, 0)).to_equal(7000)
    expect(getRetryDelay(4, "0", 32000, 0)).to_equal(0)
    expect(getRetryDelay(4, "99", 32000, 0)).to_equal(32000)
    expect(getRetryDelay(3, "-1", 32000, 25)).to_equal(2025)
    expect(getRetryDelay(100, "", 32000, 0)).to_equal(32000)
    expect(getRetryDelay(64, "", 32000, 25)).to_equal(32000)
    expect(getRetryDelay(3, "", 32000, -9223372036854775807)).to_equal(0)
```

</details>

#### should classify fast-mode-not-enabled status and message boundaries

- Compare the matching status and message with each false boundary

<details>
<summary>Executable SSpec</summary>

```simple
it "should classify fast-mode-not-enabled status and message boundaries":
    step("Compare the matching status and message with each false boundary")
    val exact = ApiError.new(400, "Fast mode is not enabled for this organization")
    val contained = ApiError.new(400, "prefix Fast mode is not enabled suffix")
    val wrongStatus = ApiError.new(401, "Fast mode is not enabled for this organization")
    val wrongMessage = ApiError.new(400, "Fast mode is enabled")
    val wrongCase = ApiError.new(400, "fast mode is not enabled")
    val unrelated = ApiError.new(500, "server")
    expect([
        isFastModeNotEnabledError(exact),
        isFastModeNotEnabledError(contained),
        isFastModeNotEnabledError(wrongStatus),
        isFastModeNotEnabledError(wrongMessage),
        isFastModeNotEnabledError(wrongCase),
        isFastModeNotEnabledError(unrelated),
    ]).to_equal([true, true, false, false, false, false])
```

</details>

#### should apply the complete default retry classifier boundaries

- Compare mock, connection, request, rate-limit, authentication, and server errors

<details>
<summary>Executable SSpec</summary>

```simple
it "should apply the complete default retry classifier boundaries":
    step("Compare mock, connection, request, rate-limit, authentication, and server errors")
    val mockRateLimit = ApiError.new(429, "mock rate")
    mockRateLimit.mockRateLimit = true
    expect([
        shouldRetry(mockRateLimit),
        shouldRetry(ApiError.connection("ECONNRESET")),
        shouldRetry(ApiError.new(408, "request timeout")),
        shouldRetry(ApiError.new(409, "conflict")),
        shouldRetry(ApiError.new(429, "rate")),
        shouldRetry(ApiError.new(401, "expired")),
        shouldRetry(ApiError.new(499, "client boundary")),
        shouldRetry(ApiError.new(500, "server boundary")),
    ]).to_equal([false, true, true, true, true, true, false, true])
```

</details>

#### should convert missing and numeric retry-after seconds to milliseconds

- Read missing, zero, and positive Retry-After values through the owner

<details>
<summary>Executable SSpec</summary>

```simple
it "should convert missing and numeric retry-after seconds to milliseconds":
    step("Read missing, zero, and positive Retry-After values through the owner")
    val missing = ApiError.new(429, "missing header")
    val zero = ApiError.new(429, "zero header")
    zero.retryAfter = "0"
    val seven = ApiError.new(429, "numeric header")
    seven.retryAfter = "7"
    expect([
        getRetryAfterMs(missing),
        getRetryAfterMs(zero),
        getRetryAfterMs(seven),
    ]).to_equal([0, 0, 7000])
```

</details>

### Supporting persistent and bounded retry sequences

#### should keep persistent 429 retries beyond max retries

- Run four persistent rate-limit failures with one configured max retry

<details>
<summary>Executable SSpec</summary>

```simple
it "should keep persistent 429 retries beyond max retries":
    step("Run four persistent rate-limit failures with one configured max retry")
    val options = RetryOptions.new("opus")
    options.maxRetries = 1
    options.persistentRetry = true
    val model = WithRetryModel.new(options)
    val result = run_retry_sequence(model, setup_retry_sequence_fixture(429, 4, ""))
    check_retry_sequence(result, 4, 7500, 0, "retry", "")
    expect(model.trace.sleepDelaysMs).to_equal([500, 1000, 2000, 4000])
    expect(model.trace.heartbeatCounts).to_equal([0, 0, 0, 0])
    expect(model.trace.attemptStatuses).to_equal(["retry", "retry", "retry", "retry"])
```

</details>

#### should emit exact heartbeats for persistent 529 retry-after delays

- Run 30-second and 31-second overload delays beyond one configured max retry

<details>
<summary>Executable SSpec</summary>

```simple
it "should emit exact heartbeats for persistent 529 retry-after delays":
    step("Run 30-second and 31-second overload delays beyond one configured max retry")
    val options = RetryOptions.new("opus")
    options.maxRetries = 1
    options.persistentRetry = true
    options.claudeAiSubscriber = true
    val model = WithRetryModel.new(options)
    val errors = setup_retry_sequence_fixture(529, 3, "31")
    errors[0].retryAfter = "30"
    val result = run_retry_sequence(model, errors)
    check_retry_sequence(result, 3, 92000, 5, "retry", "")
    expect(model.trace.sleepDelaysMs).to_equal([30000, 31000, 31000])
    expect(model.trace.heartbeatCounts).to_equal([1, 2, 2])
    expect(model.trace.attemptStatuses).to_equal(["retry", "retry", "retry"])
```

</details>

#### should fail exactly after max retries plus one nonpersistent attempt

- Run three server failures with two configured retries

<details>
<summary>Executable SSpec</summary>

```simple
it "should fail exactly after max retries plus one nonpersistent attempt":
    step("Run three server failures with two configured retries")
    val options = RetryOptions.new("opus")
    options.maxRetries = 2
    val model = WithRetryModel.new(options)
    val result = run_retry_sequence(model, setup_retry_sequence_fixture(500, 3, ""))
    check_retry_sequence(result, 3, 1500, 0, "fail", "retry fixture")
    expect(model.trace.sleepDelaysMs).to_equal([500, 1000])
    expect(model.trace.heartbeatCounts).to_equal([0, 0])
    expect(model.trace.attemptStatuses).to_equal(["retry", "retry", "fail"])
    expect(result.outcomes[2].errorName).to_equal("RetryError")
    expect(result.outcomes[2].delayMs).to_equal(0)
    expect(result.outcomes[2].yieldedHeartbeats).to_equal(0)
```

</details>

### Supporting overflow and thinking-budget parts-bin behavior

#### should adjust max tokens within the available context

- Handle a context overflow with a valid thinking budget

<details>
<summary>Executable SSpec</summary>

```simple
it "should adjust max tokens within the available context":
    step("Handle a context overflow with a valid thinking budget")
    val options = RetryOptions.new("opus")
    val model = WithRetryModel.new(options)
    model.context.thinkingEnabled = true
    model.context.thinkingBudgetTokens = 9000
    val error = ApiError.new(400, "input length and `max_tokens` exceed context limit: 188059 + 20000 > 200000")
    val outcome = model.handleError(error, 1)
    expect(outcome.status).to_equal("retry")
    expect(outcome.context.maxTokensOverride).to_equal(10941)
    expect(outcome.context.thinkingBudgetTokens).to_equal(9000)
    expect(model.logs).to_equal(["tengu_max_tokens_context_overflow_adjustment"])
```

</details>

#### should reject context overflow below the output floor

- Leave no room for the minimum output allocation

<details>
<summary>Executable SSpec</summary>

```simple
it "should reject context overflow below the output floor":
    step("Leave no room for the minimum output allocation")
    val options = RetryOptions.new("opus")
    val model = WithRetryModel.new(options)
    val error = ApiError.new(400, "input length and `max_tokens` exceed context limit: 197000 + 20000 > 200000")
    val outcome = model.handleError(error, 1)
    expect(outcome.status).to_equal("fail")
    expect(outcome.errorName).to_equal("ApiError")
    expect(outcome.errorMessage).to_equal("availableContext below floor")
    expect(outcome.context.maxTokensOverride).to_equal(0)
```

</details>

#### should reject a thinking budget above available context

- Require one output token beyond the thinking budget

<details>
<summary>Executable SSpec</summary>

```simple
it "should reject a thinking budget above available context":
    step("Require one output token beyond the thinking budget")
    val options = RetryOptions.new("opus")
    val model = WithRetryModel.new(options)
    model.context.thinkingEnabled = true
    model.context.thinkingBudgetTokens = 10941
    val error = ApiError.new(400, "input length and `max_tokens` exceed context limit: 188059 + 20000 > 200000")
    val outcome = model.handleError(error, 1)
    expect(outcome.status).to_equal("fail")
    expect(outcome.errorName).to_equal("ApiError")
    expect(outcome.errorMessage).to_equal("thinking budget exceeds availableContext")
    expect(outcome.context.maxTokensOverride).to_equal(0)
    val extremeModel = WithRetryModel.new(RetryOptions.new("opus"))
    extremeModel.context.thinkingEnabled = true
    extremeModel.context.thinkingBudgetTokens = 9223372036854775807
    val extremeOutcome = extremeModel.handleError(error, 1)
    expect(extremeOutcome.status).to_equal("fail")
    expect(extremeOutcome.errorMessage).to_equal("thinking budget exceeds availableContext")
    expect(extremeOutcome.context.maxTokensOverride).to_equal(0)
```

</details>

### Supporting provider recovery effect parts-bin behavior

#### should clear only explicitly selected provider caches

- Exercise Bedrock, Vertex, and generic authentication failures

<details>
<summary>Executable SSpec</summary>

```simple
it "should clear only explicitly selected provider caches":
    step("Exercise Bedrock, Vertex, and generic authentication failures")
    val awsOptions = RetryOptions.new("opus")
    awsOptions.useBedrock = true
    val awsModel = WithRetryModel.new(awsOptions)
    val awsError = ApiError.new(403, "bedrock denied")
    val firstAws = awsModel.handleError(awsError, 1)
    val immediateCachedAws = awsModel.handleError(awsError, 1)
    expect(immediateCachedAws).to_be(firstAws)
    val secondAws = awsModel.handleError(awsError, 2)
    expect(secondAws.status).to_equal("retry")
    val nonconsecutiveCachedAws = awsModel.handleError(awsError, 1)
    expect(nonconsecutiveCachedAws).to_be(firstAws)
    expect(awsModel.trace.cacheClears).to_equal(["aws_credentials", "aws_credentials"])
    expect(awsModel.trace.cooldownDelaysMs).to_equal([])
    expect(awsModel.trace.sleepDelaysMs).to_equal([500, 1000])
    expect(awsModel.trace.heartbeatCounts).to_equal([0, 0])
    expect(awsModel.trace.attemptStatuses).to_equal(["retry", "retry"])
    expect(awsModel.logs).to_equal(["tengu_api_retry", "tengu_api_retry"])
    expect(awsModel.handledAttempts).to_equal([1, 2])
    expect(awsModel.handledOutcomes.len()).to_equal(2)
    val gcpOptions = RetryOptions.new("opus")
    gcpOptions.useVertex = true
    val gcpModel = WithRetryModel.new(gcpOptions)
    expect(gcpModel.handleError(ApiError.new(401, "Could not refresh access token"), 1).status).to_equal("retry")
    expect(gcpModel.trace.cacheClears).to_equal(["gcp_credentials"])
    val genericModel = WithRetryModel.new(RetryOptions.new("opus"))
    expect(genericModel.handleError(ApiError.new(401, "expired"), 1).status).to_equal("retry")
    expect(genericModel.handleError(ApiError.new(403, "denied"), 2).status).to_equal("fail")
    expect(genericModel.trace.cacheClears).to_equal([])
    expect(awsCredentialCacheIdentity()).to_equal("aws_credentials")
    expect(gcpCredentialCacheIdentity()).to_equal("gcp_credentials")
```

</details>

#### should record stale connection cooldown once per attempt

- Run reset and broken-pipe failures while separating cooldown from retry delay

<details>
<summary>Executable SSpec</summary>

```simple
it "should record stale connection cooldown once per attempt":
    step("Run reset and broken-pipe failures while separating cooldown from retry delay")
    val options = RetryOptions.new("opus")
    options.staleConnectionCooldownMs = 1000
    val model = WithRetryModel.new(options)
    val result = run_retry_sequence(model, [ApiError.connection("ECONNRESET"), ApiError.connection("EPIPE")])
    check_retry_sequence(result, 2, 1500, 0, "retry", "")
    expect(model.trace.cooldownDelaysMs).to_equal([1000, 1000])
    expect(model.trace.sleepDelaysMs).to_equal([500, 1000])
    val nonconsecutiveCached = model.handleError(ApiError.connection("ECONNRESET"), 1)
    expect(nonconsecutiveCached).to_be(result.outcomes[0])
    expect(model.trace.cooldownDelaysMs).to_equal([1000, 1000])
    expect(model.trace.cacheClears).to_equal([])
    expect(model.trace.sleepDelaysMs).to_equal([500, 1000])
    expect(model.trace.heartbeatCounts).to_equal([0, 0])
    expect(model.trace.attemptStatuses).to_equal(["retry", "retry"])
    expect(model.logs).to_equal(["tengu_api_retry", "tengu_api_retry"])
    expect(model.handledAttempts).to_equal([1, 2])
    expect(model.handledOutcomes.len()).to_equal(2)
```

</details>

### Supporting fallback, background, and header boundaries

#### should drop background 529 before retry amplification

- Use a nonforeground query source

<details>
<summary>Executable SSpec</summary>

```simple
it "should drop background 529 before retry amplification":
    step("Use a nonforeground query source")
    val options = RetryOptions.new("opus")
    options.querySource = "title"
    val model = WithRetryModel.new(options)
    val outcome = model.handleError(ApiError.new(529, "overloaded"), 1)
    expect(outcome.status).to_equal("fail")
    expect(outcome.errorName).to_equal("RetryError")
    expect(outcome.errorMessage).to_equal("overloaded")
    expect(model.logs).to_equal(["tengu_api_529_background_dropped"])
    expect(model.trace.sleepDelaysMs).to_equal([])
```

</details>

#### should trigger model fallback after the third foreground 529

- Seed two overloads and provide an explicit fallback model

<details>
<summary>Executable SSpec</summary>

```simple
it "should trigger model fallback after the third foreground 529":
    step("Seed two overloads and provide an explicit fallback model")
    val options = RetryOptions.new("opus")
    options.initialConsecutive529Errors = 2
    options.fallbackModel = "sonnet"
    val model = WithRetryModel.new(options)
    val outcome = model.handleError(ApiError.new(529, "overloaded"), 1)
    expect(outcome.status).to_equal("fail")
    expect(outcome.errorName).to_equal("FallbackTriggeredError")
    expect(outcome.errorMessage).to_equal("Model fallback triggered: opus -> sonnet")
    expect(model.trace.attemptStatuses).to_equal(["fail"])
```

</details>

#### should honor retry headers and subscriber boundaries

- Check false, true, subscriber, enterprise, and rate-limit decisions

<details>
<summary>Executable SSpec</summary>

```simple
it "should honor retry headers and subscriber boundaries":
    step("Check false, true, subscriber, enterprise, and rate-limit decisions")
    val blocked = ApiError.new(500, "server")
    blocked.shouldRetryHeader = "false"
    expect(shouldRetryWithOptions(blocked, RetryOptions.new("opus"))).to_equal(false)
    val ant = RetryOptions.new("opus")
    ant.antUser = true
    expect(shouldRetryWithOptions(blocked, ant)).to_equal(true)
    val requested = ApiError.new(400, "request")
    requested.shouldRetryHeader = "true"
    expect(shouldRetryWithOptions(requested, RetryOptions.new("opus"))).to_equal(true)
    val subscriber = RetryOptions.new("opus")
    subscriber.claudeAiSubscriber = true
    expect(shouldRetryWithOptions(requested, subscriber)).to_equal(false)
    subscriber.enterpriseSubscriber = true
    expect(shouldRetryWithOptions(requested, subscriber)).to_equal(true)
    expect(shouldRetryWithOptions(ApiError.new(429, "rate"), subscriber)).to_equal(true)
```

</details>

#### should cap reset delays and expose stable policy constants

- Check reset-window and retry-policy boundaries

<details>
<summary>Executable SSpec</summary>

```simple
it "should cap reset delays and expose stable policy constants":
    step("Check reset-window and retry-policy boundaries")
    val error = ApiError.new(429, "rate")
    error.resetUnixSec = 100
    expect(getRateLimitResetDelayMs(error, 99000)).to_equal(1000)
    error.resetUnixSec = 999999
    expect(getRateLimitResetDelayMs(error, 0)).to_equal(21600000)
    expect(abortError()).to_equal("APIUserAbortError")
    expect(getDefaultMaxRetries("")).to_equal(10)
    expect(floorOutputTokens()).to_equal(3000)
    expect(heartbeatIntervalMs()).to_equal(30000)
    expect(defaultStaleConnectionCooldownMs()).to_equal(1000)
```

</details>

## Execution Status

The executable spec and this mirrored manual were updated statically. No
runtime was invoked, 0 scenarios were executed, and no PASS is claimed.
