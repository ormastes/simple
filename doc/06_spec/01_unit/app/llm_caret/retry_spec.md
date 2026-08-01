# Retry Specification

> <details>

<!-- sdn-diagram:id=retry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=retry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

retry_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=retry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Retry Specification

## Scenarios

### default_retry_policy

#### has sane production defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = default_retry_policy()
expect(p.max_attempts).to_equal(4)
expect(p.base_delay_ms).to_equal(1000)
expect(p.max_delay_ms).to_equal(32000)
expect(p.timeout_ms).to_equal(600000)
```

</details>

### is_retryable_status

#### retries 429

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_retryable_status(429)).to_equal(true)
```

</details>

#### retries 500

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_retryable_status(500)).to_equal(true)
```

</details>

#### retries 502 and 503

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_retryable_status(502)).to_equal(true)
expect(is_retryable_status(503)).to_equal(true)
```

</details>

#### retries connection error (status <= 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_retryable_status(-1)).to_equal(true)
expect(is_retryable_status(0)).to_equal(true)
```

</details>

#### does not retry 400

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_retryable_status(400)).to_equal(false)
```

</details>

#### does not retry 401 or 403

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_retryable_status(401)).to_equal(false)
expect(is_retryable_status(403)).to_equal(false)
```

</details>

#### does not retry 404

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_retryable_status(404)).to_equal(false)
```

</details>

#### does not retry 200

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_retryable_status(200)).to_equal(false)
```

</details>

### should_retry

#### retries 429 within max_attempts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _test_policy()
expect(should_retry(429, 1, p)).to_equal(true)
```

</details>

#### retries 500 within max_attempts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _test_policy()
expect(should_retry(500, 1, p)).to_equal(true)
```

</details>

#### does not retry 400

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _test_policy()
expect(should_retry(400, 1, p)).to_equal(false)
```

</details>

#### does not retry once max_attempts is reached

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _test_policy()
expect(should_retry(500, 4, p)).to_equal(false)
```

</details>

#### does not retry beyond max_attempts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _test_policy()
expect(should_retry(500, 10, p)).to_equal(false)
```

</details>

### backoff_delay_ms

#### produces increasing delays for successive attempts

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _test_policy()
val d1 = backoff_delay_ms(1, p)
val d2 = backoff_delay_ms(2, p)
val d3 = backoff_delay_ms(3, p)
expect(d1).to_be_greater_than(0)
expect(d2).to_be_greater_than(d1)
expect(d3).to_be_greater_than(d2)
```

</details>

#### attempt 1 is close to base_delay_ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _test_policy()
val d1 = backoff_delay_ms(1, p)
expect(d1).to_be_greater_than(999)
expect(d1).to_be_less_than(1300)
```

</details>

#### attempt 2 is roughly double base_delay_ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _test_policy()
val d2 = backoff_delay_ms(2, p)
expect(d2).to_be_greater_than(1999)
expect(d2).to_be_less_than(2300)
```

</details>

#### caps at max_delay_ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _test_policy()
val d_big = backoff_delay_ms(20, p)
expect(d_big).to_be_less_than(p.max_delay_ms + 300)
```

</details>

#### is deterministic for the same inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _test_policy()
val a = backoff_delay_ms(3, p)
val b = backoff_delay_ms(3, p)
expect(a).to_equal(b)
```

</details>

### effective_delay_ms

#### honors Retry-After when positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _test_policy()
val delay = effective_delay_ms(1, p, 5000)
expect(delay).to_equal(5000)
```

</details>

#### falls back to backoff when Retry-After is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _test_policy()
val delay = effective_delay_ms(1, p, 0)
val expected = backoff_delay_ms(1, p)
expect(delay).to_equal(expected)
```

</details>

#### caps Retry-After at max_delay_ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _test_policy()
val delay = effective_delay_ms(1, p, 999999)
expect(delay).to_equal(p.max_delay_ms)
```

</details>

### with_retry

#### does not retry on immediate success

-
   - Expected: outcome.status equals `200`
   - Expected: outcome.attempts equals `1`
   - Expected: outcome.error equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _fast_policy()
val outcome = with_retry(p, fn(attempt: i64) -> (i64, text, text, i64):
    (200, "ok", "", 0)
)
expect(outcome.status).to_equal(200)
expect(outcome.attempts).to_equal(1)
expect(outcome.error).to_equal("")
```

</details>

#### retries on 429 then succeeds

-
-
   - Expected: outcome.status equals `200`
   - Expected: outcome.attempts equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _fast_policy()
val outcome = with_retry(p, fn(attempt: i64) -> (i64, text, text, i64):
    if attempt < 2:
        (429, "", "", 0)
    else:
        (200, "ok", "", 0)
)
expect(outcome.status).to_equal(200)
expect(outcome.attempts).to_equal(2)
```

</details>

#### retries on 500 then succeeds

-
-
   - Expected: outcome.status equals `200`
   - Expected: outcome.attempts equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _fast_policy()
val outcome = with_retry(p, fn(attempt: i64) -> (i64, text, text, i64):
    if attempt < 3:
        (500, "", "", 0)
    else:
        (200, "ok", "", 0)
)
expect(outcome.status).to_equal(200)
expect(outcome.attempts).to_equal(3)
```

</details>

#### does not retry 400 (fails on first attempt)

-
   - Expected: outcome.status equals `400`
   - Expected: outcome.attempts equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _fast_policy()
val outcome = with_retry(p, fn(attempt: i64) -> (i64, text, text, i64):
    (400, "bad request", "", 0)
)
expect(outcome.status).to_equal(400)
expect(outcome.attempts).to_equal(1)
```

</details>

#### exhausts max_attempts and returns the final error

-
   - Expected: outcome.attempts equals `p.max_attempts`
   - Expected: outcome.status equals `503`
   - Expected: outcome.body equals `still down`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _fast_policy()
val outcome = with_retry(p, fn(attempt: i64) -> (i64, text, text, i64):
    (503, "still down", "", 0)
)
expect(outcome.attempts).to_equal(p.max_attempts)
expect(outcome.status).to_equal(503)
expect(outcome.body).to_equal("still down")
```

</details>

#### retries on connection error (non-empty error string)

-
-
   - Expected: outcome.status equals `200`
   - Expected: outcome.attempts equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _fast_policy()
val outcome = with_retry(p, fn(attempt: i64) -> (i64, text, text, i64):
    if attempt < 2:
        (0, "", "connection refused", 0)
    else:
        (200, "ok", "", 0)
)
expect(outcome.status).to_equal(200)
expect(outcome.attempts).to_equal(2)
```

</details>

#### honors Retry-After hint on a retried attempt

-
-
   - Expected: outcome.status equals `200`
   - Expected: outcome.attempts equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _fast_policy()
val outcome = with_retry(p, fn(attempt: i64) -> (i64, text, text, i64):
    if attempt < 2:
        (429, "", "", 10)
    else:
        (200, "ok", "", 0)
)
expect(outcome.status).to_equal(200)
expect(outcome.attempts).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/retry_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- default_retry_policy
- is_retryable_status
- should_retry
- backoff_delay_ms
- effective_delay_ms
- with_retry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
