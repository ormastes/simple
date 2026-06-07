# rate_limit_spec

> Tests for rate limiting configuration, defaults, and peer tracking. Validates that request limits and time windows are correct.

<!-- sdn-diagram:id=rate_limit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rate_limit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rate_limit_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rate_limit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rate_limit_spec

Tests for rate limiting configuration, defaults, and peer tracking. Validates that request limits and time windows are correct.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SEC-012 |
| Category | HTTP Server Security |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/http_server/rate_limit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for rate limiting configuration, defaults, and peer tracking.
Validates that request limits and time windows are correct.

## Scenarios

### RateLimitConfig defaults

#### defaults to 100 requests

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_rate_limit_config()
expect(config.max_requests).to_equal(100)
```

</details>

#### defaults to 60000ms window

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_rate_limit_config()
expect(config.window_ms).to_equal(60000)
```

</details>

#### has enabled set to true by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_rate_limit_config()
expect(config.enabled).to_equal(true)
```

</details>

### Rate limit checking

#### allows requests within limit

1. var store = new rate limit store
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_rate_limit_config()
var store = new_rate_limit_store()
val result = check_rate_limit(store, config, "192.168.1.1")
expect(result).to_equal(true)
```

</details>

#### tracks peer request count

1. var store = new rate limit store
   - Expected: first is true
   - Expected: second is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_rate_limit_config()
var store = new_rate_limit_store()
val first = check_rate_limit(store, config, "10.0.0.1")
val second = check_rate_limit(store, config, "10.0.0.1")
expect(first).to_equal(true)
expect(second).to_equal(true)
```

</details>

#### tracks different peers independently

1. var store = new rate limit store
   - Expected: result_a is true
   - Expected: result_b is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_rate_limit_config()
var store = new_rate_limit_store()
val result_a = check_rate_limit(store, config, "10.0.0.1")
val result_b = check_rate_limit(store, config, "10.0.0.2")
expect(result_a).to_equal(true)
expect(result_b).to_equal(true)
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
