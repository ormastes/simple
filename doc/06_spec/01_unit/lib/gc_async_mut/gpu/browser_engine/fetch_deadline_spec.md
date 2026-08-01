# Browser Fetch Aggregate Redirect Deadline

> The browser owns one absolute five-second Fetch budget across redirects after DNS resolution returns. Deterministic mock latency covers mixed HTTP/HTTPS hops without sleeping or depending on external hosts. Blocking DNS remains outside this claim because its runtime facade has no remaining-deadline input.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Fetch Aggregate Redirect Deadline

The browser owns one absolute five-second Fetch budget across redirects after DNS resolution returns. Deterministic mock latency covers mixed HTTP/HTTPS hops without sleeping or depending on external hosts. Blocking DNS remains outside this claim because its runtime facade has no remaining-deadline input.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md |
| Design | doc/05_design/simple_web_browser_engine_production_hardening.md |
| Research | N/A |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/fetch_deadline_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The browser owns one absolute five-second Fetch budget across redirects after
DNS resolution returns. Deterministic mock latency covers mixed HTTP/HTTPS
hops without sleeping or depending on external hosts. Blocking DNS remains
outside this claim because its runtime facade has no remaining-deadline input.

**Requirements:** doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md
**Plan:** doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md
**Design:** doc/05_design/simple_web_browser_engine_production_hardening.md
**Research:** N/A

## Examples

An HTTP redirect may upgrade to HTTPS, but every hop receives the same absolute
deadline. A chain totaling less than five seconds succeeds; a later hop that
would cross the deadline fails before its response is committed.

## Scenarios

### Browser Fetch aggregate redirect deadline

#### should stop a mixed-scheme redirect chain at one absolute deadline

- Register three local hops whose aggregate latency exceeds five seconds
- var registry = MockResponseRegistry create at
- [Pair
- [Pair
- [Pair
- set mock registry
- Logger new
- Fetch with one absolute deadline shared by every redirect
- Ok
- fail
- Err
   - Expected: error.source equals `network`
- Reject the late response without committing cache state
   - Expected: get_mock_registry().observed_requests.len() equals `3`
   - Expected: get_mock_registry().now_ms equals `6000`
   - Expected: fetch.cache.entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Register three local hops whose aggregate latency exceeds five seconds")
var registry = MockResponseRegistry.create_at(1000)
registry.register_slow(
    "http://slow.test/start", 302,
    [Pair("Location", "https://slow.test/second")], "", 2000
)
registry.register_slow(
    "https://slow.test/second", 302,
    [Pair("Location", "https://slow.test/final")], "", 2000
)
registry.register_slow(
    "https://slow.test/final", 200,
    [Pair("Cache-Control", "max-age=60")], "late", 2000
)
set_mock_registry(registry)
var fetch = FetchEngine.new_for_origin(
    Logger.new("fetch-deadline", BrowserLogLevel.Error),
    "http://slow.test"
)

step("Fetch with one absolute deadline shared by every redirect")
match fetch.fetch(_deadline_request("http://slow.test/start")):
    Ok(_):
        fail("slow redirect chain escaped the aggregate deadline")
    Err(error):
        expect(error.source).to_equal("network")
        expect(error.message).to_equal(
            "h1: aggregate request deadline exceeded"
        )

step("Reject the late response without committing cache state")
expect(get_mock_registry().observed_requests.len()).to_equal(3)
expect(get_mock_registry().now_ms).to_equal(6000)
expect(fetch.cache.entries.len()).to_equal(0)
```

</details>

#### should complete a mixed-scheme redirect chain within the same budget

- Register a local HTTP to HTTPS chain within five seconds
- var registry = MockResponseRegistry create at
- [Pair
- [Pair
- set mock registry
- Logger new
- Complete all hops before the absolute deadline
- Err
- fail
- Ok
   - Expected: response.status equals `200`
   - Expected: response.body_text() equals `done`
   - Expected: get_mock_registry().observed_requests.len() equals `3`
   - Expected: get_mock_registry().now_ms equals `5500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Register a local HTTP to HTTPS chain within five seconds")
var registry = MockResponseRegistry.create_at(1000)
registry.register_slow(
    "http://fast.test/start", 302,
    [Pair("Location", "https://fast.test/second")], "", 1500
)
registry.register_slow(
    "https://fast.test/second", 302,
    [Pair("Location", "https://fast.test/final")], "", 1500
)
registry.register_slow(
    "https://fast.test/final", 200, [], "done", 1500
)
set_mock_registry(registry)
var fetch = FetchEngine.new_for_origin(
    Logger.new("fetch-deadline", BrowserLogLevel.Error),
    "http://fast.test"
)

step("Complete all hops before the absolute deadline")
match fetch.fetch(_deadline_request("http://fast.test/start")):
    Err(error):
        fail(error.message)
    Ok(response):
        expect(response.status).to_equal(200)
        expect(response.body_text()).to_equal("done")
expect(get_mock_registry().observed_requests.len()).to_equal(3)
expect(get_mock_registry().now_ms).to_equal(5500)
```

</details>

<details>
<summary>Advanced: should retain the twenty-redirect ceiling inside the deadline</summary>

#### should retain the twenty-redirect ceiling inside the deadline

- Register a zero-latency local redirect loop
- var registry = MockResponseRegistry create at
- [Pair
- set mock registry
- Logger new
- Stop after twenty redirects without refreshing the deadline
- Ok
- fail
- Err
- "Too many redirects
   - Expected: get_mock_registry().observed_requests.len() equals `21`
   - Expected: get_mock_registry().now_ms equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Register a zero-latency local redirect loop")
var registry = MockResponseRegistry.create_at(1000)
registry.register_slow(
    "https://loop.test/again", 302,
    [Pair("Location", "/again")], "", 0
)
set_mock_registry(registry)
var fetch = FetchEngine.new_for_origin(
    Logger.new("fetch-deadline", BrowserLogLevel.Error),
    "https://loop.test"
)

step("Stop after twenty redirects without refreshing the deadline")
match fetch.fetch(_deadline_request("https://loop.test/again")):
    Ok(_):
        fail("redirect loop escaped the twenty-hop ceiling")
    Err(error):
        expect(error.message).to_equal(
            "Too many redirects (max: 20)"
        )
expect(get_mock_registry().observed_requests.len()).to_equal(21)
expect(get_mock_registry().now_ms).to_equal(1000)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md`
- **Design:** `doc/05_design/simple_web_browser_engine_production_hardening.md`


</details>
