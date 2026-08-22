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
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# Browser Fetch Aggregate Redirect Deadline

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

- Verify: should stop a mixed-scheme redirect chain at one absolute deadline
- Register three local hops whose aggregate latency exceeds five seconds
- Fetch with one absolute deadline shared by every redirect
   - Expected: error.source equals `network`
- Reject the late response without committing cache state
   - Expected: get_mock_registry().observed_requests.len() equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: get_mock_registry().now_ms equals `6000)  # oracle: pinned constant asserted by this scenario  # oracle: pinned ... (full value in folded executable source)`
   - Expected: fetch.cache.entries.len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: should stop a mixed-scheme redirect chain at one absolute deadline")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
expect(get_mock_registry().observed_requests.len()).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(get_mock_registry().now_ms).to_equal(6000)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(fetch.cache.entries.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### should complete a mixed-scheme redirect chain within the same budget

- Verify: should complete a mixed-scheme redirect chain within the same budget
- Register a local HTTP to HTTPS chain within five seconds
- Complete all hops before the absolute deadline
   - Expected: response.status equals `200)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: response.body_text() equals `done`
   - Expected: get_mock_registry().observed_requests.len() equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: get_mock_registry().now_ms equals `5500)  # oracle: pinned constant asserted by this scenario  # oracle: pinned ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: should complete a mixed-scheme redirect chain within the same budget")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
        expect(response.status).to_equal(200)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
        expect(response.body_text()).to_equal("done")
expect(get_mock_registry().observed_requests.len()).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(get_mock_registry().now_ms).to_equal(5500)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

<details>
<summary>Advanced: should retain the twenty-redirect ceiling inside the deadline</summary>

#### should retain the twenty-redirect ceiling inside the deadline

- Verify: should retain the twenty-redirect ceiling inside the deadline
- Register a zero-latency local redirect loop
- Stop after twenty redirects without refreshing the deadline
   - Expected: get_mock_registry().observed_requests.len() equals `21)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`
   - Expected: get_mock_registry().now_ms equals `1000)  # oracle: pinned constant asserted by this scenario  # oracle: pinned ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-017
step("Verify: should retain the twenty-redirect ceiling inside the deadline")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
expect(get_mock_registry().observed_requests.len()).to_equal(21)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(get_mock_registry().now_ms).to_equal(1000)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bca99a576ea2cab30675bdb26710b9b1de848aa427bb0708dae57304c31a0130`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bca99a576ea2cab30675bdb26710b9b1de848aa427bb0708dae57304c31a0130`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bca99a576ea2cab30675bdb26710b9b1de848aa427bb0708dae57304c31a0130`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/fetch_deadline_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/fetch_deadline_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/fetch_deadline_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/fetch_deadline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/fetch_deadline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/fetch_deadline_spec.spl:65:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should stop a mixed-scheme redirect chain at one absolute deadline' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/fetch_deadline_spec.spl:105:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should complete a mixed-scheme redirect chain within the same budget' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/fetch_deadline_spec.spl:139:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain the twenty-redirect ceiling inside the deadline' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
