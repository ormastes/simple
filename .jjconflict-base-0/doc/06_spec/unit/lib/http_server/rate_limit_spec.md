# rate_limit_spec

> Purpose: Prove that RateLimitConfig defaults.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rate_limit_spec

Purpose: Prove that RateLimitConfig defaults.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/http_server/rate_limit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that RateLimitConfig defaults.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### RateLimitConfig defaults

#### defaults to 100 requests per window

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults to 100 requests per window
- Verify: defaults to 100 requests per window
   - Expected: config.requests_per_window equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to 100 requests per window")
step("Verify: defaults to 100 requests per window")
# @req: REQ-LIB-HTTP-SERVER-001
val config = RateLimitConfig.default()
expect(config.requests_per_window).to_equal(100)  # oracle: 100 — named expected value from the requirement
```

</details>

#### defaults to 60000ms window

- defaults to 60000ms window
- Verify: defaults to 60000ms window
   - Expected: config.window_ms equals `60000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to 60000ms window")
step("Verify: defaults to 60000ms window")
val config = RateLimitConfig.default()
expect(config.window_ms).to_equal(60000)  # oracle: 60000 — named expected value from the requirement
```

</details>

#### applies to every request by default

- applies to every request by default
- Verify: applies to every request by default
   - Expected: config.exempt_paths.len() equals `0`
   - Expected: config.trusted_proxies.len() equals `0`
   - Expected: admit(store, config, "203.0.113.9") equals `0`
   - Expected: store.find_peer("203.0.113.9") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies to every request by default")
step("Verify: applies to every request by default")
val config = RateLimitConfig.default()
expect(config.exempt_paths.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(config.trusted_proxies.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
var store = RateLimitStore.new()
expect(admit(store, config, "203.0.113.9")).to_equal(0)
expect(store.find_peer("203.0.113.9")).to_equal(0)
```

</details>

### Rate limit checking

#### allows requests within limit

- allows requests within limit
- Verify: allows requests within limit
   - Expected: admit(store, config, "192.168.1.1") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows requests within limit")
step("Verify: allows requests within limit")
val config = RateLimitConfig.default()
var store = RateLimitStore.new()
expect(admit(store, config, "192.168.1.1")).to_equal(0)
```

</details>

#### tracks peer request count

- tracks peer request count
- Verify: tracks peer request count
   - Expected: admit(store, config, "10.0.0.1") equals `0`
   - Expected: admit(store, config, "10.0.0.1") equals `0`
   - Expected: after_first equals `config.requests_per_window + config.burst_size - 1`
   - Expected: after_second equals `after_first - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks peer request count")
step("Verify: tracks peer request count")
val config = RateLimitConfig.default()
var store = RateLimitStore.new()
expect(admit(store, config, "10.0.0.1")).to_equal(0)
val after_first = store.tokens[store.find_peer("10.0.0.1")]
expect(admit(store, config, "10.0.0.1")).to_equal(0)
val after_second = store.tokens[store.find_peer("10.0.0.1")]
expect(after_first).to_equal(config.requests_per_window + config.burst_size - 1)
expect(after_second).to_equal(after_first - 1)
```

</details>

#### tracks different peers independently

- tracks different peers independently
- Verify: tracks different peers independently
   - Expected: admit(store, config, "10.0.0.1") equals `0`
   - Expected: admit(store, config, "10.0.0.1") equals `0`
   - Expected: admit(store, config, "10.0.0.2") equals `0`
   - Expected: store.peers.len() equals `2`
   - Expected: b equals `a + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks different peers independently")
step("Verify: tracks different peers independently")
val config = RateLimitConfig.default()
var store = RateLimitStore.new()
expect(admit(store, config, "10.0.0.1")).to_equal(0)
expect(admit(store, config, "10.0.0.1")).to_equal(0)
expect(admit(store, config, "10.0.0.2")).to_equal(0)
expect(store.peers.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
val a = store.tokens[store.find_peer("10.0.0.1")]
val b = store.tokens[store.find_peer("10.0.0.2")]
expect(b).to_equal(a + 1)
```

</details>

### Rate limit enforcement

#### rejects with 429 once the bucket is exhausted

- rejects with 429 once the bucket is exhausted
- Verify: rejects with 429 once the bucket is exhausted
   - Expected: admit(store, config, "198.51.100.7") equals `0`
   - Expected: admit(store, config, "198.51.100.7") equals `0`
   - Expected: admit(store, config, "198.51.100.7") equals `429`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects with 429 once the bucket is exhausted")
step("Verify: rejects with 429 once the bucket is exhausted")
val config = RateLimitConfig(
    requests_per_window: 2,
    window_ms: 60000,
    burst_size: 0,
    exempt_paths: [],
    trusted_proxies: []
)
var store = RateLimitStore.new()
expect(admit(store, config, "198.51.100.7")).to_equal(0)
expect(admit(store, config, "198.51.100.7")).to_equal(0)
expect(admit(store, config, "198.51.100.7")).to_equal(429)
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

- `REQ-SSPEC-UNIT`
- `REQ-LIB-HTTP-SERVER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2de48873f15dd7916480e2a9e4342e51e4fe3c02e04b6fa9c8941728d6c5d959`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2de48873f15dd7916480e2a9e4342e51e4fe3c02e04b6fa9c8941728d6c5d959`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2de48873f15dd7916480e2a9e4342e51e4fe3c02e04b6fa9c8941728d6c5d959`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/http_server/rate_limit_spec.spl
mirror: doc/06_spec/unit/lib/http_server/rate_limit_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/http_server/rate_limit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/http_server/rate_limit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/http_server/rate_limit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/http_server/rate_limit_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults to 100 requests per window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/http_server/rate_limit_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults to 60000ms window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/http_server/rate_limit_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies to every request by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
