# Hosted Browser CORS Preflight

> Proves the sandbox broker runs a public-only OPTIONS job before an unsafe

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Browser CORS Preflight

Proves the sandbox broker runs a public-only OPTIONS job before an unsafe

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Status | Active |
| Source | `test/03_system/security/browser_hosted_cors_preflight_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the sandbox broker runs a public-only OPTIONS job before an unsafe
cross-origin request and never publishes preflight authority or side effects.

## Scenarios

### Hosted browser CORS preflight

#### should publish only an actual request admitted by OPTIONS

- should publish only an actual request admitted by OPTIONS
   - Protocol capture: after_step
- Admit the hosted unsafe request
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: policy.mode equals `RequestMode.Cors`
- Run OPTIONS before the actual request
   - Protocol capture: after_step
   - Evidence: protocol response verified by 3 expected checks
   - Expected: observed_mock_request_count(url, "OPTIONS") equals `1`
   - Expected: observed_mock_request_count(url, "POST") equals `1`
   - Expected: preflight.method equals `OPTIONS`
- Cancel denied preflight work without side effects
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: response.status equals `0`
   - Expected: denied.network_job_phase equals ``
- Publish only the validated actual response
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: decoded.status equals `message`
   - Expected: response.status equals `204`


<details>
<summary>Executable SSpec</summary>

Runnable source: 109 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should publish only an actual request admitted by OPTIONS")
step("Admit the hosted unsafe request")
val url = "https://api.test/update"
val fetch = hosted_cors_request(url)
val policy = hosted_browser_renderer_request_policy(
    "https://app.test", empty_navigation_permit(), fetch
)
expect(policy.ok).to_be(true)
expect(policy.mode).to_equal(RequestMode.Cors)
expect(policy.sanitized_headers.contains("Origin:")).to_be(false)

step("Run OPTIONS before the actual request")
var registry = MockResponseRegistry.create()
registry.register_with_headers(
    url, 204,
    [
        Pair("Access-Control-Allow-Origin", "https://app.test"),
        Pair("Access-Control-Allow-Methods", "POST"),
        Pair(
            "Access-Control-Allow-Headers",
            "content-type, x-admin-action"
        ),
        Pair("Set-Cookie", "preflight=blocked"),
        Pair("Strict-Transport-Security", "max-age=600")
    ],
    ""
)
set_mock_registry(registry)
var broker = HostedBrowserRendererProcess.create(7, 64, 48)
broker.document_url = "https://app.test/page"
broker.document_origin = "https://app.test"
broker.active_command_capability = (
    "11111111111111111111111111111111"
)
broker.active_root_command_request_id = 1
match broker._start_network_job(fetch, policy, 0):
    nil:
        fail("mock CORS exchange did not complete")
    Some(response):
        expect(broker._write_network_response(
            fetch, policy, response, 0
        )).to_equal("")
expect(observed_mock_request_count(url, "OPTIONS")).to_equal(1)
expect(observed_mock_request_count(url, "POST")).to_equal(1)
match observed_mock_request(url):
    nil:
        fail("missing OPTIONS request")
    Some(preflight):
        expect(preflight.method).to_equal("OPTIONS")
        expect(preflight.headers).to_contain(
            "Access-Control-Request-Headers: content-type, x-admin-action"
        )

step("Cancel denied preflight work without side effects")
var denied_registry = MockResponseRegistry.create()
denied_registry.register_with_headers(
    "https://api.test/denied", 302,
    [
        Pair("Location", "https://api.test/elsewhere"),
        Pair("Set-Cookie", "denied=blocked"),
        Pair("Strict-Transport-Security", "max-age=600")
    ],
    ""
)
set_mock_registry(denied_registry)
val denied_fetch = hosted_cors_request(
    "https://api.test/denied"
)
val denied_policy = hosted_browser_renderer_request_policy(
    "https://app.test", empty_navigation_permit(), denied_fetch
)
var denied = HostedBrowserRendererProcess.create(8, 64, 48)
denied.document_url = "https://app.test/page"
denied.document_origin = "https://app.test"
match denied._start_network_job(denied_fetch, denied_policy, 0):
    nil:
        fail("redirected preflight left a job active")
    Some(response):
        expect(response.status).to_equal(0)
        expect(response.error).to_equal(
            "network: CORS preflight denied"
        )
expect(observed_mock_request_count(
    "https://api.test/denied", "POST"
)).to_equal(0)
denied.network_job_phase = "preflight"
expect(denied._cancel_pending_for_stop()).to_be(true)
expect(denied.network_job_phase).to_equal("")
expect(denied.network_job_actual_request).to_be_nil()
expect(denied.hsts_dirty).to_be(false)

step("Publish only the validated actual response")
val decoded = browser_renderer_capability_decoder_feed(
    browser_renderer_capability_decoder_new(7),
    broker.pending_wire
)
expect(decoded.status).to_equal("message")
val response = browser_renderer_network_response_decode(
    browser_renderer_capability_payload_message(decoded.message)
)
expect(response.ok).to_be(true)
expect(response.status).to_equal(204)
expect(response.headers.contains("Set-Cookie")).to_be(false)
expect(response.headers.contains(
    "Strict-Transport-Security"
)).to_be(false)
expect(broker.hsts_dirty).to_be(false)
set_mock_registry(MockResponseRegistry.create())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-010`
- `REQ-WEB-BROWSER-012`
- `REQ-WEB-BROWSER-021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dc1b22a685c5e665ff14c3ad068582a6cc170b8f938b0d6c23fde9ebd4111aef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc1b22a685c5e665ff14c3ad068582a6cc170b8f938b0d6c23fde9ebd4111aef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc1b22a685c5e665ff14c3ad068582a6cc170b8f938b0d6c23fde9ebd4111aef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/security/browser_hosted_cors_preflight_spec.spl
mirror: doc/06_spec/03_system/security/browser_hosted_cors_preflight_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=95 oracle=70
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/security/browser_hosted_cors_preflight_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/security/browser_hosted_cors_preflight_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/security/browser_hosted_cors_preflight_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/security/browser_hosted_cors_preflight_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/security/browser_hosted_cors_preflight_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should publish only an actual request admitted by OPTIONS' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/security/browser_hosted_cors_preflight_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should publish only an actual request admitted by OPTIONS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
