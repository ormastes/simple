# Browser Fetch CORS Unsafe-Header Preflight

> Proves a non-safelisted cross-origin request header is authorized through the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Fetch CORS Unsafe-Header Preflight

Proves a non-safelisted cross-origin request header is authorized through the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Status | Active |
| Source | `test/03_system/security/browser_fetch_cors_unsafe_header_preflight_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves a non-safelisted cross-origin request header is authorized through the
real OPTIONS path before any actual request can reach the endpoint.

## Scenarios

### Browser Fetch CORS unsafe-header preflight

#### should deny an ungranted custom header before the actual request

- should deny an ungranted custom header before the actual request
   - Protocol capture: after_step
- Register a cross-origin endpoint that omits X-Admin-Action permission
   - Protocol capture: after_step
- Issue a credential-free CORS GET carrying X-Admin-Action
   - Protocol capture: after_step
- Observe the first and only OPTIONS advertising x-admin-action
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: observed.method equals `OPTIONS`
- Reject the fetch before the ungranted action reaches the endpoint
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should deny an ungranted custom header before the actual request")
step("Register a cross-origin endpoint that omits X-Admin-Action permission")
var registry = MockResponseRegistry.create()
registry.register_with_headers(
    "https://api.test/admin",
    204,
    [Pair(
        "Access-Control-Allow-Origin", "https://app.test"
    )],
    ""
)
set_mock_registry(registry)

step("Issue a credential-free CORS GET carrying X-Admin-Action")
var fetch = FetchEngine.new_for_origin(
    Logger.new("cors-header-preflight", BrowserLogLevel.Error),
    "https://app.test"
)
val result = fetch.fetch(FetchRequest(
    url: Url.parse_or_opaque("https://api.test/admin"),
    method: "GET",
    headers: "X-Admin-Action: delete\r\n",
    body: [],
    mode: RequestMode.Cors,
    credentials: "omit"
))

step("Observe the first and only OPTIONS advertising x-admin-action")
match observed_mock_request("https://api.test/admin"):
    Some(observed):
        expect(observed.method).to_equal("OPTIONS")
        expect(observed.headers).to_contain(
            "Access-Control-Request-Headers: x-admin-action"
        )
    nil:
        fail("missing CORS preflight request")
expect(observed_mock_request_count(
    "https://api.test/admin"
)).to_equal(1)
expect(observed_mock_request_count(
    "https://api.test/admin", "GET"
)).to_equal(0)

step("Reject the fetch before the ungranted action reaches the endpoint")
match result:
    Err(error):
        expect(error.message).to_contain("CORS preflight denied")
    Ok(_):
        fail("ungranted custom-header request reached the endpoint")
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

- Canonical SPipe generation for source `689bf7b8e718930ff2aab5270a4bf4ba11b0dd71b6b49109a95336d2dc8a6f4d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `689bf7b8e718930ff2aab5270a4bf4ba11b0dd71b6b49109a95336d2dc8a6f4d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `689bf7b8e718930ff2aab5270a4bf4ba11b0dd71b6b49109a95336d2dc8a6f4d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/security/browser_fetch_cors_unsafe_header_preflight_spec.spl
mirror: doc/06_spec/03_system/security/browser_fetch_cors_unsafe_header_preflight_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=95 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/03_system/security/browser_fetch_cors_unsafe_header_preflight_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/security/browser_fetch_cors_unsafe_header_preflight_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/security/browser_fetch_cors_unsafe_header_preflight_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/security/browser_fetch_cors_unsafe_header_preflight_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should deny an ungranted custom header before the actual request' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/security/browser_fetch_cors_unsafe_header_preflight_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should deny an ungranted custom header before the actual request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
