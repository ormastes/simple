# Cookie Name Token Authority

> Verifies the browser cookie name token behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cookie Name Token Authority

Verifies the browser cookie name token behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_cookie_name_token_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser cookie name token behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### cookie name token authority

#### should reject one malformed name at both cookie producer boundaries

- Verify: should reject one malformed name at both cookie producer boundaries
- Open the authenticated HTTPS cookie fixture
   - Expected: origin.to_text() equals `https://secure.example.test`
- Receive valid and malformed protected cookies
   - Expected: valid_verdict.reason equals `ok`
   - Expected: network_verdict.reason equals `invalid-name`
   - Expected: cookies.count() equals `1)  # oracle: pinned constant asserted by this scenario`
- Attempt the same malformed cookie from script
   - Expected: script_verdict.reason equals `invalid-name`
   - Expected: cookies.count() equals `1)  # oracle: pinned constant asserted by this scenario`
- Observe authoritative script and network cookie state
   - Expected: cookies.script_cookie_header(origin, "/", now) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-011 REQ-WEB-BROWSER-013 REQ-WEB-BROWSER-021
step("Verify: should reject one malformed name at both cookie producer boundaries")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Open the authenticated HTTPS cookie fixture")
var cookies = CookieStore.new()
val origin = Origin(
    scheme: "https", host: "secure.example.test", port: 443
)
val now = 1000
expect(origin.to_text()).to_equal("https://secure.example.test")

step("Receive valid and malformed protected cookies")
val valid = parse_set_cookie(
    "sid=control; Path=/; Secure; HttpOnly; SameSite=None"
)
val malformed = parse_set_cookie(
    "bad name=poison; Path=/; Secure; SameSite=None"
)
val valid_verdict = cookies.store_from_origin(valid, origin, now)
val network_verdict = cookies.store_from_origin(
    malformed, origin, now
)
expect(valid_verdict.accepted).to_be(true)
expect(valid_verdict.reason).to_equal("ok")
expect(network_verdict.accepted).to_be(false)
expect(network_verdict.reason).to_equal("invalid-name")
expect(cookies.count()).to_equal(1)  # oracle: pinned constant asserted by this scenario

step("Attempt the same malformed cookie from script")
val script_verdict = cookies.store_from_script(
    malformed, origin, now
)
expect(script_verdict.accepted).to_be(false)
expect(script_verdict.reason).to_equal("invalid-name")
expect(cookies.count()).to_equal(1)  # oracle: pinned constant asserted by this scenario

step("Observe authoritative script and network cookie state")
expect(cookies.script_cookie_header(origin, "/", now)).to_equal("")
expect(cookies.get_header_for_origin(
    origin, "/", Some(origin), "GET", true, now
)).to_equal("sid=control")
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bcf1a7134a98f5bbe846ff7ac174a42248ece3b16f87ddd254ab5194859c3faf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bcf1a7134a98f5bbe846ff7ac174a42248ece3b16f87ddd254ab5194859c3faf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bcf1a7134a98f5bbe846ff7ac174a42248ece3b16f87ddd254ab5194859c3faf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_cookie_name_token_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_cookie_name_token_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_cookie_name_token_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_cookie_name_token_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_cookie_name_token_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_cookie_name_token_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject one malformed name at both cookie producer boundaries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
