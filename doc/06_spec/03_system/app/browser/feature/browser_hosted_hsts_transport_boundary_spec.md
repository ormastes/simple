# Hosted HSTS Transport Boundary

> Verifies the browser hosted hsts transport boundary behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted HSTS Transport Boundary

Verifies the browser hosted hsts transport boundary behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_hosted_hsts_transport_boundary_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser hosted hsts transport boundary behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### REQ-WEB-BROWSER-007: hosted HSTS transport boundary

#### keeps mock and cache headers out of the HSTS owner

- Verify: keeps mock and cache headers out of the HSTS owner
- Serve a mocked HTTPS document carrying HSTS
- Replay a cached HTTPS header without extending HSTS
- Keep HSTS ownership in the completed runtime-job branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-007
step("Verify: keeps mock and cache headers out of the HSTS owner")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Serve a mocked HTTPS document carrying HSTS")
var mocks = MockResponseRegistry.create()
mocks.register_with_headers(
    "https://mock-hsts.test/page", 200,
    [Pair("Strict-Transport-Security", "max-age=31536000")],
    "<main>mock</main>"
)
set_mock_registry(mocks)
var mocked = HostedWebContentSession.create(951, "about:blank", 32, 16)
expect(mocked.browser.begin_network_navigation(
    "https://mock-hsts.test/page", "GET", "", "", ""
).is_ok()).to_be(true)
val _ = mocked.advance_at(1)
expect(mocked.browser._hsts_upgrade_url(
    "http://mock-hsts.test/next"
)).to_equal("http://mock-hsts.test/next")

step("Replay a cached HTTPS header without extending HSTS")
var cached = HostedWebContentSession.create(952, "about:blank", 32, 16)
expect(cached.network.cache.store(
    "https://cache-hsts.test/page", rt_text_to_bytes("<main>cache</main>"),
    "Strict-Transport-Security: max-age=31536000\r\nCache-Control: max-age=60"
).is_ok()).to_be(true)
expect(cached.browser.begin_network_navigation(
    "https://cache-hsts.test/page", "GET", "", "", ""
).is_ok()).to_be(true)
val _ = cached.advance_at(1)
expect(cached.browser._hsts_upgrade_url(
    "http://cache-hsts.test/next"
)).to_equal("http://cache-hsts.test/next")

step("Keep HSTS ownership in the completed runtime-job branch")
expect(_hosted_hsts_source_has_runtime_owner()).to_be(true)
mocked.close()
cached.close()
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `489a36f323e78f47a207808be7b8e88aa6997fb6bf12bae2f5cf786437ec0748`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `489a36f323e78f47a207808be7b8e88aa6997fb6bf12bae2f5cf786437ec0748`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `489a36f323e78f47a207808be7b8e88aa6997fb6bf12bae2f5cf786437ec0748`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_hosted_hsts_transport_boundary_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_hosted_hsts_transport_boundary_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_hosted_hsts_transport_boundary_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_hosted_hsts_transport_boundary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_hosted_hsts_transport_boundary_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
