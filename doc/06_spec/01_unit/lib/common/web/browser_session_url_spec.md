# Browser Session Url Specification

> Tests covering BrowserSession URL authority helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Url Specification

## Scenarios

### BrowserSession URL authority helpers

#### separates origin host hostname query fragment and credentials

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- separates origin host hostname query fragment and credentials
   - Expected: url_authority("https://example.test?x=1#part") equals `example.test`
   - Expected: url_origin("https://example.test?x=1#part") equals `https://example.test`
   - Expected: url_host("https://user:secret@example.test:8443/path") equals `example.test:8443`
   - Expected: url_hostname("https://user:secret@example.test:8443/path") equals `example.test`
   - Expected: normalize_network_navigation_url("https:///missing-host").is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("separates origin host hostname query fragment and credentials")
expect(url_authority("https://example.test?x=1#part")).to_equal("example.test")
expect(url_origin("https://example.test?x=1#part")).to_equal("https://example.test")
expect(url_origin("https://example.test:443/path")).to_equal(
    "https://example.test"
)
expect(url_origin("http://example.test:080/path")).to_equal(
    "http://example.test"
)
expect(url_origin("https://example.test:8443/path")).to_equal(
    "https://example.test:8443"
)
expect(url_host("https://user:secret@example.test:8443/path")).to_equal("example.test:8443")
expect(url_hostname("https://user:secret@example.test:8443/path")).to_equal("example.test")
expect(normalize_network_navigation_url(
    "https://user:secret@example.test/path"
).is_err()).to_equal(true)
expect(normalize_network_navigation_url("https:///missing-host").is_err()).to_equal(true)
```

</details>

#### rejects request-line control characters

- rejects request-line control characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects request-line control characters")
expect(normalize_network_navigation_url(
    "https://example.test/path\r\nX-Injected: yes"
).is_err()).to_equal(true)
expect(normalize_network_navigation_url(
    "https://example.test/path\tmore"
).is_err()).to_equal(true)
```

</details>

#### rejects authorities the transport cannot route safely

- rejects authorities the transport cannot route safely
   - Expected: network_navigation_authority_valid("example.test") is true
   - Expected: network_navigation_authority_valid("example.test:443") is true
   - Expected: network_navigation_authority_valid("localhost:8080") is true
   - Expected: network_navigation_authority_valid("example.test:0") is false
   - Expected: network_navigation_authority_valid("example.test:65536") is false
   - Expected: network_navigation_authority_valid("example.test:https") is false
   - Expected: network_navigation_authority_valid("-bad.example") is false
   - Expected: network_navigation_authority_valid("bad..example") is false
   - Expected: network_navigation_authority_valid("[::1]:443") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects authorities the transport cannot route safely")
expect(network_navigation_authority_valid("example.test")).to_equal(true)
expect(network_navigation_authority_valid("example.test:443")).to_equal(true)
expect(network_navigation_authority_valid("localhost:8080")).to_equal(true)
expect(network_navigation_authority_valid("example.test:0")).to_equal(false)
expect(network_navigation_authority_valid("example.test:65536")).to_equal(false)
expect(network_navigation_authority_valid("example.test:https")).to_equal(false)
expect(network_navigation_authority_valid("-bad.example")).to_equal(false)
expect(network_navigation_authority_valid("bad..example")).to_equal(false)
expect(network_navigation_authority_valid("[::1]:443")).to_equal(true)
```

</details>

#### should admit only canonical bracketed IPv6 authorities

- should admit only canonical bracketed IPv6 authorities
- Validate an IPv6 HTTPS authority used by the hosted transport
   - Expected: parse_url("https://[::]/") != nil is true
   - Expected: parse_url("https://[::ffff:192.0.2.1]/") != nil is true
- Reject malformed literals and authority suffixes before transport
   - Expected: network_navigation_authority_valid("[::1") is false
   - Expected: network_navigation_authority_valid("[::1]evil") is false
   - Expected: network_navigation_authority_valid("[not:v6]:443") is false
   - Expected: network_navigation_authority_valid("[::1]:0") is false
   - Expected: network_navigation_authority_valid("[::1]@evil.test") is false
   - Expected: parse_url("https://[1:2:3:4:5:6:7:8:9]/") != nil is false
   - Expected: parse_url("https://[1:2:3:4:5:6:7:10000]/") != nil is false
   - Expected: parse_url("https://[1::2::3]/") != nil is false
   - Expected: parse_url("https://[::ffff:192.0.2.999]/") != nil is false
   - Expected: parse_url("https://[1:2:3:4:5:6:192.0.2.1:7]/") != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should admit only canonical bracketed IPv6 authorities")
step("Validate an IPv6 HTTPS authority used by the hosted transport")
expect(network_navigation_authority_valid(
    "[2606:4700:4700::1111]:443"
)).to_equal(true)
expect(normalize_network_navigation_url(
    "https://[2606:4700:4700::1111]:443/status"
)).to_equal("https://[2606:4700:4700::1111]:443/status")
expect(parse_url("https://[::]/") != nil).to_equal(true)
expect(parse_url(
    "https://[1:2:3:4:5:6:7:8]/"
) != nil).to_equal(true)
expect(parse_url("https://[::ffff:192.0.2.1]/") != nil).to_equal(true)

step("Reject malformed literals and authority suffixes before transport")
expect(network_navigation_authority_valid("[::1")).to_equal(false)
expect(network_navigation_authority_valid("[::1]evil")).to_equal(false)
expect(network_navigation_authority_valid("[not:v6]:443")).to_equal(false)
expect(network_navigation_authority_valid("[::1]:0")).to_equal(false)
expect(network_navigation_authority_valid("[::1]@evil.test")).to_equal(false)
expect(parse_url("https://[1:2:3:4:5:6:7:8:9]/") != nil).to_equal(false)
expect(parse_url("https://[1:2:3:4:5:6:7:10000]/") != nil).to_equal(false)
expect(parse_url("https://[1::2::3]/") != nil).to_equal(false)
expect(parse_url("https://[::ffff:192.0.2.999]/") != nil).to_equal(false)
expect(parse_url("https://[1:2:3:4:5:6:192.0.2.1:7]/") != nil).to_equal(false)
```

</details>

#### encodes address-bar search text as one UTF-8 query value

- encodes address-bar search text as one UTF-8 query value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encodes address-bar search text as one UTF-8 query value")
expect(browser_url_form_encode("Ada & 한")).to_equal(
    "Ada+%26+%ED%95%9C"
)
expect(normalize_browser_url("Ada & 한")).to_equal(
    "https://search.example.com/?q=Ada+%26+%ED%95%9C"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_url_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserSession URL authority helpers.
- BrowserSession URL authority helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-WEB-BROWSER-010`
- `REQ-WEB-BROWSER-011`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5abe3bde1736d321800e230d64fbdbb7e2866437bfd7173c6ab083286eb2df54`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5abe3bde1736d321800e230d64fbdbb7e2866437bfd7173c6ab083286eb2df54`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5abe3bde1736d321800e230d64fbdbb7e2866437bfd7173c6ab083286eb2df54`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/web/browser_session_url_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_url_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=95 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/web/browser_session_url_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_url_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_url_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/web/browser_session_url_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'separates origin host hostname query fragment and credentials' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_url_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects request-line control characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_url_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects authorities the transport cannot route safely' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_url_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should admit only canonical bracketed IPv6 authorities' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
