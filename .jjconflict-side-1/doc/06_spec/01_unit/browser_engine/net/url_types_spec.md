# URL Types Specification

> Verifies URL and Origin entity types: construction, field access, scheme/host/port/path extraction, and origin computation. No network calls — pure value-type logic.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# URL Types Specification

Verifies URL and Origin entity types: construction, field access, scheme/host/port/path extraction, and origin computation. No network calls — pure value-type logic.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #M16-AC1 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/browser_engine/net/url_types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies URL and Origin entity types: construction, field access, scheme/host/port/path
extraction, and origin computation. No network calls — pure value-type logic.

## Scenarios

### Url entity type

#### when constructing a simple http URL

#### AC-1: stores scheme correctly

- AC-1: stores scheme correctly
   - Expected: u.scheme equals `http`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: stores scheme correctly")
val u = make_http_url()
expect(u.scheme).to_equal("http")
```

</details>

#### AC-1: stores host correctly

- AC-1: stores host correctly
   - Expected: u.host equals `example.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: stores host correctly")
val u = make_http_url()
expect(u.host).to_equal("example.com")
```

</details>

#### AC-1: stores default port 80 for http

- AC-1: stores default port 80 for http
   - Expected: u.port equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: stores default port 80 for http")
val u = make_http_url()
expect(u.port).to_equal(80)
```

</details>

#### AC-1: stores path correctly

- AC-1: stores path correctly
   - Expected: u.path equals `/index.html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: stores path correctly")
val u = make_http_url()
expect(u.path).to_equal("/index.html")
```

</details>

#### when constructing an https URL with explicit port

#### AC-1: stores https scheme

- AC-1: stores https scheme
   - Expected: u.scheme equals `https`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: stores https scheme")
val u = make_https_explicit_port_url()
expect(u.scheme).to_equal("https")
```

</details>

#### AC-1: stores explicit port 8443

- AC-1: stores explicit port 8443
   - Expected: u.port equals `8443`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: stores explicit port 8443")
val u = make_https_explicit_port_url()
expect(u.port).to_equal(8443)
```

</details>

#### AC-1: stores host without port

- AC-1: stores host without port
   - Expected: u.host equals `api.example.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: stores host without port")
val u = make_https_explicit_port_url()
expect(u.host).to_equal("api.example.com")
```

</details>

#### when URL has query string

#### AC-1: stores query string

- AC-1: stores query string
   - Expected: u.query equals `foo=bar&baz=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: stores query string")
val u = make_url_with_query()
expect(u.query).to_equal("foo=bar&baz=1")
```

</details>

#### when URL has fragment

#### AC-1: stores fragment

- AC-1: stores fragment
   - Expected: u.fragment equals `section-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: stores fragment")
val u = make_url_with_fragment()
expect(u.fragment).to_equal("section-2")
```

</details>

#### when URL has empty path

#### AC-1: path is empty string or slash

- AC-1: path is empty string or slash
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: path is empty string or slash")
val u = make_root_url()
val ok = (u.path == "/" or u.path == "")
expect(ok).to_equal(true)
```

</details>

### Origin from Url

#### AC-5: same scheme+host+port is same origin

- AC-5: same scheme+host+port is same origin
   - Expected: a.scheme equals `b.scheme`
   - Expected: a.host equals `b.host`
   - Expected: a.port equals `b.port`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: same scheme+host+port is same origin")
val a = make_origin("https", "example.com", 443)
val b = make_origin("https", "example.com", 443)
expect(a.scheme).to_equal(b.scheme)
expect(a.host).to_equal(b.host)
expect(a.port).to_equal(b.port)
```

</details>

#### AC-5: different scheme is different origin

- AC-5: different scheme is different origin
   - Expected: same is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: different scheme is different origin")
val a = make_origin("http", "example.com", 80)
val b = make_origin("https", "example.com", 443)
val same = (a.scheme == b.scheme)
expect(same).to_equal(false)
```

</details>

#### AC-5: different host is different origin

- AC-5: different host is different origin
   - Expected: same is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: different host is different origin")
val a = make_origin("https", "example.com", 443)
val b = make_origin("https", "other.com", 443)
val same = (a.host == b.host)
expect(same).to_equal(false)
```

</details>

#### AC-5: different port is different origin

- AC-5: different port is different origin
   - Expected: same is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: different port is different origin")
val a = make_origin("https", "example.com", 443)
val b = make_origin("https", "example.com", 8443)
val same = (a.port == b.port)
expect(same).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER_ENGINE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `99da4f8d0a84c977df615bf23097a8ce60f384d91a0e61e5c816c508cbf95677`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `99da4f8d0a84c977df615bf23097a8ce60f384d91a0e61e5c816c508cbf95677`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `99da4f8d0a84c977df615bf23097a8ce60f384d91a0e61e5c816c508cbf95677`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/browser_engine/net/url_types_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/net/url_types_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/net/url_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/net/url_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/net/url_types_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/net/url_types_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: stores scheme correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/net/url_types_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: stores host correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/net/url_types_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: stores default port 80 for http' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
