# Simple Portal Server Specification

> Tests covering simple_portal server, simple_portal app identity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Portal Server Specification

## Scenarios

### simple_portal server

#### serves the landing page from the app filesystem root

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- serves the landing page from the app filesystem root


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("serves the landing page from the app filesystem root")
val resp = _server().route_request("GET", "/", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("Filesystem-first portal")
expect(resp).to_contain("Content-Security-Policy:")
```

</details>

#### normalizes duplicate slashes for public APIs

- normalizes duplicate slashes for public APIs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("normalizes duplicate slashes for public APIs")
val resp = _server().route_request("GET", "//api//portal//releases//", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("\"releases\"")
```

</details>

#### rejects static path traversal

- rejects static path traversal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects static path traversal")
val resp = _server().route_request("GET", "/static/../content/pages.db", "", "")
expect(resp).to_start_with("HTTP/1.1 404 Not Found")
```

</details>

#### rejects disallowed methods on public endpoints

- rejects disallowed methods on public endpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects disallowed methods on public endpoints")
val resp = _server().route_request("POST", "/api/portal/pages", "{}", "")
expect(resp).to_start_with("HTTP/1.1 405 Method Not Allowed")
expect(resp).to_contain("Allow: GET, HEAD")
```

</details>

#### rejects unauthorized playground runs

- rejects unauthorized playground runs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects unauthorized playground runs")
val headers = "Origin: http://localhost:4040\nX-Simple-Portal-Capability: playground.run\n"
val resp = _server().route_request("POST", "/api/playground/run", "{\"source\":\"print 1\"}", headers)
expect(resp).to_start_with("HTTP/1.1 403 Forbidden")
```

</details>

#### accepts authorized playground runs and returns a sandbox envelope

- accepts authorized playground runs and returns a sandbox envelope


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("accepts authorized playground runs and returns a sandbox envelope")
val headers = "Origin: http://localhost:4040\nX-Simple-Portal-Capability: playground.run\nX-Simple-Portal-Token: dev-token\n"
val resp = _server().route_request("POST", "/api/playground/run", "{\"mode\":\"sandbox\",\"source\":\"print 1\"}", headers)
expect(resp).to_start_with("HTTP/1.1 202 Accepted")
expect(resp).to_contain("\"runner\":\"simple run --sandbox\"")
expect(resp).to_contain("\"sandbox\":{\"filesystem\":false,\"network\":false,\"process\":false}")
```

</details>

#### rejects oversized playground bodies

- rejects oversized playground bodies


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects oversized playground bodies")
var body = "{"
var i = 0
while i < 17000:
    body = body + "a"
    i = i + 1
body = body + "}"
val headers = "Origin: http://localhost:4040\nX-Simple-Portal-Capability: playground.run\nX-Simple-Portal-Token: dev-token\n"
val resp = _server().route_request("POST", "/api/playground/run", body, headers)
expect(resp).to_start_with("HTTP/1.1 413 Request Entity Too Large")
```

</details>

### simple_portal app identity

#### uses stable sys app paths

- uses stable sys app paths
   - Expected: simple_portal_app_id() equals `/sys/apps/simple_portal`
   - Expected: simple_portal_exec_path() equals `/sys/apps/simple_portal.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses stable sys app paths")
expect(simple_portal_app_id()).to_equal("/sys/apps/simple_portal")
expect(simple_portal_exec_path()).to_equal("/sys/apps/simple_portal.smf")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/simple_portal/simple_portal_server_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simple_portal server, simple_portal app identity.
- simple_portal server
- simple_portal app identity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9fa76f45506af1c58c4c09494ad9fe4fb16e92e1df57642b6490db349f196ac8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9fa76f45506af1c58c4c09494ad9fe4fb16e92e1df57642b6490db349f196ac8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9fa76f45506af1c58c4c09494ad9fe4fb16e92e1df57642b6490db349f196ac8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/simple_portal/simple_portal_server_spec.spl
mirror: doc/06_spec/integration/app/simple_portal/simple_portal_server_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/simple_portal/simple_portal_server_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/simple_portal/simple_portal_server_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/simple_portal/simple_portal_server_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serves the landing page from the app filesystem root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/simple_portal/simple_portal_server_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes duplicate slashes for public APIs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/simple_portal/simple_portal_server_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects static path traversal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
