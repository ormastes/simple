# Server Specification

> Tests covering HttpRequest.body_json (parse_flat_json), HttpServer.dispatch_raw (in-process, no real socket).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Server Specification

## Scenarios

### HttpRequest.body_json (parse_flat_json)

#### parses a flat JSON object

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a flat JSON object
   - Expected: parsed.get("a") ?? "" equals `1`
   - Expected: parsed.get("b") ?? "" equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses a flat JSON object")
val headers: Dict<text, text> = {}
val req = HttpRequest.create("POST", "/x", headers, "{\"a\":\"1\",\"b\":\"2\"}", "")
val parsed = req.body_json()
expect(parsed.get("a") ?? "").to_equal("1")
expect(parsed.get("b") ?? "").to_equal("2")
```

</details>

#### handles commas embedded inside string values (the bug the old split-based parser had)

- handles commas embedded inside string values (the bug the old split-based parser had)
   - Expected: parsed.get("a") ?? "" equals `x,y`
   - Expected: parsed.get("b") ?? "" equals `z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles commas embedded inside string values (the bug the old split-based parser had)")
val headers: Dict<text, text> = {}
val req = HttpRequest.create("POST", "/x", headers, "{\"a\":\"x,y\",\"b\":\"z\"}", "")
val parsed = req.body_json()
expect(parsed.get("a") ?? "").to_equal("x,y")
expect(parsed.get("b") ?? "").to_equal("z")
```

</details>

#### returns an empty dict for non-object JSON

- returns an empty dict for non-object JSON
   - Expected: parsed.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns an empty dict for non-object JSON")
val headers: Dict<text, text> = {}
val req = HttpRequest.create("POST", "/x", headers, "[1,2,3]", "")
val parsed = req.body_json()
expect(parsed.len()).to_equal(0)
```

</details>

### HttpServer.dispatch_raw (in-process, no real socket)

#### dispatches a raw HTTP request to the registered handler

- dispatches a raw HTTP request to the registered handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dispatches a raw HTTP request to the registered handler")
var server = HttpServer.localhost(0)
server = server.handler(echo_path_handler)
val raw = "GET /world HTTP/1.1\r\nHost: localhost\r\n\r\n"
val response_text = server.dispatch_raw(raw)
expect(response_text).to_contain("200")
expect(response_text).to_contain("hello /world")
```

</details>

#### falls back to the default 404 handler when none is registered

- falls back to the default 404 handler when none is registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back to the default 404 handler when none is registered")
val server = HttpServer.localhost(0)
val raw = "GET /missing HTTP/1.1\r\nHost: localhost\r\n\r\n"
val response_text = server.dispatch_raw(raw)
expect(response_text).to_contain("404")
```

</details>

#### returns 400 Bad Request for malformed input

- returns 400 Bad Request for malformed input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 400 Bad Request for malformed input")
val server = HttpServer.localhost(0)
val response_text = server.dispatch_raw("not an http request")
expect(response_text).to_contain("400")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/web/http/server_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HttpRequest.body_json (parse_flat_json), HttpServer.dispatch_raw (in-process, no real socket).
- HttpRequest.body_json (parse_flat_json)
- HttpServer.dispatch_raw (in-process, no real socket)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `258dff8c5a5e8baf163d2331729b924f3cdd93b6ec77c8c8b2ca6009ce19532e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `258dff8c5a5e8baf163d2331729b924f3cdd93b6ec77c8c8b2ca6009ce19532e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `258dff8c5a5e8baf163d2331729b924f3cdd93b6ec77c8c8b2ca6009ce19532e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/web/http/server_spec.spl
mirror: doc/06_spec/01_unit/lib/web/http/server_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/web/http/server_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/web/http/server_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/web/http/server_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/web/http/server_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a flat JSON object' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/web/http/server_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles commas embedded inside string values (the bug the old split-based parser had)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/web/http/server_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an empty dict for non-object JSON' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
