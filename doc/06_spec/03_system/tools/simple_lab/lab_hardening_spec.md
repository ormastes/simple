# Simple Lab HTTP/WS API — hardening contract (Stream H, task H1)

> Drives `src/app/simple_lab/lab_server.spl` as a **separate OS process** over a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Lab HTTP/WS API — hardening contract (Stream H, task H1)

Drives `src/app/simple_lab/lab_server.spl` as a **separate OS process** over a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/simple_lab/lab_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Drives `src/app/simple_lab/lab_server.spl` as a **separate OS process** over a
**real TCP socket**, same real-loopback subprocess pattern as
`test/03_system/tools/simple_lab/lab_http_api_spec.spl` (L3) — an in-process
call proves nothing about the actual wire, and the auth/origin/bounds gate
lives in `LabServer.handle_connection`, which only a real socket exercises.

Verifies design §8.1-§8.2 (`doc/05_design/app/tools/notebook_lanes_architecture.md`):
no-token 401, bad-origin WS refused, oversized body 413, traversal path 403,
malformed JSON 400 without panic, output-cap truncation marker. Every limit
this spec pins is env-configurable (`app.simple_lab.lab_hardening`) — the
values below are deliberately small so the spec doesn't need multi-megabyte
payloads to exercise the caps.

Design: doc/05_design/app/tools/notebook_lanes_architecture.md §8.1-§8.2
Plan:   doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md (Stream H, H1)

## Scenarios

### Simple Lab hardening (H1: auth + bounds, real loopback)

#### refuses a request with no Authorization header: 401

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- refuses a request with no Authorization header: 401
- GET /api/lab/status with no bearer token
   - Expected: resp.ok is true
   - Expected: resp.status equals `401`
- a wrong bearer token also gets 401 (not just missing-header)
   - Expected: resp2.status equals `401`
- the correct bearer token is accepted
   - Expected: resp3.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses a request with no Authorization header: 401")
val server = start_lab_server(20)
if not server.started:
    fail("lab_server subprocess did not start listening")

step("GET /api/lab/status with no bearer token")
val resp = http_request_no_auth(server.addr, "GET", "/api/lab/status", "")
expect(resp.ok).to_equal(true)
expect(resp.status).to_equal(401)
expect(resp.headers.to_lower()).to_contain("x-lab-protocol-version: 1")

step("a wrong bearer token also gets 401 (not just missing-header)")
val resp2 = http_request_bad_auth(server.addr, "GET", "/api/lab/status", "")
expect(resp2.status).to_equal(401)

step("the correct bearer token is accepted")
val resp3 = http_request(server.addr, "GET", "/api/lab/status", "")
expect(resp3.status).to_equal(200)

server.stop()
```

</details>

#### refuses a WebSocket upgrade from a disallowed Origin, but allows an allow-listed one

- refuses a WebSocket upgrade from a disallowed Origin, but allows an allow-listed one
- create a real session to have a valid events path
   - Expected: create_resp.status equals `201`
- a WS upgrade from a disallowed Origin never gets a 101
- a WS upgrade from the allow-listed Origin with the right token gets 101
- a WS upgrade from the allow-listed Origin but no token is refused (401), not upgraded


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses a WebSocket upgrade from a disallowed Origin, but allows an allow-listed one")
val server = start_lab_server_with_env(20, [
    "SIMPLE_LAB_TOKEN={TEST_TOKEN}",
    "SIMPLE_LAB_ALLOWED_ORIGINS=http://allowed.example"
])
if not server.started:
    fail("lab_server subprocess did not start listening")

step("create a real session to have a valid events path")
val create_resp = http_request(server.addr, "POST", "/api/lab/sessions", "{\"default_mode\":\"interpreter\"}")
expect(create_resp.status).to_equal(201)
val session_id = json_field(create_resp.body, "id")

step("a WS upgrade from a disallowed Origin never gets a 101")
val bad_head = ws_handshake_probe(server.addr, "/api/lab/sessions/{session_id}/events", "http://evil.example", TEST_TOKEN)
expect(bad_head).to_contain("403")
expect(bad_head).to_not_contain("101 Switching Protocols")

step("a WS upgrade from the allow-listed Origin with the right token gets 101")
val good_head = ws_handshake_probe(server.addr, "/api/lab/sessions/{session_id}/events", "http://allowed.example", TEST_TOKEN)
expect(good_head).to_contain("101 Switching Protocols")

step("a WS upgrade from the allow-listed Origin but no token is refused (401), not upgraded")
val no_token_head = ws_handshake_probe(server.addr, "/api/lab/sessions/{session_id}/events", "http://allowed.example", "")
expect(no_token_head).to_not_contain("101 Switching Protocols")

server.stop()
```

</details>

#### answers 413 (not 400) when the body exceeds the configured max body size

- answers 413 (not 400) when the body exceeds the configured max body size
- PUT a notebook body far larger than the 64-byte cap
   - Expected: resp.ok is true
   - Expected: resp.status equals `413`
- the server is still alive and answers the next request
   - Expected: status_resp.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("answers 413 (not 400) when the body exceeds the configured max body size")
val server = start_lab_server_with_env(20, [
    "SIMPLE_LAB_TOKEN={TEST_TOKEN}",
    "SIMPLE_LAB_MAX_BODY_BYTES=64"
])
if not server.started:
    fail("lab_server subprocess did not start listening")

step("PUT a notebook body far larger than the 64-byte cap")
var big = ""
var i = 0
while i < 200:
    big = "{big}x"
    i = i + 1
val resp = http_request(server.addr, "PUT", "/api/lab/notebooks/too_big.snb.sdn", big)
expect(resp.ok).to_equal(true)
expect(resp.status).to_equal(413)
expect(resp.headers.to_lower()).to_contain("x-lab-protocol-version: 1")

step("the server is still alive and answers the next request")
val status_resp = http_request(server.addr, "GET", "/api/lab/status", "")
expect(status_resp.status).to_equal(200)

server.stop()
```

</details>

#### answers 413 when a single cell's source exceeds the configured max cell size

- answers 413 when a single cell's source exceeds the configured max cell size
   - Expected: create_resp.status equals `201`
- a cell source well over 16 bytes is rejected with 413
   - Expected: exec_resp.status equals `413`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("answers 413 when a single cell's source exceeds the configured max cell size")
val server = start_lab_server_with_env(20, [
    "SIMPLE_LAB_TOKEN={TEST_TOKEN}",
    "SIMPLE_LAB_MAX_CELL_BYTES=16"
])
if not server.started:
    fail("lab_server subprocess did not start listening")

val create_resp = http_request(server.addr, "POST", "/api/lab/sessions", "{\"default_mode\":\"interpreter\"}")
expect(create_resp.status).to_equal(201)
val session_id = json_field(create_resp.body, "id")

step("a cell source well over 16 bytes is rejected with 413")
val exec_resp = http_request(server.addr, "POST", "/api/lab/sessions/{session_id}/cells/c1/execute", "{\"source\":\"print(\\\"this source is much longer than sixteen bytes\\\")\"}")
expect(exec_resp.status).to_equal(413)

server.stop()
```

</details>

#### answers 403 (not the router's blanket 400) for a traversal-flavored notebook name

- answers 403 (not the router's blanket 400) for a traversal-flavored notebook name
- GET .../notebooks/NAME where NAME contains '..' but isn't a router-level '..' segment
   - Expected: resp.ok is true
   - Expected: resp.status equals `403`
- same guard applies to PUT
   - Expected: put_resp.status equals `403`
- the server is still alive
   - Expected: status_resp.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("answers 403 (not the router's blanket 400) for a traversal-flavored notebook name")
val server = start_lab_server(20)
if not server.started:
    fail("lab_server subprocess did not start listening")

step("GET .../notebooks/NAME where NAME contains '..' but isn't a router-level '..' segment")
val resp = http_request(server.addr, "GET", "/api/lab/notebooks/..hidden", "")
expect(resp.ok).to_equal(true)
expect(resp.status).to_equal(403)
expect(resp.headers.to_lower()).to_contain("x-lab-protocol-version: 1")

step("same guard applies to PUT")
val put_resp = http_request(server.addr, "PUT", "/api/lab/notebooks/..hidden", "irrelevant body")
expect(put_resp.status).to_equal(403)

step("the server is still alive")
val status_resp = http_request(server.addr, "GET", "/api/lab/status", "")
expect(status_resp.status).to_equal(200)

server.stop()
```

</details>

#### answers 400 (not a panic/connection-drop) for a malformed JSON body on every JSON-consuming route

- answers 400 (not a panic/connection-drop) for a malformed JSON body on every JSON-consuming route
- POST /api/lab/sessions with garbage JSON
   - Expected: create_resp.ok is true
   - Expected: create_resp.status equals `400`
- a real session for the execute/interrupt/reset malformed-body checks
   - Expected: ok_create.status equals `201`
- POST .../execute with garbage JSON
   - Expected: exec_resp.ok is true
   - Expected: exec_resp.status equals `400`
- POST .../reset with garbage JSON
   - Expected: reset_resp.ok is true
   - Expected: reset_resp.status equals `400`
- the server never panicked/dropped the connection — it is still alive and correct
   - Expected: status_resp.ok is true
   - Expected: status_resp.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("answers 400 (not a panic/connection-drop) for a malformed JSON body on every JSON-consuming route")
val server = start_lab_server(20)
if not server.started:
    fail("lab_server subprocess did not start listening")

step("POST /api/lab/sessions with garbage JSON")
val create_resp = http_request(server.addr, "POST", "/api/lab/sessions", "not valid json {{{")
expect(create_resp.ok).to_equal(true)
expect(create_resp.status).to_equal(400)

step("a real session for the execute/interrupt/reset malformed-body checks")
val ok_create = http_request(server.addr, "POST", "/api/lab/sessions", "{\"default_mode\":\"interpreter\"}")
expect(ok_create.status).to_equal(201)
val session_id = json_field(ok_create.body, "id")

step("POST .../execute with garbage JSON")
val exec_resp = http_request(server.addr, "POST", "/api/lab/sessions/{session_id}/cells/c1/execute", "{{{not json")
expect(exec_resp.ok).to_equal(true)
expect(exec_resp.status).to_equal(400)

step("POST .../reset with garbage JSON")
val reset_resp = http_request(server.addr, "POST", "/api/lab/sessions/{session_id}/reset", "{{{not json")
expect(reset_resp.ok).to_equal(true)
expect(reset_resp.status).to_equal(400)

step("the server never panicked/dropped the connection — it is still alive and correct")
val status_resp = http_request(server.addr, "GET", "/api/lab/status", "")
expect(status_resp.ok).to_equal(true)
expect(status_resp.status).to_equal(200)

server.stop()
```

</details>

#### rejects an oversized header line with 431 instead of silently truncating it

- rejects an oversized header line with 431 instead of silently truncating it
- build one header value well over the 8192-byte runtime line cap
- the request is rejected with 431, not answered 200 off a truncated header
   - Expected: resp.ok is true
   - Expected: resp.status equals `431`
- the server is still alive and answers the next well-formed request
   - Expected: status_resp.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects an oversized header line with 431 instead of silently truncating it")
"""
A header line longer than the runtime line reader's 8192-byte cap
used to be silently truncated by `read_line_chunked` (Rust runtime),
making `parser.spl`'s own `> max_header_line` guard structurally
unreachable -- the request got a 200 off a mangled header. Fixed
2026-08-08 in `parser.spl` (truncation-signature detection); see
`doc/08_tracking/bug/lab_http_parser_oversized_header_line_silently_truncated_not_rejected_2026-08-07.md`.
"""
val server = start_lab_server(20)
if not server.started:
    fail("lab_server subprocess did not start listening")

step("build one header value well over the 8192-byte runtime line cap")
var big = "x"
while big.len() < 20000:
    big = "{big}{big}"
val resp = http_request_ex(server.addr, "GET", "/api/lab/status", "", "Authorization: Bearer {TEST_TOKEN}\r\nX-Oversized: {big}\r\n")

step("the request is rejected with 431, not answered 200 off a truncated header")
expect(resp.ok).to_equal(true)
expect(resp.status).to_equal(431)
expect(resp.headers).to_contain("Request Header Fields Too Large")

step("the server is still alive and answers the next well-formed request")
val status_resp = http_request(server.addr, "GET", "/api/lab/status", "")
expect(status_resp.status).to_equal(200)

server.stop()
```

</details>

#### truncates cell output with an explicit marker once it exceeds the configured max output size

- truncates cell output with an explicit marker once it exceeds the configured max output size
   - Expected: create_resp.status equals `201`
- a cell that prints well over 8 bytes of stdout gets a truncated, marker-annotated response
   - Expected: exec_resp.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("truncates cell output with an explicit marker once it exceeds the configured max output size")
val server = start_lab_server_with_env(20, [
    "SIMPLE_LAB_TOKEN={TEST_TOKEN}",
    "SIMPLE_LAB_MAX_OUTPUT_BYTES=8"
])
if not server.started:
    fail("lab_server subprocess did not start listening")

val create_resp = http_request(server.addr, "POST", "/api/lab/sessions", "{\"default_mode\":\"interpreter\"}")
expect(create_resp.status).to_equal(201)
val session_id = json_field(create_resp.body, "id")

step("a cell that prints well over 8 bytes of stdout gets a truncated, marker-annotated response")
val exec_resp = http_request(server.addr, "POST", "/api/lab/sessions/{session_id}/cells/c1/execute", "{\"source\":\"print(\\\"0123456789ABCDEF\\\")\"}")
expect(exec_resp.status).to_equal(200)
expect(exec_resp.body).to_contain("[truncated:")
expect(exec_resp.body).to_not_contain("0123456789ABCDEF")

server.stop()
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1e3689132186a385f4e819612ccccf0a0e99b5bfb8d6a7644f238987aa5c1d9e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1e3689132186a385f4e819612ccccf0a0e99b5bfb8d6a7644f238987aa5c1d9e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1e3689132186a385f4e819612ccccf0a0e99b5bfb8d6a7644f238987aa5c1d9e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/simple_lab/lab_hardening_spec.spl
mirror: doc/06_spec/03_system/tools/simple_lab/lab_hardening_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/simple_lab/lab_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/simple_lab/lab_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/simple_lab/lab_hardening_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/simple_lab/lab_hardening_spec.spl:270:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a request with no Authorization header: 401' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/simple_lab/lab_hardening_spec.spl:293:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a WebSocket upgrade from a disallowed Origin, but allows an allow-listed one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/simple_lab/lab_hardening_spec.spl:323:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'answers 413 (not 400) when the body exceeds the configured max body size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
