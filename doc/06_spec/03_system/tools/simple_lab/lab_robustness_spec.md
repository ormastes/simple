# Simple Lab robustness evidence (Stream H, task H3)

> Drives `src/app/simple_lab/lab_server.spl` as a **separate OS process** over a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Lab robustness evidence (Stream H, task H3)

Drives `src/app/simple_lab/lab_server.spl` as a **separate OS process** over a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/simple_lab/lab_robustness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Drives `src/app/simple_lab/lab_server.spl` as a **separate OS process** over a
**real TCP socket**, the same real-loopback subprocess pattern as
`lab_http_api_spec.spl` (L3) and `lab_hardening_spec.spl` (H1) — no mocks, no
in-process shim. Per the crash-safe execution rules referenced by the plan
(no parallel QEMU/bootstrap, loopback only, recorded limits), everything here
runs sequentially, one lab_server subprocess per example, on 127.0.0.1.

Three pieces of evidence, per design §8.5:
  1. **Load smoke** — a bounded run of sequential authenticated
     `GET /api/lab/status` requests, timed, all must return 200.
  2. **100-cell soak** — one session, 100 sequential real
     `POST .../cells/:cid/execute` calls (the real functional path, not
     `/api/test/click` — see the filed gap
     `doc/08_tracking/bug/lab_test_api_click_does_not_invoke_simple_lab_app_add_cell_2026-08-07.md`),
     all must return `ok:true`, panic-free.
  3. **Fuzz-lite corpus** — malformed JSON bodies, an oversized header line,
     a too-many-headers request, and a WS handshake truncated mid-write.
     Each gets its own example so a genuinely-failing assertion (see the
     oversized-header example below) stays visibly RED per
     `.claude/rules/testing.md` instead of being merged into one aggregate
     pass/fail that would hide it.

Numbers this spec measures are recorded verbatim into
`doc/09_report/notebook_lanes_robustness_evidence_2026-08-07.md` (H3 verify
requirement: "perf/robustness report checked into doc/09_report/ with
commands + numbers; zero panics").

Design: doc/05_design/app/tools/notebook_lanes_architecture.md §8.5
Plan:   doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md (Stream H, H3)

## Scenarios

### Simple Lab robustness evidence (H3: load smoke + 100-cell soak + fuzz-lite, real loopback)

#### load smoke: 200 sequential authenticated GET /api/lab/status requests, all 200, panic-free

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- load smoke: 200 sequential authenticated GET /api/lab/status requests, all 200, panic-free
- fire {n} sequential authenticated status requests and time each
   - Expected: ok_count equals `n`
- the server is still alive after the load smoke
   - Expected: final_status.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("load smoke: 200 sequential authenticated GET /api/lab/status requests, all 200, panic-free")
val n: i64 = 200
val server = start_lab_server(n + 5)
if not server.started:
    fail("lab_server subprocess did not start listening")

step("fire {n} sequential authenticated status requests and time each")
var ok_count: i64 = 0
var min_us: i64 = -1
var max_us: i64 = -1
var total_us: i64 = 0
var i: i64 = 0
while i < n:
    val t0 = rt_time_now_unix_micros()
    val resp = http_request(server.addr, "GET", "/api/lab/status", "")
    val t1 = rt_time_now_unix_micros()
    val dt = t1 - t0
    if resp.status == 200:
        ok_count = ok_count + 1
    total_us = total_us + dt
    if min_us < 0 or dt < min_us:
        min_us = dt
    if dt > max_us:
        max_us = dt
    i = i + 1

val avg_us = total_us / n
record("load_smoke requests={n} ok={ok_count} min_us={min_us} max_us={max_us} avg_us={avg_us}")
expect(ok_count).to_equal(n)
# Generous ceiling (5s/req) — this asserts "no pathological stall",
# not a tight perf budget; see the report for the actual numbers.
expect(max_us).to_be_less_than(5000000)

step("the server is still alive after the load smoke")
val final_status = http_request(server.addr, "GET", "/api/lab/status", "")
expect(final_status.status).to_equal(200)

server.stop()
```

</details>

#### 100-cell soak: one session, 100 sequential real cell executions, all ok, panic-free

- 100-cell soak: one session, 100 sequential real cell executions, all ok, panic-free
- create one real session
   - Expected: create_resp.status equals `201`
- execute {n} cells sequentially through the real .../execute route (not /api/test/click — see the filed gap for that path)
   - Expected: ok_count equals `n`
- the server is still alive and correct after the soak
   - Expected: final_status.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("100-cell soak: one session, 100 sequential real cell executions, all ok, panic-free")
val n: i64 = 100
val server = start_lab_server(n + 10)
if not server.started:
    fail("lab_server subprocess did not start listening")

step("create one real session")
val create_resp = http_request(server.addr, "POST", "/api/lab/sessions", "{\"default_mode\":\"interpreter\"}")
expect(create_resp.status).to_equal(201)
val session_id = json_field(create_resp.body, "id")
expect(session_id).to_start_with("sess_")

step("execute {n} cells sequentially through the real .../execute route (not /api/test/click — see the filed gap for that path)")
var ok_count: i64 = 0
var min_us: i64 = -1
var max_us: i64 = -1
var total_us: i64 = 0
var i: i64 = 0
while i < n:
    val cell_id = "c{i}"
    val exec_path = "/api/lab/sessions/{session_id}/cells/{cell_id}/execute"
    val source_json = "{\"source\":\"print(\\\"cell-{i}\\\")\"}"
    val t0 = rt_time_now_unix_micros()
    val resp = http_request(server.addr, "POST", exec_path, source_json)
    val t1 = rt_time_now_unix_micros()
    val dt = t1 - t0
    if resp.status == 200 and resp.body.contains("\"ok\":true"):
        ok_count = ok_count + 1
    total_us = total_us + dt
    if min_us < 0 or dt < min_us:
        min_us = dt
    if dt > max_us:
        max_us = dt
    i = i + 1

val avg_us = total_us / n
record("cell_soak cells={n} ok={ok_count} min_us={min_us} max_us={max_us} avg_us={avg_us}")
expect(ok_count).to_equal(n)

step("the server is still alive and correct after the soak")
val final_status = http_request(server.addr, "GET", "/api/lab/status", "")
expect(final_status.status).to_equal(200)
expect(final_status.body).to_contain("\"session_count\":1")

server.stop()
```

</details>

#### fuzz-lite: malformed JSON body corpus all get 4xx, never a panic

- fuzz-lite: malformed JSON body corpus all get 4xx, never a panic
- POST /api/lab/sessions with malformed body: {bad}
   - Expected: ok_count equals `bad_bodies.len()`
- the server survived the whole corpus and still answers correctly
   - Expected: final_status.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fuzz-lite: malformed JSON body corpus all get 4xx, never a panic")
val server = start_lab_server(20)
if not server.started:
    fail("lab_server subprocess did not start listening")

val bad_bodies = [
    "not json at all",
    "{{{{",
    "{\"default_mode\":}",
    "[1,2,",
    " binary-garbage",
    "{\"default_mode\":\"interpreter\"" # missing closing brace
]
var ok_count: i64 = 0
for bad in bad_bodies:
    step("POST /api/lab/sessions with malformed body: {bad}")
    val resp = http_request(server.addr, "POST", "/api/lab/sessions", bad)
    if resp.ok and resp.status >= 400 and resp.status < 500:
        ok_count = ok_count + 1
    else:
        record("fuzz_fail malformed_json body={bad} status={resp.status}")
record("fuzz_malformed_json total={bad_bodies.len()} ok={ok_count}")
expect(ok_count).to_equal(bad_bodies.len())

step("the server survived the whole corpus and still answers correctly")
val final_status = http_request(server.addr, "GET", "/api/lab/status", "")
expect(final_status.status).to_equal(200)

server.stop()
```

</details>

#### fuzz-lite: oversized single header line (20000 bytes) is rejected with 431 and does not crash the server

- fuzz-lite: oversized single header line (20000 bytes) is rejected with 431 and does not crash the server
- oversized single header line (20000 bytes, well over the 8192-byte cap)
- hard gate: the server answered something -- not a crashed/dropped connection
   - Expected: oversized_resp.ok is true
- hard gate: the server is still alive and correct for the next request
   - Expected: final_status.ok is true
   - Expected: final_status.status equals `200`
- design contract: the oversized header line is rejected with 431
   - Expected: oversized_resp.status equals `431`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fuzz-lite: oversized single header line (20000 bytes) is rejected with 431 and does not crash the server")
"""
Design §8.5 requires oversized headers to answer 4xx. The runtime
line reader (`read_line_chunked`,
`src/compiler_rust/runtime/src/value/net_tcp.rs`) silently truncates
any line at 8192 bytes without a trailing newline, so `parser.spl`'s
`hl.len() > max_header_line` check alone could never fire for this
input shape and the request used to be silently accepted (200).
Fixed 2026-08-08: `parser.spl` now detects the truncation signature
(raw line >= 8192 bytes with no terminating newline -- `read_line()`
returns the newline when one was found) and rejects with 431. See
`doc/08_tracking/bug/lab_http_parser_oversized_header_line_silently_truncated_not_rejected_2026-08-07.md`.
"""
val server = start_lab_server(10)
if not server.started:
    fail("lab_server subprocess did not start listening")

step("oversized single header line (20000 bytes, well over the 8192-byte cap)")
val fuzz_x = "x"
val huge_header = "X-Fuzz-Oversized: {repeat_char(fuzz_x, 20000)}\r\n"
val oversized_resp = http_request_ex(server.addr, "GET", "/api/lab/status", "", "Authorization: Bearer {TEST_TOKEN}\r\n{huge_header}")
record("fuzz_oversized_header status={oversized_resp.status} ok={oversized_resp.ok}")

step("hard gate: the server answered something -- not a crashed/dropped connection")
expect(oversized_resp.ok).to_equal(true)

step("hard gate: the server is still alive and correct for the next request")
val final_status = http_request(server.addr, "GET", "/api/lab/status", "")
expect(final_status.ok).to_equal(true)
expect(final_status.status).to_equal(200)

step("design contract: the oversized header line is rejected with 431")
expect(oversized_resp.status).to_equal(431)

server.stop()
```

</details>

#### fuzz-lite: too-many-headers request (110 headers) gets 4xx, never a panic

- fuzz-lite: too-many-headers request (110 headers) gets 4xx, never a panic
- too-many-headers request (110 headers, over the 100-header cap)
   - Expected: many_resp.ok is true
   - Expected: many_resp.status >= 400 and many_resp.status < 500 is true
- the server is still alive
   - Expected: final_status.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fuzz-lite: too-many-headers request (110 headers) gets 4xx, never a panic")
val server = start_lab_server(10)
if not server.started:
    fail("lab_server subprocess did not start listening")

step("too-many-headers request (110 headers, over the 100-header cap)")
var many_headers = "Authorization: Bearer {TEST_TOKEN}\r\n"
var h: i64 = 0
while h < 110:
    many_headers = "{many_headers}X-Fuzz-{h}: v\r\n"
    h = h + 1
val many_resp = http_request_ex(server.addr, "GET", "/api/lab/status", "", many_headers)
record("fuzz_too_many_headers status={many_resp.status} ok={many_resp.ok}")
expect(many_resp.ok).to_equal(true)
expect(many_resp.status >= 400 and many_resp.status < 500).to_equal(true)

step("the server is still alive")
val final_status = http_request(server.addr, "GET", "/api/lab/status", "")
expect(final_status.status).to_equal(200)

server.stop()
```

</details>

#### fuzz-lite: a WebSocket handshake truncated mid-write does not crash or hang the server

- fuzz-lite: a WebSocket handshake truncated mid-write does not crash or hang the server
- WS handshake request truncated mid-write (connection closed before the terminating CRLFCRLF) -- must not hang or crash the server
- the server is still alive and correct after the truncated handshake
   - Expected: final_status.ok is true
   - Expected: final_status.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fuzz-lite: a WebSocket handshake truncated mid-write does not crash or hang the server")
val server = start_lab_server(10)
if not server.started:
    fail("lab_server subprocess did not start listening")

step("WS handshake request truncated mid-write (connection closed before the terminating CRLFCRLF) -- must not hang or crash the server")
val trunc_stream_res = TcpStream.connect(server.addr)
if trunc_stream_res.is_err():
    fail("could not open the probe connection at all")
var trunc_stream = trunc_stream_res.unwrap()
# Deliberately incomplete: request line + one header, no blank line,
# then close -- simulates a client that dies mid-handshake.
val partial = "GET /api/lab/sessions/nonexistent/events HTTP/1.1\r\nUpgrade: websocket\r\n"
val _w = trunc_stream.write_text(partial)
val _f2 = trunc_stream.flush()
val _c2 = trunc_stream.close()
record("fuzz_truncated_ws_handshake survived=true")

step("the server is still alive and correct after the truncated handshake")
val final_status = http_request(server.addr, "GET", "/api/lab/status", "")
expect(final_status.ok).to_equal(true)
expect(final_status.status).to_equal(200)
expect(final_status.headers.to_lower()).to_contain("x-lab-protocol-version: 1")

server.stop()
flush_evidence()
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2ffc5d40edfab0dbdd495954106722688d9a8eeed50409ab8f60c323e8b425b9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2ffc5d40edfab0dbdd495954106722688d9a8eeed50409ab8f60c323e8b425b9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2ffc5d40edfab0dbdd495954106722688d9a8eeed50409ab8f60c323e8b425b9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/simple_lab/lab_robustness_spec.spl
mirror: doc/06_spec/03_system/tools/simple_lab/lab_robustness_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/simple_lab/lab_robustness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/simple_lab/lab_robustness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/simple_lab/lab_robustness_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/simple_lab/lab_robustness_spec.spl:268:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'load smoke: 200 sequential authenticated GET /api/lab/status requests, all 200, panic-free' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/simple_lab/lab_robustness_spec.spl:309:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '100-cell soak: one session, 100 sequential real cell executions, all ok, panic-free' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/simple_lab/lab_robustness_spec.spl:357:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fuzz-lite: malformed JSON body corpus all get 4xx, never a panic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
