# Notebook Lanes — Simple Lab robustness evidence (Stream H, task H3)

**Date:** 2026-08-07
**Scope:** `doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md`
Stream H, task H3 ("Robustness evidence"). Steps per plan: "design §8.5 load
smoke + 100-cell soak + fuzz-lite corpus, under the existing crash-safe
execution rules (no parallel QEMU/bootstrap; loopback; recorded limits)."
Verify: "perf/robustness report checked into `doc/09_report/` with commands +
numbers; zero panics."

Design reference: `doc/05_design/app/tools/notebook_lanes_architecture.md`
§8.5.

## Summary

- **Zero panics / zero crashes on the load smoke and 100-cell soak.** All 300
  real HTTP round trips (200 status polls + 100 real cell executions)
  succeeded, and the server answered correctly afterward.
- **Fuzz-lite corpus: 5 of 6 examples pass** (malformed JSON, too-many-headers,
  truncated WS handshake, plus the two hard "no panic" gates on the sixth).
  One assertion is a genuine, filed gap (see below) — left RED, not weakened.
- One real bug was found and **fixed** during this work (a crash, not a
  cosmetic issue): `TcpStream` had no `read_bytes` method even though
  `http_server/parser.spl` called it on every request with a body, so
  **every POST/PUT to Simple Lab crashed the server process outright**. Fixed
  in `src/lib/nogc_sync_mut/io/tcp.spl`.
- A second, non-crashing gap was found and **filed** (not fixed — it's a
  native-runtime primitive, out of scope for this task): an oversized HTTP
  header line is silently truncated instead of rejected with 4xx.

## Files

- Spec (new): `test/03_system/tools/simple_lab/lab_robustness_spec.spl`
- Fix (this task): `src/lib/nogc_sync_mut/io/tcp.spl` — added `TcpStream.read_bytes(count: i32) -> Result<text, IoError>`
- Bugs filed:
  - `doc/08_tracking/bug/lab_http_parser_oversized_header_line_silently_truncated_not_rejected_2026-08-07.md`
- This report: `doc/09_report/notebook_lanes_robustness_evidence_2026-08-07.md`

## Bug found and fixed: `TcpStream.read_bytes` did not exist — every request with a body crashed the server process

Before writing the H3 spec, the plan's known-gap note (`/api/test/click`
not reaching `add_cell`) was the only documented gap. Running the very first
draft of the H3 spec surfaced a second, much more serious one: **every**
`POST`/`PUT` request to `lab_server.spl` (create session, execute cell, save
notebook — anything with a body) crashed the server process.

Root cause: `src/lib/nogc_sync_mut/http_server/parser.spl:101` calls
`stream.read_bytes(content_length)` whenever `Content-Length > 0`, but
`TcpStream` (`src/lib/nogc_sync_mut/io/tcp.spl`) only defined `read()`,
`read_exact()`, `read_all()`, `read_text()`, and `read_line()` — no
`read_bytes`. Under the interpreter this is a fatal, unrecovered semantic
error that terminates the whole process (verified directly: after sending one
POST with a body to a manually-started `lab_server.spl`, `ps aux` showed the
process gone and a second connection attempt got `Connection refused`).

This is why H1's own hardening spec (which POSTs bodies on every example)
must have been passing on stale/cached state, or the crash was masked by
something in that particular run's timing — either way, the moment a POST
body actually reached this code path fresh, it took the whole server down.
Not a cosmetic issue: this would have crashed **any** consumer of
`parse_request_with_limits` with a body, not just Simple Lab.

**Fix:** added a real `read_bytes` method to `TcpStream`
(`src/lib/nogc_sync_mut/io/tcp.spl`), matching the exact-byte-count semantics
`Content-Length` requires (not "read until EOF" like `read_text`), built as a
thin wrapper over the existing `read_exact` + the file's own
`rt_bytes_to_text`:

```simple
fn read_bytes(count: i32) -> Result<text, IoError>:
    val bytes = self.read_exact(count.to_i64())?
    val s = rt_bytes_to_text(bytes)
    Ok(s)
```

Confirmed fixed two ways:
1. Direct raw-socket repro against a manually-started `lab_server.spl`: same
   POST that previously reset the connection and killed the process now
   returns a normal `201 Created`.
2. Re-ran `test/03_system/tools/simple_lab/lab_hardening_spec.spl` (H1) after
   the fix — **7/7 passed** (it POSTs bodies on 6 of its 7 examples).

## Evidence

All commands below were run from the repo root, sequentially (one at a time,
no parallel QEMU/bootstrap), loopback (`127.0.0.1`) only, against the
self-hosted `bin/simple` binary. Every limit exercised is the H1-landed
`app.simple_lab.lab_hardening` config, using its documented safe defaults
(`MAX_HEADER_LINE=8192`, `MAX_HEADER_COUNT=100`) unless noted.

```
bin/simple test test/03_system/tools/simple_lab/lab_robustness_spec.spl
```

Final result: **6 examples, 5 passed, 1 failed** (the filed, non-crashing
gap below). Zero panics/hangs across all 6.

```
SPEC FILE VERDICT: test/03_system/tools/simple_lab/lab_robustness_spec.spl declared>=6 executed=6 passed=5 failed=1 dropped=0
Test Summary
Passed: 5
Failed: 1
Results: 6 total, 5 passed, 1 failed
```

### 1. Load smoke — 200 sequential authenticated `GET /api/lab/status`

Design §8.5: "bounded `wrk`-based smoke on `/api/lab/status`." This repo has
no `wrk` dependency wired in, so the smoke is driven the same way every other
system spec in this suite drives real traffic: a real loopback `TcpStream`
client, sequential (not concurrent — `LabServer.handle_connection` is
single-connection-at-a-time by design, see `lab_server.spl`'s docstring), 200
requests, each timed individually.

| Metric | Value |
|---|---|
| Requests | 200 |
| OK (status 200) | 200 / 200 |
| Min latency | 3,791 µs (3.79 ms) |
| Max latency | 6,563 µs (6.56 ms) |
| Avg latency | 4,751 µs (4.75 ms) |

No pathological stalls (assertion ceiling was a generous 5s/request; the
observed max was ~6.6 ms, three orders of magnitude under it). Server
answered correctly immediately after the run.

### 2. 100-cell soak — one session, 100 sequential real cell executions

Design §8.5: "100-cell execute soak on the local lane." Driven through the
real `POST /api/lab/sessions/:id/cells/:cid/execute` route (L3's functional
path) — **not** `/api/test/click`, which is known not to invoke
`SimpleLabApp.add_cell()` (see
`doc/08_tracking/bug/lab_test_api_click_does_not_invoke_simple_lab_app_add_cell_2026-08-07.md`).
Each cell executes through `KernelSessionManager` → `LabLocalExec`, which
runs `bin/simple run <accumulated-cell-source>.spl` as a real subprocess per
cell (see `src/app/simple_lab/lab_executor.spl`) — cell *N*'s subprocess
re-runs the concatenated source of cells 1..N, so per-cell cost grows with
history length, not just cell count.

| Metric | Value |
|---|---|
| Cells executed | 100 |
| OK (`"ok":true`) | 100 / 100 |
| Min per-cell latency | 56,331 µs (56.3 ms) |
| Max per-cell latency | 80,640 µs (80.6 ms) |
| Avg per-cell latency | 62,268 µs (62.3 ms) |
| Session count after soak | 1 (`GET /api/lab/status` confirmed) |

Per-cell cost stayed flat (~56–81 ms) across the whole run rather than
growing noticeably with accumulated history — the underlying `bin/simple run`
cold-start dominates over the cost of re-interpreting up to 100 trivial
`print(...)` lines. Total soak wall time: ~6.2 s of actual execution (not
counting the one-time ~150s-budgeted server subprocess boot, which is fixed
overhead paid once per `it` example, not per cell).

### 3. Fuzz-lite corpus

Each fuzz case is its own spec example (kept separate rather than one
aggregate pass/fail, so a genuinely-failing assertion — see 3b — stays
individually visible instead of being averaged away):

**3a. Malformed JSON bodies (6-item corpus) → PASS, 6/6 got 4xx**

`"not json at all"`, `"{{{{"`, `"{\"default_mode\":}"`, `"[1,2,"`,
`" binary-garbage"`, and a JSON object missing its closing brace, all POSTed
to `/api/lab/sessions`. All 6 answered a 4xx (this exercises the same
`lab_json_body_is_valid` gate H1's spec already covers; re-run here as part
of the combined evidence pass). Server answered correctly immediately after.

**3b. Oversized single header line (20,000 bytes) → FAIL on the strict 4xx
expectation; PASS on the hard "no panic" gate. KNOWN GAP, filed.**

```
fuzz_oversized_header status=200 ok=true
```

Design §8.5 says oversized headers "must produce 4xx." What actually happens:
the request is accepted with a normal `200`. Root-caused to a **runtime**
(not `.spl`) primitive: `read_line_chunked`
(`src/compiler_rust/runtime/src/value/net_tcp.rs:544`, backing
`TcpStream.read_line()`) silently truncates any line at exactly 8192 bytes
without a trailing newline and without an error — the same boundary
`parser.spl`'s own `hl.len() > max_header_line` check is trying to catch — so
that check can never fire for a line the runtime already cut at that exact
boundary. The oversized header's tail is then read as a colon-less "header"
on the next line and silently dropped, not rejected. **Not a crash**: the
server stayed alive and correct for the very next request in the same
example. Filed:
`doc/08_tracking/bug/lab_http_parser_oversized_header_line_silently_truncated_not_rejected_2026-08-07.md`.
Fixing it means touching the Rust runtime primitive, which is out of scope
for this pure-Simple evidence task — left as a filed, RED assertion rather
than silently loosened or removed.

**3c. Too-many-headers (110 headers, over the 100-header cap) → PASS, got 4xx**

```
fuzz_too_many_headers status=400 ok=true
```

Confirms the header-*count* guard (`> max_header_count`, distinct code path
from the per-line-length guard above) works correctly — it operates on a
running counter across well-formed short lines and is unaffected by the
chunked reader's per-line truncation bug.

**3d. WebSocket handshake truncated mid-write → PASS, survived**

```
fuzz_truncated_ws_handshake survived=true
```

A client that writes a partial WS upgrade request (request line + one
header, no terminating blank line) and closes the connection immediately —
simulating a client dying mid-handshake — does not hang or crash the server;
the very next request on a fresh connection is answered correctly.

## Verify checklist (against the plan's H3 verify line)

| Requirement | Status |
|---|---|
| Load smoke on `/api/lab/status`, bounded | Done — 200 requests, 200/200 OK, evidence above |
| 100-cell execute soak on the local lane | Done — 100 cells, 100/100 OK, evidence above |
| Fuzz-lite: malformed JSON bodies | Done — 6/6 4xx |
| Fuzz-lite: oversized headers | Attempted; found + filed a genuine non-crashing gap (§3b) |
| Fuzz-lite: truncated WS frames | Done (as a truncated handshake, the reachable truncation surface — see spec docstring) — survives |
| No parallel QEMU/bootstrap | Satisfied — this work never touches QEMU/bootstrap |
| Loopback only | Satisfied — every request is `127.0.0.1` |
| Recorded limits | Satisfied — `MAX_HEADER_LINE=8192`/`MAX_HEADER_COUNT=100` (library defaults) recorded above; per-`it` `max_requests` budgets are visible in the spec source |
| Report checked into `doc/09_report/` with commands + numbers | This file |
| Zero panics | **Satisfied** — zero process crashes or hangs across all 6 examples (the one bug that *did* crash the process, `read_bytes`, was found and fixed before this evidence run, not left as a panic) |

## Plan-path corrections

- Design §8.5 mentions `wrk`-based load smoke; this repo has no `wrk`
  integration, so the load smoke is a real sequential `TcpStream` client
  loop instead (same driver pattern as every other Lab system spec in this
  suite). Recorded here rather than silently substituted without comment.
- Design §8.5 says "truncated WS frames"; `lab_server.spl`'s WS support is
  server-push-only (it never reads frames from the client after the upgrade —
  see its docstring), so there is no in-protocol "WS frame" for a client to
  truncate. The reachable truncation surface is the WS **handshake request**
  itself (a client dying mid-upgrade), which is what 3d exercises.
