# Notebook Lanes — Simple Lab Robustness Evidence (H3)

**Date:** 2026-08-07
**Plan:** `doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md` (Stream H, task H3)
**Design:** `doc/05_design/app/tools/notebook_lanes_architecture.md` §8.5
**Spec:** `test/03_system/tools/simple_lab/lab_robustness_spec.spl`
**Command:** `bin/simple test test/03_system/tools/simple_lab/lab_robustness_spec.spl`

All three examples drive `src/app/simple_lab/lab_server.spl` as a real,
separate OS process over a real TCP socket on `127.0.0.1` — no mocks, no
in-process shim. Same pattern as L3's (`lab_http_api_spec.spl`) and H1's
(`lab_hardening_spec.spl`) real-loopback specs.

## 1. Load smoke — PASS

200 sequential, authenticated (`Authorization: Bearer <token>`)
`GET /api/lab/status` requests against one live server.

```
requests=200  ok=200  min_us=4730  max_us=8969  avg_us=5242
```

All 200 requests returned `200`. Max single-request latency 8.97ms — well
under the 5s no-pathological-stall ceiling the spec asserts. Server answered
correctly immediately after the run.

## 2. 100-cell soak — PASS

One real session (`POST /api/lab/sessions`), then 100 sequential real cell
executions through the actual functional route
(`POST /api/lab/sessions/:id/cells/:cid/execute`) — not the generic
`/api/test/click` layer, which has a known, separately-filed gap
(`doc/08_tracking/bug/lab_test_api_click_does_not_invoke_simple_lab_app_add_cell_2026-08-07.md`).

```
cells=100  ok=100  min_us=49937  max_us=116856  avg_us=70326
```

All 100 cell executions returned `200` with `"ok":true`. Per-cell latency
(50–117ms, avg 70ms) reflects real subprocess-backed cell execution, not a
mock. Server correctly reported `"session_count":1` after the soak and
remained responsive.

## 3. Fuzz-lite corpus — 8/9 PASS, 1 real gap found

Nine adversarial inputs against the live server, each expected to produce a
`4xx` response or a clean connection close, never a panic/hang:

| Case | Result |
|---|---|
| Malformed JSON body: `not json at all` | 4xx ✅ |
| Malformed JSON body: `{{{{` | 4xx ✅ |
| Malformed JSON body: `{"default_mode":}` | 4xx ✅ |
| Malformed JSON body: `[1,2,` | 4xx ✅ |
| Malformed JSON body: ` binary-garbage` | 4xx ✅ |
| Malformed JSON body: missing closing brace | 4xx ✅ |
| Too-many-headers (110 headers, over a 100-header cap) | 4xx ✅ |
| Truncated WebSocket handshake (connection closed mid-write, no terminating CRLFCRLF) | clean close, server survived ✅ |
| Oversized single header line (20,000 bytes, over an intended 8,192-byte cap) | **200 — accepted, not rejected** ❌ |

**Zero panics or crashes across all nine cases.** The one failure is a bounds
policy gap, not a stability issue: the server processed the oversized-header
request normally rather than rejecting it. Filed:
`doc/08_tracking/bug/lab_hardening_missing_oversized_header_cap_2026-08-07.md`.
Left the assertion RED in the spec rather than weakened, per
`.claude/rules/testing.md`.

## Summary

| Example | Verdict |
|---|---|
| Load smoke | PASS |
| 100-cell soak | PASS |
| Fuzz-lite corpus | 8/9 PASS — one real, filed gap (oversized-header cap not enforced) |

Zero panics observed across 200 status requests, 100 real cell executions,
and 9 adversarial fuzz-lite inputs. The one open item does not affect
stability — it's a missed size-cap enforcement, tracked separately.
