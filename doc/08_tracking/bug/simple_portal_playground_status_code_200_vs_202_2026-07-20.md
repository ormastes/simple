# `simple_portal` server: authorized playground run returns `200 OK` instead of expected `202 Accepted`
**Status:** OPEN (2026-09-12, re-verified: bin/simple test test/02_integration/app/simple_portal/simple_portal_server_spec.spl -> 8 passed, 1 failed, still reproduces)

**Date:** 2026-07-20
**Component:** `src/app/simple_portal/*` server (`/api/playground/run` route)
**Severity:** Low — single example; 8 of 9 examples in the spec file pass
**Found by:** whole-suite triage campaign,
`test/02_integration/app/simple_portal/simple_portal_server_spec.spl`

## Symptom

```simple
it "accepts authorized playground runs and returns a sandbox envelope":
    val headers = "Origin: http://localhost:4040\nX-Simple-Portal-Capability: playground.run\nX-Simple-Portal-Token: dev-token\n"
    val resp = _server().route_request("POST", "/api/playground/run", "{\"mode\":\"sandbox\",\"source\":\"print 1\"}", headers)
    expect(resp).to_start_with("HTTP/1.1 202 Accepted")
    expect(resp).to_contain("\"runner\":\"simple run --sandbox\"")
    expect(resp).to_contain("\"sandbox\":{\"filesystem\":false,\"network\":false,\"process\":false}")
```

fails at the status-line check: actual response starts with `HTTP/1.1 200
OK`, not `202 Accepted`. Not confirmed whether the JSON body content
(`runner`, `sandbox` envelope fields) is otherwise correct, since the
example halts at the first failing assertion.

## Root-cause hypothesis

Not root-caused to the exact route handler in `src/app/simple_portal/`
(time-boxed triage). A `202 Accepted` status typically signals
async/queued processing (matching the "sandbox run" semantics implied by
the runner string), so this could be either the server having been
simplified to synchronous `200 OK` responses without updating the contract
test, or the status-code assignment being a genuine oversight in the
handler.

## Note

Spec left unmodified — `202` vs `200` for an async-flavored playground-run
endpoint is a real protocol-contract question, not an obvious rename;
flagged for the `simple_portal` owner to confirm the intended status code.

## Triage 2026-09-12
Rule B: ran `bin/simple test test/02_integration/app/simple_portal/simple_portal_server_spec.spl` on the deployed seed; 1 of 9 checks still fail, so this record still reproduces. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Re-check 2026-09-12

- Status: RESOLVED (2026-09-12) — spec `test/02_integration/app/simple_portal/simple_portal_server_spec.spl`
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple`, sha256 `3d120a6f9ab5`

Reproduced exactly as filed, then root-caused (the record left this open):
`SimplePortalServer._run_playground` (`src/app/simple_portal/server.spl:253`)
ended in `self._finalize(build_json(envelope), false, true)`, and
`build_json` is a thin wrapper over `build_ok(body, "application/json")`
(`src/lib/nogc_async_mut/http_server/response.spl:95,80`) which hardcodes
`status: 200, reason: "OK"`. There was no status-code assignment to get wrong —
the handler simply had no way to express anything but 200.

The spec's `202` is the correct side of the contract question this record
raised. The handler does not execute the submitted source: it bumps a run
sequence, writes `{data_root}/{audit_id}.json`, and returns an envelope whose
`runner` field names the command a future executor would invoke
(`simple run --sandbox`). That is a queued request with no result, which is
exactly what `202 Accepted` means; `200 OK` would claim the run had completed.
Fixed by constructing the response with `status: 202, reason: "Accepted"`
in the handler rather than adding a `build_accepted` helper to the shared
response module for this one call site.

```
RED   SPEC FILE VERDICT: ... outcome=ERROR declared>=9 executed=9 passed=8 failed=1 skipped=0 dropped=0
        ✗ accepts authorized playground runs and returns a sandbox envelope
          expected HTTP/1.1 200 OK ...
GREEN SPEC FILE VERDICT: ... outcome=OK    declared>=9 executed=9 passed=9 failed=0 skipped=0 dropped=0
```

Suite `test/02_integration/app/simple_portal/` after: content_db 5/5 OK,
server 9/9 OK. The legacy mirror
`test/integration/app/simple_portal/simple_portal_server_spec.spl` was NOT
edited (frozen tree) and still passes 8/8 — it has no status-line assertion on
this route, which is why the divergence is benign here.
