# `simple_portal` server: authorized playground run returns `200 OK` instead of expected `202 Accepted`

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
