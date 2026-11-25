# `simple_portal` server: authorized playground run returns `200 OK` instead of expected `202 Accepted`
## Resolved 2026-11-25 — fix already landed on release/1.0.0; resolution section restored

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

(2026-11-25: the "no resolution evidence" claim above was false — the
resolution section added by `04cae210bf4` had been silently dropped by the
`940bd30c832` ledger sweep. See "Resolution 2026-11-25" below.)

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

## Resolution 2026-11-25

**Status: RESOLVED — code fix already landed; this pass restores the
resolution record and re-verifies.**

### Contract evidence

1. The spec encoded `202 Accepted` from before the fix: the pre-fix spec
   (`git show 88aac2ffe28^:test/02_integration/app/simple_portal/simple_portal_server_spec.spl`)
   already asserted `expect(resp).to_start_with("HTTP/1.1 202 Accepted")`
   while all sibling examples asserted `200 OK` — `202` was a deliberate
   per-route contract, not a copy-paste slip.
2. The pre-fix handler (`SimplePortalServer._run_playground`,
   `src/app/simple_portal/server.spl`) ended in
   `self._finalize(build_json(envelope), false, true)`; `build_json` wraps
   `build_ok(body, "application/json")`, which hardcodes
   `status: 200, reason: "OK"` — the route had no way to express any other
   status, so `200` was a structural oversight, not a designed synchronous
   contract.
3. The response body already implements the sandbox-envelope contract the
   spec asserts (`"runner":"simple run --sandbox"`,
   `"sandbox":{"filesystem":false,"network":false,"process":false}`): the
   handler queues the run (writes `{data_root}/{audit_id}.json`, returns the
   envelope) and never executes the source — exactly `202 Accepted`
   semantics; `200 OK` would falsely claim completion.
4. No commit message or doc anywhere declares the endpoint deliberately
   synchronous; the only contract-decision record is the fix commit itself.

### Decision and fix

`202 Accepted` is the intended contract. The handler was fixed in
`04cae210bf4` (2026-09-12, "fix(app): return 202 Accepted from the portal
playground run route"): `_run_playground` now constructs the response with
`status: 202, reason: "Accepted"` directly instead of `build_json`. That
commit landed on main and reached `release/1.0.0` via the tree transplant
`88aac2ffe28`; the fixed handler is present at
`src/app/simple_portal/server.spl:265-282`. No code change was needed in
this pass.

### Before/after evidence

Before (historical, quoted from `04cae210bf4` and the original triage —
the failure no longer reproduces on this branch):

```
RED   SPEC FILE VERDICT: ... outcome=ERROR declared>=9 executed=9 passed=8 failed=1
        ✗ accepts authorized playground runs and returns a sandbox envelope
          expected HTTP/1.1 202 Accepted, got HTTP/1.1 200 OK
```

After (2026-11-25, this worktree, `bin/simple.exe` self-hosted):

```
$ SIMPLE_LIB=src bin/simple.exe test test/02_integration/app/simple_portal/simple_portal_server_spec.spl --mode=interpreter
SPEC FILE VERDICT: test/02_integration/app/simple_portal/simple_portal_server_spec.spl outcome=OK declared>=9 executed=9 passed=9 failed=0 skipped=0 blocked=0 dropped=0
Results: 9 total, 9 passed, 0 failed
```

All three assertions of the playground example pass: status line
`HTTP/1.1 202 Accepted`, `"runner":"simple run --sandbox"`, and the sandbox
envelope fields.

### Ledger note

The resolution section added by `04cae210bf4` (and annotated by
`7f6436ef9b9`) was silently dropped by the `940bd30c832` "sweep
fixed/stale bug ledger entries" commit, after which the `23648885149`
normalization pass re-headered this record as "Open — no resolution
evidence found in the body". This section restores the record; the ledger
sweep's handling of resolution sections may warrant a broader audit.

