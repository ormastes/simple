# Store Web Request-Gating — dispatcher CSRF + route-level write gate (W14-C)

> command's (`forbidden: 0`), so the `write-gate:` assertion FAILS (red);

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Store Web Request-Gating — dispatcher CSRF + route-level write gate (W14-C)

command's (`forbidden: 0`), so the `write-gate:` assertion FAILS (red);

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md |
| Source | `test/03_system/app/enterprise/store_web_request_gating_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Red-first evidence
- Item 1: before the gate, the `booking` -> close denial detail is the
  command's (`forbidden: 0`), so the `write-gate:` assertion FAILS (red);
  after, it PASSES with 403.
- Item 2: before the check, an admin cookie-borne close WITHOUT a token
  reaches the command and returns 200 (the forgery succeeds — red); after, it
  is 403 without a token and 200 with the session's token.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md

Lane: .spipe/simple_enterprise_suite (v2, W14-C).

## Scenarios

### request-gating — route-level write gate at the dispatcher (item 1)

#### denies an authenticated booking role at DISPATCH on POST /fin/period/close

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- denies an authenticated booking role at DISPATCH on POST /fin/period/close
- A booking-role session may authenticate but must not close a period
- Rejected 403 — and the denial detail proves it was the dispatcher gate, not the command
   - Expected: http_status_code(resp.status) equals `403`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("denies an authenticated booking role at DISPATCH on POST /fin/period/close")
val store = fresh_store("writegate")
val t = tenant_a()
val agent = booking_a()
val s = session_for(agent, t)
step("A booking-role session may authenticate but must not close a period")
val resp = store_app_handle(store, s, t, agent, "POST", "/fin/period/close", bearer_headers(), "end=1000&now=1001&idem=bk1")
step("Rejected 403 — and the denial detail proves it was the dispatcher gate, not the command")
expect(http_status_code(resp.status)).to_equal(403)
expect(resp.body.contains("write-gate:finance.period.close")).to_be(true)
store_close(store)
```

</details>

#### lets an authorized admin role through the write gate to the guarded command

- lets an authorized admin role through the write gate to the guarded command
- admin satisfies the same policy the command enforces -> passes the gate and closes
   - Expected: http_status_code(resp.status) equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lets an authorized admin role through the write gate to the guarded command")
val store = fresh_store("writegate_ok")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
step("admin satisfies the same policy the command enforces -> passes the gate and closes")
val resp = store_app_handle(store, s, t, admin, "POST", "/fin/period/close", bearer_headers(), "end=1000&now=1001&idem=ad1")
expect(http_status_code(resp.status)).to_equal(200)
expect(resp.body.contains("write-gate:")).to_be(false)
store_close(store)
```

</details>

### request-gating — CSRF double-submit for cookie-borne writes (item 2)

#### rejects a cookie-borne state-changing request that carries no CSRF token

- rejects a cookie-borne state-changing request that carries no CSRF token
- An admin who WOULD be authorized is still rejected 403 when the cookie flow lacks a CSRF token
   - Expected: http_status_code(resp.status) equals `403`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a cookie-borne state-changing request that carries no CSRF token")
val store = fresh_store("csrf_missing")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
step("An admin who WOULD be authorized is still rejected 403 when the cookie flow lacks a CSRF token")
val resp = store_app_handle(store, s, t, admin, "POST", "/fin/period/close", cookie_headers(""), "end=1000&now=1001&idem=cm1")
expect(http_status_code(resp.status)).to_equal(403)
expect(resp.body.contains("csrf")).to_be(true)
store_close(store)
```

</details>

#### rejects a cookie-borne request whose CSRF token does not match the session

- rejects a cookie-borne request whose CSRF token does not match the session
- A forged/stale token is not the session's token -> 403
   - Expected: http_status_code(resp.status) equals `403`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a cookie-borne request whose CSRF token does not match the session")
val store = fresh_store("csrf_wrong")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
step("A forged/stale token is not the session's token -> 403")
val resp = store_app_handle(store, s, t, admin, "POST", "/fin/period/close", cookie_headers("csrf.tok-someone-else"), "end=1000&now=1001&idem=cw1")
expect(http_status_code(resp.status)).to_equal(403)
store_close(store)
```

</details>

#### admits a cookie-borne request that echoes the session's own CSRF token

- admits a cookie-borne request that echoes the session's own CSRF token
- The session's double-submit token in X-CSRF-Token clears the gate and the close runs
   - Expected: http_status_code(resp.status) equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("admits a cookie-borne request that echoes the session's own CSRF token")
val store = fresh_store("csrf_ok")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
step("The session's double-submit token in X-CSRF-Token clears the gate and the close runs")
val resp = store_app_handle(store, s, t, admin, "POST", "/fin/period/close", cookie_headers(csrf_token(s)), "end=1000&now=1001&idem=co1")
expect(http_status_code(resp.status)).to_equal(200)
store_close(store)
```

</details>

#### leaves bearer-only writes (no cookie) exempt so API clients do not regress

- leaves bearer-only writes (no cookie) exempt so API clients do not regress
- No Cookie header -> no ambient credential -> CSRF not required
   - Expected: http_status_code(resp.status) equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves bearer-only writes (no cookie) exempt so API clients do not regress")
val store = fresh_store("csrf_bearer")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
step("No Cookie header -> no ambient credential -> CSRF not required")
val resp = store_app_handle(store, s, t, admin, "POST", "/fin/period/close", bearer_headers(), "end=1000&now=1001&idem=cb1")
expect(http_status_code(resp.status)).to_equal(200)
store_close(store)
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


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `080cc1a6fc5c1665368356707694e3fe30cb5740cd80d318d38a934c2e1ab5ee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `080cc1a6fc5c1665368356707694e3fe30cb5740cd80d318d38a934c2e1ab5ee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `080cc1a6fc5c1665368356707694e3fe30cb5740cd80d318d38a934c2e1ab5ee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/enterprise/store_web_request_gating_spec.spl
mirror: doc/06_spec/03_system/app/enterprise/store_web_request_gating_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/enterprise/store_web_request_gating_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/enterprise/store_web_request_gating_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/enterprise/store_web_request_gating_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/enterprise/store_web_request_gating_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies an authenticated booking role at DISPATCH on POST /fin/period/close' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/enterprise/store_web_request_gating_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lets an authorized admin role through the write gate to the guarded command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/enterprise/store_web_request_gating_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a cookie-borne state-changing request that carries no CSRF token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
