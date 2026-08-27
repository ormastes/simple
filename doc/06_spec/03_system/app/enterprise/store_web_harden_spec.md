# Store Web UI Hardening — auth, escaping, headers on the hardened route path

> AC-15 of `.spipe/simple_enterprise_suite` (Goal Set v2): the store web UI is dispatched exclusively through the hardened path — `http_core` request limits (`body_decision`), traversal safety (`path_is_safe`), and the frozen authenticated-session guard (`session_valid`) — and every response carries the EXISTING shared security-header policy (`with_default_security_headers`), not a duplicate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Store Web UI Hardening — auth, escaping, headers on the hardened route path

AC-15 of `.spipe/simple_enterprise_suite` (Goal Set v2): the store web UI is dispatched exclusively through the hardened path — `http_core` request limits (`body_decision`), traversal safety (`path_is_safe`), and the frozen authenticated-session guard (`session_valid`) — and every response carries the EXISTING shared security-header policy (`with_default_security_headers`), not a duplicate.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md |
| Source | `test/03_system/app/enterprise/store_web_harden_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

AC-15 of `.spipe/simple_enterprise_suite` (Goal Set v2): the store web UI is
dispatched exclusively through the hardened path — `http_core` request
limits (`body_decision`), traversal safety (`path_is_safe`), and the frozen
authenticated-session guard (`session_valid`) — and every response carries
the EXISTING shared security-header policy
(`with_default_security_headers`), not a duplicate.

Proven here:
- an unauthenticated (inactive / mismatched) session is denied 401 on every
  route, including read-only catalog browsing;
- business data is HTML-escaped: a product named with a literal
  `<script>` tag renders with no raw `<script>` in the output;
- security headers (CSP, X-Content-Type-Options, X-Frame-Options) are
  present on both success and denial responses;
- `http_core` limit violations surface as HTTP statuses: duplicate Host
  header 400, oversized Content-Length 413, traversal path 400.

## Troubleshooting

- Missing security headers point at a response built outside `secured()` in
  `src/app/enterprise_store_app/main.spl` — every return must wrap.
- A raw `<script>` in output means some view interpolated business data
  without `esc()` — fix the view, never the spec.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md

Lane: .spipe/simple_enterprise_suite (v2, L-B, AC-15).

## Scenarios

### store web harden — unauthenticated requests are denied

#### denies an inactive session 401 before any route logic runs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- denies an inactive session 401 before any route logic runs
- Dispatch GET /store/catalog with an inactive session
   - Expected: http_status_code(resp.status) equals `401`
- A session bound to another tenant is also denied 401
   - Expected: http_status_code(resp2.status) equals `401`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("denies an inactive session 401 before any route logic runs")
val store = fresh_store("auth")
val t = tenant_a()
val admin = admin_a()
var dead = session_for(admin, t)
dead.active = false
step("Dispatch GET /store/catalog with an inactive session")
val resp = store_app_handle(store, dead, t, admin, "GET", "/store/catalog", plain_headers(), "")
expect(http_status_code(resp.status)).to_equal(401)

step("A session bound to another tenant is also denied 401")
val forged = SessionContext(token: "tok-x", actor_id: "admin-1", tenant_id: "tenant-b", active: true)
val resp2 = store_app_handle(store, forged, t, admin, "GET", "/store/catalog", plain_headers(), "")
expect(http_status_code(resp2.status)).to_equal(401)
store_close(store)
```

</details>

### store web harden — business data is HTML-escaped

#### renders a script-tag product name with no raw script element

- renders a script-tag product name with no raw script element
- Publish a product whose NAME is a script injection attempt
   - Expected: add.reason equals `accepted`
- Render the catalog and verify the payload arrives escaped
   - Expected: http_status_code(resp.status) equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders a script-tag product name with no raw script element")
val store = fresh_store("xss")
val t = tenant_a()
val admin = admin_a()
val sa = session_for(admin, t)
step("Publish a product whose NAME is a script injection attempt")
val hostile = "<script>alert('x')</script>"
val add = sale_add_product(store, sa, t, admin, "SKU-EVIL", hostile, Money(amount_cents: 100, currency: "USD"))
expect(add.reason).to_equal("accepted")

step("Render the catalog and verify the payload arrives escaped")
val resp = store_app_handle(store, sa, t, admin, "GET", "/store/catalog", plain_headers(), "")
expect(http_status_code(resp.status)).to_equal(200)
expect(resp.body.contains("<script>")).to_be(false)
expect(resp.body.contains("&lt;script&gt;")).to_be(true)
store_close(store)
```

</details>

### store web harden — shared security-header policy on every response

#### carries CSP, nosniff, and frame denial on success and on denial

- carries CSP, nosniff, and frame denial on success and on denial
- A successful catalog response carries the shared policy headers
   - Expected: header_value(ok, "X-Content-Type-Options") equals `nosniff`
   - Expected: header_value(ok, "X-Frame-Options") equals `DENY`
- A 401 denial carries the same policy headers
   - Expected: http_status_code(denied.status) equals `401`
   - Expected: header_value(denied, "X-Content-Type-Options") equals `nosniff`
   - Expected: header_value(denied, "X-Frame-Options") equals `DENY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("carries CSP, nosniff, and frame denial on success and on denial")
val store = fresh_store("headers")
val t = tenant_a()
val admin = admin_a()
val sa = session_for(admin, t)
step("A successful catalog response carries the shared policy headers")
val ok = store_app_handle(store, sa, t, admin, "GET", "/store/catalog", plain_headers(), "")
expect(header_value(ok, "Content-Security-Policy").contains("default-src 'self'")).to_be(true)
expect(header_value(ok, "X-Content-Type-Options")).to_equal("nosniff")
expect(header_value(ok, "X-Frame-Options")).to_equal("DENY")

step("A 401 denial carries the same policy headers")
var dead = session_for(admin, t)
dead.active = false
val denied = store_app_handle(store, dead, t, admin, "GET", "/store/catalog", plain_headers(), "")
expect(http_status_code(denied.status)).to_equal(401)
expect(header_value(denied, "X-Content-Type-Options")).to_equal("nosniff")
expect(header_value(denied, "X-Frame-Options")).to_equal("DENY")
store_close(store)
```

</details>

### store web harden — http_core limits and path safety gate dispatch

#### rejects smuggling-shaped and traversal-shaped requests

- rejects smuggling-shaped and traversal-shaped requests
- Duplicate Host header is rejected 400 (header smuggling)
   - Expected: http_status_code(r1.status) equals `400`
- Oversized Content-Length is rejected 413
   - Expected: http_status_code(r2.status) equals `400`
   - Expected: http_status_code(r3.status) equals `413`
- A traversal path is rejected 400 even when authenticated
   - Expected: http_status_code(r4.status) equals `400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects smuggling-shaped and traversal-shaped requests")
val store = fresh_store("limits")
val t = tenant_a()
val admin = admin_a()
val sa = session_for(admin, t)

step("Duplicate Host header is rejected 400 (header smuggling)")
val dup_host = [("Host", "a.example"), ("Host", "b.example")]
val r1 = store_app_handle(store, sa, t, admin, "GET", "/store/catalog", dup_host, "")
expect(http_status_code(r1.status)).to_equal(400)

step("Oversized Content-Length is rejected 413")
val huge = [("Host", "store.example"), ("Content-Length", "99999999999")]
val r2 = store_app_handle(store, sa, t, admin, "POST", "/store/order", huge, "")
expect(http_status_code(r2.status)).to_equal(400)
val big = [("Host", "store.example"), ("Content-Length", "20000000")]
val r3 = store_app_handle(store, sa, t, admin, "POST", "/store/order", big, "")
expect(http_status_code(r3.status)).to_equal(413)

step("A traversal path is rejected 400 even when authenticated")
val r4 = store_app_handle(store, sa, t, admin, "GET", "/store/../etc/passwd", plain_headers(), "")
expect(http_status_code(r4.status)).to_equal(400)
store_close(store)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `1a0932b919c57ace6e31678afc37456809509e59e4cdf91a0d08f312ebc04b0e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1a0932b919c57ace6e31678afc37456809509e59e4cdf91a0d08f312ebc04b0e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1a0932b919c57ace6e31678afc37456809509e59e4cdf91a0d08f312ebc04b0e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/enterprise/store_web_harden_spec.spl
mirror: doc/06_spec/03_system/app/enterprise/store_web_harden_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/enterprise/store_web_harden_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/enterprise/store_web_harden_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/enterprise/store_web_harden_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/enterprise/store_web_harden_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies an inactive session 401 before any route logic runs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/enterprise/store_web_harden_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a script-tag product name with no raw script element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/enterprise/store_web_harden_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries CSP, nosniff, and frame denial on success and on denial' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
