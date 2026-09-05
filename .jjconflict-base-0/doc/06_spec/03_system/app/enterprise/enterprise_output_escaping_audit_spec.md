# Enterprise Web UI — output-escaping + security-header completeness audit (W14-A)

> Lane W14-A of `.spipe/simple_enterprise_suite` — a reproduce-first audit of EVERY place a route render function interpolates a request- or store-derived value into HTML. The audit (full list in `doc/07_guide/app/enterprise/security_posture.md`) found that the app is ALREADY hardened: every interpolation of attacker-influenceable data passes through `web_common.esc()`, and every response path (success, `deny()`, `command_page`, trailing 404, throttle/unauthorized) is wrapped by `secured()`/`with_default_security_headers`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Web UI — output-escaping + security-header completeness audit (W14-A)

Lane W14-A of `.spipe/simple_enterprise_suite` — a reproduce-first audit of EVERY place a route render function interpolates a request- or store-derived value into HTML. The audit (full list in `doc/07_guide/app/enterprise/security_posture.md`) found that the app is ALREADY hardened: every interpolation of attacker-influenceable data passes through `web_common.esc()`, and every response path (success, `deny()`, `command_page`, trailing 404, throttle/unauthorized) is wrapped by `secured()`/`with_default_security_headers`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md |
| Source | `test/03_system/app/enterprise/enterprise_output_escaping_audit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Lane W14-A of `.spipe/simple_enterprise_suite` — a reproduce-first audit of
EVERY place a route render function interpolates a request- or store-derived
value into HTML. The audit (full list in
`doc/07_guide/app/enterprise/security_posture.md`) found that the app is
ALREADY hardened: every interpolation of attacker-influenceable data passes
through `web_common.esc()`, and every response path (success, `deny()`,
`command_page`, trailing 404, throttle/unauthorized) is wrapped by
`secured()`/`with_default_security_headers`.

The prior fence (`store_web_harden_spec`) only covered the goods `/store/catalog`
view through the main dispatcher, in ELEMENT context. This spec closes two
gaps that were untested rather than unsafe:

1. **Attribute context.** The vertical views emit values inside double-quoted
   attributes (`data-resource="..."`, `data-line="..."`, `data-po="..."`,
   `data-account="..."`). An element-only escaper would let a `">`-prefixed
   payload break out of the attribute. `esc()` escapes `"`->`&quot;` and
   `'`->`&#39;` as well as `<`/`>`/`&`, so it is attribute-safe for quoted
   attributes — proven directly here.
2. **The vertical route families.** `booking_routes_handle` is exercised with a
   hostile store-derived `resource_id` to prove the render escapes it in both
   attribute and element position, and that both its success AND its
   `forbidden` denial response carry the shared security headers.

Each assertion is kept non-vacuous: the raw payload is asserted to genuinely
contain live markup first, so a regression that dropped `esc()` would flip the
negative assertions red.

## Troubleshooting

- A raw `<script>` or `"><` in output means a view interpolated data without
  `esc()` — fix the view (`src/app/enterprise_store_app/*_routes.spl`), never
  the spec.
- A missing header on a deny path means a `deny()`/error return escaped
  `secured()` — every return in a route family must wrap.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md

Lane: .spipe/simple_enterprise_suite (v2, W14-A output-escaping audit).

## Scenarios

### web_common.esc() is attribute-context safe, not just element-safe

#### neutralizes an attribute-breakout payload (double quote + tag)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- neutralizes an attribute-breakout payload (double quote + tag)
- The raw payload genuinely carries live markup (non-vacuous)
- esc() removes the live breakout


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("neutralizes an attribute-breakout payload (double quote + tag)")
val payload = "\"><img src=x onerror=alert(1)>"
step("The raw payload genuinely carries live markup (non-vacuous)")
expect(payload.contains("\"><img")).to_be(true)

step("esc() removes the live breakout")
val out = esc(payload)
expect(out.contains("\"><img")).to_be(false)
expect(out.contains("<img")).to_be(false)
expect(out.contains("&quot;&gt;&lt;img")).to_be(true)
```

</details>

#### neutralizes a bare attribute-value breakout (\

- neutralizes a bare attribute-value breakout (\


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("neutralizes a bare attribute-value breakout (\")
val payload = "\" onmouseover=alert(1) x=\""
expect(payload.contains("\"")).to_be(true)
val out = esc(payload)
expect(out.contains("\"")).to_be(false)
expect(out.contains("&quot; onmouseover=alert(1) x=&quot;")).to_be(true)
```

</details>

#### neutralizes a single-quoted attribute breakout (' onmouseover=)

- neutralizes a single-quoted attribute breakout (' onmouseover=)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("neutralizes a single-quoted attribute breakout (' onmouseover=)")
val payload = "' onmouseover='alert(1)"
expect(payload.contains("'")).to_be(true)
val out = esc(payload)
expect(out.contains("'")).to_be(false)
expect(out.contains("&#39; onmouseover=&#39;alert(1)")).to_be(true)
```

</details>

### booking resource view escapes a hostile store-derived resource_id

#### renders the id escaped in both attribute and element context

- renders the id escaped in both attribute and element context
- Seed a booking resource whose id is an XSS attempt
- Render GET /booking/resources and verify no live markup survives
   - Expected: http_status_code(resp.status) equals `200`
- The success response carries the shared security headers
   - Expected: header_value(resp, "X-Content-Type-Options") equals `nosniff`
   - Expected: header_value(resp, "X-Frame-Options") equals `DENY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders the id escaped in both attribute and element context")
val store = fresh_store("booking")
val t = tenant_a()
val admin = admin_a()
val sa = session_for(admin, t)
val hostile = "\"><script>alert(1)</script>"
step("Seed a booking resource whose id is an XSS attempt")
val add = booking_create_resource(store, sa, t, admin, hostile, "capacity-pool", 5, "v1")
expect(add.ok).to_be(true)

step("Render GET /booking/resources and verify no live markup survives")
val resp = booking_routes_handle(store, sa, t, admin, "GET", "/booking/resources", "")
expect(http_status_code(resp.status)).to_equal(200)
expect(resp.body.contains("<script>")).to_be(false)
expect(resp.body.contains("\"><script")).to_be(false)
expect(resp.body.contains("&lt;script&gt;")).to_be(true)
expect(resp.body.contains("&quot;&gt;")).to_be(true)

step("The success response carries the shared security headers")
expect(header_value(resp, "X-Content-Type-Options")).to_equal("nosniff")
expect(header_value(resp, "X-Frame-Options")).to_equal("DENY")
expect(header_value(resp, "Content-Security-Policy").contains("default-src 'self'")).to_be(true)
store_close(store)
```

</details>

### booking route denial path also carries the shared security headers

#### a forbidden read is 403 and still wrapped by secured()

- a forbidden read is 403 and still wrapped by secured()
- finance role lacks booking.hold -> GET /booking/resources denied
   - Expected: http_status_code(resp.status) equals `403`
   - Expected: header_value(resp, "X-Content-Type-Options") equals `nosniff`
   - Expected: header_value(resp, "X-Frame-Options") equals `DENY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a forbidden read is 403 and still wrapped by secured()")
val store = fresh_store("deny")
val t = tenant_a()
val fin = finance_a()
val fs = session_for(fin, t)
step("finance role lacks booking.hold -> GET /booking/resources denied")
val resp = booking_routes_handle(store, fs, t, fin, "GET", "/booking/resources", "")
expect(http_status_code(resp.status)).to_equal(403)
expect(header_value(resp, "X-Content-Type-Options")).to_equal("nosniff")
expect(header_value(resp, "X-Frame-Options")).to_equal("DENY")
store_close(store)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `9a2da57a9e76814e35e9569b0fa2b9ad71e342f4c74a757375ee6ea2e7f55f9e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9a2da57a9e76814e35e9569b0fa2b9ad71e342f4c74a757375ee6ea2e7f55f9e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9a2da57a9e76814e35e9569b0fa2b9ad71e342f4c74a757375ee6ea2e7f55f9e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/app/enterprise/enterprise_output_escaping_audit_spec.spl
mirror: doc/06_spec/03_system/app/enterprise/enterprise_output_escaping_audit_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/enterprise/enterprise_output_escaping_audit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/enterprise/enterprise_output_escaping_audit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/enterprise/enterprise_output_escaping_audit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/enterprise/enterprise_output_escaping_audit_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'neutralizes an attribute-breakout payload (double quote + tag)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/enterprise/enterprise_output_escaping_audit_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'neutralizes a bare attribute-value breakout (\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/enterprise/enterprise_output_escaping_audit_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'neutralizes a single-quoted attribute breakout (' onmouseover=)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
