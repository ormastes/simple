# Security Headers Specification

> Tests covering SecurityHeaders middleware, security header value building, security header toggles.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Security Headers Specification

## Scenarios

### SecurityHeaders middleware

#### adds CSP header by default

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- adds CSP header by default
   - Expected: config.enable_csp is true
   - Expected: header_value(headers, "Content-Security-Policy") equals `config.csp_value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds CSP header by default")
val config = SecurityHeadersConfig.default()
expect(config.enable_csp).to_equal(true)
val headers = collect_security_headers(config)
expect(header_value(headers, "Content-Security-Policy")).to_equal(config.csp_value)
```

</details>

#### adds X-Content-Type-Options header

- adds X-Content-Type-Options header
   - Expected: config.enable_content_type_options is true
   - Expected: header_value(headers, "X-Content-Type-Options") equals `nosniff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds X-Content-Type-Options header")
val config = SecurityHeadersConfig.default()
expect(config.enable_content_type_options).to_equal(true)
val headers = collect_security_headers(config)
expect(header_value(headers, "X-Content-Type-Options")).to_equal("nosniff")
```

</details>

#### adds X-Frame-Options header

- adds X-Frame-Options header
   - Expected: config.enable_frame_options is true
   - Expected: header_value(headers, "X-Frame-Options") equals `DENY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds X-Frame-Options header")
val config = SecurityHeadersConfig.default()
expect(config.enable_frame_options).to_equal(true)
val headers = collect_security_headers(config)
expect(header_value(headers, "X-Frame-Options")).to_equal("DENY")
```

</details>

#### default CSP contains self

- default CSP contains self


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default CSP contains self")
val config = SecurityHeadersConfig.default()
expect(config.csp_value).to_contain("default-src 'self'")
```

</details>

### security header value building

#### builds nosniff header value

- builds nosniff header value
   - Expected: header_value(headers, "X-Content-Type-Options") equals `nosniff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds nosniff header value")
val headers = collect_security_headers(SecurityHeadersConfig.default())
expect(header_value(headers, "X-Content-Type-Options")).to_equal("nosniff")
```

</details>

#### builds DENY frame option value

- builds DENY frame option value
   - Expected: SecurityHeadersConfig.default().frame_options_value equals `DENY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds DENY frame option value")
expect(SecurityHeadersConfig.default().frame_options_value).to_equal("DENY")
```

</details>

#### builds HSTS header value

- builds HSTS header value
   - Expected: header_value(headers, "Strict-Transport-Security") equals `hsts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds HSTS header value")
val config = SecurityHeadersConfig.default()
val hsts = build_hsts_value(config.hsts_max_age, config.hsts_include_subdomains)
expect(hsts).to_contain("max-age=")
val headers = collect_security_headers(config)
expect(header_value(headers, "Strict-Transport-Security")).to_equal(hsts)
```

</details>

### security header toggles

#### omits disabled headers from the emitted set

- omits disabled headers from the emitted set
   - Expected: header_value(headers, "X-Frame-Options") equals ``
   - Expected: header_value(headers, "Strict-Transport-Security") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("omits disabled headers from the emitted set")
val relaxed = SecurityHeadersConfig.relaxed()
val headers = collect_security_headers(relaxed)
expect(header_value(headers, "X-Frame-Options")).to_equal("")
expect(header_value(headers, "Strict-Transport-Security")).to_equal("")
```

</details>

#### appends security headers to existing response headers

- appends security headers to existing response headers
   - Expected: header_value(final_headers, "Content-Type") equals `text/html`
   - Expected: header_value(final_headers, "X-Content-Type-Options") equals `nosniff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends security headers to existing response headers")
val existing: [(text, text)] = [("Content-Type", "text/html")]
val final_headers = apply_security_headers(existing, SecurityHeadersConfig.default())
expect(header_value(final_headers, "Content-Type")).to_equal("text/html")
expect(header_value(final_headers, "X-Content-Type-Options")).to_equal("nosniff")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/http_server/security_headers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SecurityHeaders middleware, security header value building, security header toggles.
- SecurityHeaders middleware
- security header value building
- security header toggles

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `37a5510566a14582937ce1f4142c5f9cb4e5ec9c8c59cd00485642aafcb24cb8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `37a5510566a14582937ce1f4142c5f9cb4e5ec9c8c59cd00485642aafcb24cb8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `37a5510566a14582937ce1f4142c5f9cb4e5ec9c8c59cd00485642aafcb24cb8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/http_server/security_headers_spec.spl
mirror: doc/06_spec/unit/lib/http_server/security_headers_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/http_server/security_headers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/http_server/security_headers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/http_server/security_headers_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds CSP header by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/http_server/security_headers_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds X-Content-Type-Options header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/http_server/security_headers_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds X-Frame-Options header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
