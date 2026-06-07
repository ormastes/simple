# security_headers_spec

> Tests for SecurityHeaders middleware configuration and header value building. Validates default CSP, X-Content-Type-Options, and X-Frame-Options settings.

<!-- sdn-diagram:id=security_headers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=security_headers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

security_headers_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=security_headers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# security_headers_spec

Tests for SecurityHeaders middleware configuration and header value building. Validates default CSP, X-Content-Type-Options, and X-Frame-Options settings.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SEC-010 |
| Category | HTTP Server Security |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/http_server/security_headers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for SecurityHeaders middleware configuration and header value building.
Validates default CSP, X-Content-Type-Options, and X-Frame-Options settings.

## Scenarios

### SecurityHeaders middleware

#### adds CSP header by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_security_headers_config()
expect(config.enable_csp).to_equal(true)
```

</details>

#### adds X-Content-Type-Options header

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_security_headers_config()
expect(config.enable_nosniff).to_equal(true)
```

</details>

#### adds X-Frame-Options header

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_security_headers_config()
expect(config.enable_frame_deny).to_equal(true)
```

</details>

#### default CSP contains self

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_security_headers_config()
expect(config.csp_policy).to_contain("default-src 'self'")
```

</details>

### build_security_header_value

#### builds nosniff header value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = build_security_header_value("nosniff")
expect(value).to_equal("nosniff")
```

</details>

#### builds DENY frame option value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = build_security_header_value("frame-deny")
expect(value).to_equal("DENY")
```

</details>

#### builds HSTS header value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = build_security_header_value("hsts")
expect(value).to_contain("max-age=")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
