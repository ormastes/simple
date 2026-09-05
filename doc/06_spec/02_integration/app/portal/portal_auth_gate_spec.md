# Portal Auth Gate Specification

> Tests covering portal auth gate (PORTAL_AUTH).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Portal Auth Gate Specification

## Scenarios

### portal auth gate (PORTAL_AUTH)

#### serves pages without a login when PORTAL_AUTH is off (default)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- serves pages without a login when PORTAL_AUTH is off (default)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("serves pages without a login when PORTAL_AUTH is off (default)")
val _ = rt_env_remove("PORTAL_AUTH")
val resp = _server().route_request("GET", "/", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
```

</details>

#### redirects to /login when PORTAL_AUTH=1 and there is no session cookie

- redirects to /login when PORTAL_AUTH=1 and there is no session cookie


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("redirects to /login when PORTAL_AUTH=1 and there is no session cookie")
val _ = rt_env_set("PORTAL_AUTH", "1")
val resp = _server().route_request("GET", "/", "", "")
expect(resp).to_start_with("HTTP/1.1 302 Found")
expect(resp).to_contain("Location: /login")
val _cleanup = rt_env_remove("PORTAL_AUTH")
```

</details>

#### still serves the /repos page as a redirect (not a 404) when gated

- still serves the /repos page as a redirect (not a 404) when gated


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("still serves the /repos page as a redirect (not a 404) when gated")
val _ = rt_env_set("PORTAL_AUTH", "1")
val resp = _server().route_request("GET", "/repos", "", "")
expect(resp).to_start_with("HTTP/1.1 302 Found")
expect(resp).to_contain("Location: /login")
val _cleanup = rt_env_remove("PORTAL_AUTH")
```

</details>

#### always serves the login page itself, even when gated

- always serves the login page itself, even when gated


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("always serves the login page itself, even when gated")
val _ = rt_env_set("PORTAL_AUTH", "1")
val resp = _server().route_request("GET", "/login", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("Log In")
val _cleanup = rt_env_remove("PORTAL_AUTH")
```

</details>

#### does not gate static assets

- does not gate static assets


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not gate static assets")
val _ = rt_env_set("PORTAL_AUTH", "1")
val resp = _server().route_request("GET", "/css/app.css", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
val _cleanup = rt_env_remove("PORTAL_AUTH")
```

</details>

#### grants access with a valid signed session cookie

- grants access with a valid signed session cookie


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("grants access with a valid signed session cookie")
val _ = rt_env_set("PORTAL_AUTH", "1")
val _ = rt_env_set("PORTAL_AUTH_SECRET", _SECRET)
val cookie_value = sign_session_cookie("admin", _SECRET)
val resp = _server().route_request("GET", "/", "", _cookie_header(cookie_value))
expect(resp).to_start_with("HTTP/1.1 200 OK")
val _c1 = rt_env_remove("PORTAL_AUTH")
val _c2 = rt_env_remove("PORTAL_AUTH_SECRET")
```

</details>

#### rejects a tampered session cookie and redirects to login

- rejects a tampered session cookie and redirects to login


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a tampered session cookie and redirects to login")
val _ = rt_env_set("PORTAL_AUTH", "1")
val _ = rt_env_set("PORTAL_AUTH_SECRET", _SECRET)
val cookie_value = sign_session_cookie("admin", _SECRET)
val forged = cookie_value + "0"
val resp = _server().route_request("GET", "/", "", _cookie_header(forged))
expect(resp).to_start_with("HTTP/1.1 302 Found")
expect(resp).to_contain("Location: /login")
val _c1 = rt_env_remove("PORTAL_AUTH")
val _c2 = rt_env_remove("PORTAL_AUTH_SECRET")
```

</details>

#### rejects a session cookie signed with a different secret

- rejects a session cookie signed with a different secret


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a session cookie signed with a different secret")
val _ = rt_env_set("PORTAL_AUTH", "1")
val _ = rt_env_set("PORTAL_AUTH_SECRET", _SECRET)
val cookie_value = sign_session_cookie("admin", "wrong-secret")
val resp = _server().route_request("GET", "/", "", _cookie_header(cookie_value))
expect(resp).to_start_with("HTTP/1.1 302 Found")
val _c1 = rt_env_remove("PORTAL_AUTH")
val _c2 = rt_env_remove("PORTAL_AUTH_SECRET")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/portal/portal_auth_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering portal auth gate (PORTAL_AUTH).
- portal auth gate (PORTAL_AUTH)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d1407e01dac5c3684eb749459af9d30d53abcfdc12c5dd2e8169fbad4604d9d1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d1407e01dac5c3684eb749459af9d30d53abcfdc12c5dd2e8169fbad4604d9d1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d1407e01dac5c3684eb749459af9d30d53abcfdc12c5dd2e8169fbad4604d9d1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/app/portal/portal_auth_gate_spec.spl
mirror: doc/06_spec/02_integration/app/portal/portal_auth_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/portal/portal_auth_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/portal/portal_auth_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/portal/portal_auth_gate_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serves pages without a login when PORTAL_AUTH is off (default)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/portal/portal_auth_gate_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'redirects to /login when PORTAL_AUTH=1 and there is no session cookie' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/portal/portal_auth_gate_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still serves the /repos page as a redirect (not a 404) when gated' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
