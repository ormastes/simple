# Ws Handler Specification

> Tests covering ui.web.ws_handler.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ws Handler Specification

## Scenarios

### ui.web.ws_handler

#### recognizes websocket upgrade headers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognizes websocket upgrade headers
   - Expected: is_ws_upgrade_request(headers) is true
   - Expected: is_ws_upgrade_request("Host: localhost\nConnection: keep-alive\n") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes websocket upgrade headers")
val headers = "Host: localhost\nUpgrade: websocket\nConnection: Upgrade\n"
expect(is_ws_upgrade_request(headers)).to_equal(true)
expect(is_ws_upgrade_request("Host: localhost\nConnection: keep-alive\n")).to_equal(false)
```

</details>

#### extracts the websocket key from request headers

- extracts the websocket key from request headers
   - Expected: extract_ws_key(headers) equals `dGhlIHNhbXBsZSBub25jZQ==`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts the websocket key from request headers")
val headers = "Host: localhost\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\n"
expect(extract_ws_key(headers)).to_equal("dGhlIHNhbXBsZSBub25jZQ==")
```

</details>

#### computes the RFC websocket accept hash

- computes the RFC websocket accept hash
   - Expected: compute_ws_accept("dGhlIHNhbXBsZSBub25jZQ==") equals `s3pPLMBiTxaQ9kYGzzhZRbK+xOo=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes the RFC websocket accept hash")
expect(compute_ws_accept("dGhlIHNhbXBsZSBub25jZQ==")).to_equal("s3pPLMBiTxaQ9kYGzzhZRbK+xOo=")
```

</details>

#### extracts bearer tokens from authorization headers

- extracts bearer tokens from authorization headers
   - Expected: _extract_bearer(headers, "/ui/ws") equals `secret-token`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts bearer tokens from authorization headers")
val headers = "Authorization: Bearer secret-token\n"
expect(_extract_bearer(headers, "/ui/ws")).to_equal("secret-token")
```

</details>

#### extracts bearer tokens from the websocket query string

- extracts bearer tokens from the websocket query string
   - Expected: _extract_bearer("", path) equals `query-token`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts bearer tokens from the websocket query string")
val path = "/ui/ws?token=query-token&client=wm"
expect(_extract_bearer("", path)).to_equal("query-token")
```

</details>

#### prefers authorization headers over query parameters

- prefers authorization headers over query parameters
   - Expected: _extract_bearer(headers, path) equals `header-token`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefers authorization headers over query parameters")
val headers = "Authorization: Bearer header-token\n"
val path = "/ui/ws?token=query-token"
expect(_extract_bearer(headers, path)).to_equal("header-token")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/ws_handler_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ui.web.ws_handler.
- ui.web.ws_handler

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `e461ad35139550b9d193e5c938eda81f5b0c7598359bb1cf8ab6989652b78262`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e461ad35139550b9d193e5c938eda81f5b0c7598359bb1cf8ab6989652b78262`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e461ad35139550b9d193e5c938eda81f5b0c7598359bb1cf8ab6989652b78262`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/ws_handler_spec.spl
mirror: doc/06_spec/unit/app/ui/ws_handler_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/ws_handler_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/ws_handler_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/ws_handler_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes websocket upgrade headers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/ws_handler_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts the websocket key from request headers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/ws_handler_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes the RFC websocket accept hash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
