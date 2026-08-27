# Simple Web Browser WebSocket Handler Hardening Specification

> Verifies selected Feature C and NFR C WebSocket upgrade parsing, canonical route gating, bearer extraction, query-token non-authorization, and frame bounds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Browser WebSocket Handler Hardening Specification

Verifies selected Feature C and NFR C WebSocket upgrade parsing, canonical route gating, bearer extraction, query-token non-authorization, and frame bounds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/nfr/simple_web_browser_production_hardening.md |
| Source | `test/01_unit/app/ui/ws_handler_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies selected Feature C and NFR C WebSocket upgrade parsing, canonical
route gating, bearer extraction, query-token non-authorization, and frame bounds.

**Requirements:** doc/02_requirements/feature/simple_web_browser_production_hardening.md
**Requirements:** doc/02_requirements/nfr/simple_web_browser_production_hardening.md
**Traceability:** REQ-WEB-HARD-005, REQ-WEB-HARD-007, REQ-WEB-HARD-012, NFR-WEB-HARD-004, NFR-WEB-HARD-005, NFR-WEB-HARD-008, NFR-WEB-HARD-010

## Scenarios

### ui.web.ws_handler

#### recognizes websocket upgrade headers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-WEB-HARD-005
# @req REQ-WEB-HARD-007
# @req REQ-WEB-HARD-012
```

</details>

#### allows websocket upgrades only for GET

- allows websocket upgrades only for GET


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("allows websocket upgrades only for GET")
expect(ui_web_ws_upgrade_method_allowed("GET")).to_be(true)
expect(ui_web_ws_upgrade_method_allowed("POST")).to_be(false)
expect(ui_web_ws_upgrade_method_allowed("get")).to_be(false)
```

</details>

#### allows websocket upgrades only on the canonical ui route

- allows websocket upgrades only on the canonical ui route


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("allows websocket upgrades only on the canonical ui route")
expect(ui_web_ws_upgrade_path_allowed("/ui/ws")).to_be(true)
expect(ui_web_ws_upgrade_path_allowed("/ui/ws?client=wm")).to_be(true)
expect(ui_web_ws_upgrade_path_allowed("/ws")).to_be(false)
expect(ui_web_ws_upgrade_path_allowed("/api/state")).to_be(false)
```

</details>

#### extracts the websocket key from request headers

- extracts the websocket key from request headers
   - Expected: extract_ws_key(headers) equals `dGhlIHNhbXBsZSBub25jZQ==`
   - Expected: extract_ws_key(lowercase) equals `lowercase-key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts the websocket key from request headers")
val headers = "Host: localhost\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\n"
expect(extract_ws_key(headers)).to_equal("dGhlIHNhbXBsZSBub25jZQ==")
val lowercase = "Host: localhost\nsec-websocket-key: lowercase-key\n"
expect(extract_ws_key(lowercase)).to_equal("lowercase-key")
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
# @req REQ-SSPEC-APP
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
# @req REQ-SSPEC-APP
step("extracts bearer tokens from authorization headers")
val headers = "Authorization: Bearer secret-token\n"
expect(_extract_bearer(headers, "/ui/ws")).to_equal("secret-token")
```

</details>

#### rejects websocket query bearer tokens unless compatibility is enabled

- rejects websocket query bearer tokens unless compatibility is enabled
   - Expected: _extract_bearer("", path) equals ``
   - Expected: ui_web_extract_bearer_with_query_policy("", path, false) equals ``
   - Expected: ui_web_extract_bearer_with_query_policy("", path, true) equals `query-token`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects websocket query bearer tokens unless compatibility is enabled")
val path = "/ui/ws?token=query-token&client=wm"
expect(_extract_bearer("", path)).to_equal("")
expect(ui_web_extract_bearer_with_query_policy("", path, false)).to_equal("")
expect(ui_web_extract_bearer_with_query_policy("", path, true)).to_equal("query-token")
```

</details>

#### extracts and decodes compatibility query bearer tokens from any query position

- extracts and decodes compatibility query bearer tokens from any query position
   - Expected: ui_web_extract_bearer_with_query_policy("", path, true) equals `abc%2Edef%3Aghi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts and decodes compatibility query bearer tokens from any query position")
val path = "/ui/ws?client=wm&token=abc%252Edef%253Aghi"
expect(ui_web_extract_bearer_with_query_policy("", path, true)).to_equal("abc%2Edef%3Aghi")
```

</details>

#### extracts bearer tokens from websocket subprotocols before query fallback

- extracts bearer tokens from websocket subprotocols before query fallback
   - Expected: _extract_bearer(headers, path) equals `abc%2Edef%3Aghi`
   - Expected: ui_web_ws_response_protocol(headers) equals `simple-ui`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts bearer tokens from websocket subprotocols before query fallback")
val headers = "Sec-WebSocket-Protocol: simple-ui, bearer.abc%252Edef%253Aghi\n"
val path = "/ui/ws?token=query-token"
expect(_extract_bearer(headers, path)).to_equal("abc%2Edef%3Aghi")
expect(ui_web_ws_response_protocol(headers)).to_equal("simple-ui")
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
# @req REQ-SSPEC-APP
step("prefers authorization headers over query parameters")
val headers = "Authorization: Bearer header-token\n"
val path = "/ui/ws?token=query-token"
expect(_extract_bearer(headers, path)).to_equal("header-token")
```

</details>

#### keeps query bearer compatibility disabled from production env values

- keeps query bearer compatibility disabled from production env values


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps query bearer compatibility disabled from production env values")
expect(ui_web_query_token_allowed_from_env_value("")).to_be(false)
expect(ui_web_query_token_allowed_from_env_value("0")).to_be(false)
expect(ui_web_query_token_allowed_from_env_value("false")).to_be(false)
expect(ui_web_query_token_allowed_from_env_value("1")).to_be(false)
expect(ui_web_query_token_allowed_from_env_value("true")).to_be(false)
expect(ui_web_query_token_allowed_from_env_value(" yes ")).to_be(false)
```

</details>

#### bounds unauthenticated request body sizes before transport reads

- bounds unauthenticated request body sizes before transport reads
   - Expected: ui_web_content_length("Content-Length: 42\n") equals `42`
   - Expected: ui_web_content_length("content-length: 17\n") equals `17`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("bounds unauthenticated request body sizes before transport reads")
expect(ui_web_content_length("Content-Length: 42\n")).to_equal(42)
expect(ui_web_content_length("content-length: 17\n")).to_equal(17)
expect(ui_web_body_exceeds_unauth_limit("Content-Length: 8192\n")).to_be(false)
val too_large = UI_WEB_MAX_UNAUTH_BODY_BYTES + 1
expect(ui_web_body_exceeds_unauth_limit("Content-Length: {too_large}\n")).to_be(true)
```

</details>

#### bounds inbound websocket frame payload lengths before allocation

- bounds inbound websocket frame payload lengths before allocation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("bounds inbound websocket frame payload lengths before allocation")
expect(ui_web_ws_frame_payload_allowed(0)).to_be(true)
expect(ui_web_ws_frame_payload_allowed(UI_WEB_MAX_WS_FRAME_BYTES)).to_be(true)
expect(ui_web_ws_frame_payload_allowed(UI_WEB_MAX_WS_FRAME_BYTES + 1)).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/nfr/simple_web_browser_production_hardening.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-WEB-HARD-005`
- `REQ-WEB-HARD-007`
- `REQ-WEB-HARD-012`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7bd9194effeb8bb7b6185791bb3f4726497eaa426c7684da6c0a510f975c612e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7bd9194effeb8bb7b6185791bb3f4726497eaa426c7684da6c0a510f975c612e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7bd9194effeb8bb7b6185791bb3f4726497eaa426c7684da6c0a510f975c612e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/01_unit/app/ui/ws_handler_spec.spl
mirror: doc/06_spec/01_unit/app/ui/ws_handler_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ui/ws_handler_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/ws_handler_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/ws_handler_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/ui/ws_handler_spec.spl:33:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'recognizes websocket upgrade headers' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/ui/ws_handler_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows websocket upgrades only for GET' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/ws_handler_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows websocket upgrades only on the canonical ui route' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/ws_handler_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts the websocket key from request headers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
