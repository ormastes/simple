# Test Api Mount Specification

> Tests covering test_api_mount.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Api Mount Specification

## Scenarios

### test_api_mount

#### exposes the canonical route prefix

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes the canonical route prefix
   - Expected: TEST_API_PREFIX equals `/api/test/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes the canonical route prefix")
expect(TEST_API_PREFIX).to_equal("/api/test/")
```

</details>

#### test_api_matches returns true only for /api/test/ paths

- test_api_matches returns true only for /api/test/ paths
   - Expected: test_api_matches("/api/test/ready") is true
   - Expected: test_api_matches("/api/test/ui/snapshot") is true
   - Expected: test_api_matches("/api/state") is false
   - Expected: test_api_matches("/") is false
   - Expected: test_api_matches("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test_api_matches returns true only for /api/test/ paths")
expect(test_api_matches("/api/test/ready")).to_equal(true)
expect(test_api_matches("/api/test/ui/snapshot")).to_equal(true)
expect(test_api_matches("/api/state")).to_equal(false)
expect(test_api_matches("/")).to_equal(false)
expect(test_api_matches("")).to_equal(false)
```

</details>

#### dispatch_test_api returns the ready probe against any session

- dispatch_test_api returns the ready probe against any session
   - Expected: result.0 equals `200`
   - Expected: result.1 equals `application/json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch_test_api returns the ready probe against any session")
val session = _trivial_session()
val result = dispatch_test_api(
    "/api/test/ready",
    "GET",
    "",
    session,
    \_: pass_dn
)
expect(result.0).to_equal(200)
expect(result.1).to_equal("application/json")
expect(result.2).to_contain("\"ready\":true")
expect(result.2).to_contain("\"protocol_version\":1")
```

</details>

#### dispatch_test_api surfaces a multi-mode UI snapshot

- dispatch_test_api surfaces a multi-mode UI snapshot
   - Expected: result.0 equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch_test_api surfaces a multi-mode UI snapshot")
val session = _trivial_session()
val result = dispatch_test_api(
    "/api/test/ui/snapshot",
    "GET",
    "",
    session,
    \_: pass_dn
)
expect(result.0).to_equal(200)
expect(result.2).to_contain("\"protocol_version\":1")
```

</details>

#### format_http_response emits a well-formed HTTP/1.1 response

- format_http_response emits a well-formed HTTP/1.1 response


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format_http_response emits a well-formed HTTP/1.1 response")
val response = format_http_response(200, "application/json", "{\"ok\":true}")
expect(response).to_start_with("HTTP/1.1 200 OK")
expect(response).to_contain("Content-Type: application/json")
expect(response).to_contain("X-UI-Protocol-Version: 1")
expect(response).to_contain("Content-Length: 11")
expect(response).to_end_with("{\"ok\":true}")
```

</details>

#### format_http_response maps known error statuses

- format_http_response maps known error statuses


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format_http_response maps known error statuses")
val not_found = format_http_response(404, "text/plain", "nope")
expect(not_found).to_start_with("HTTP/1.1 404 Not Found")
val bad = format_http_response(400, "application/json", "{}")
expect(bad).to_start_with("HTTP/1.1 400 Bad Request")
```

</details>

#### dispatch_and_format combines dispatch + encode in one call

- dispatch_and_format combines dispatch + encode in one call


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch_and_format combines dispatch + encode in one call")
val session = _trivial_session()
val encoded = dispatch_and_format(
    "/api/test/ready",
    "GET",
    "",
    session,
    \_: pass_dn
)
expect(encoded).to_start_with("HTTP/1.1 200 OK")
expect(encoded).to_contain("\"ready\":true")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/test_api_mount_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering test_api_mount.
- test_api_mount

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `732560e6f50ab8b93b1864998aebc8b7f3458ab4f4a937828663dc9a12bdec22`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `732560e6f50ab8b93b1864998aebc8b7f3458ab4f4a937828663dc9a12bdec22`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `732560e6f50ab8b93b1864998aebc8b7f3458ab4f4a937828663dc9a12bdec22`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/ui/test_api_mount_spec.spl
mirror: doc/06_spec/unit/app/ui/test_api_mount_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/test_api_mount_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/test_api_mount_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/test_api_mount_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/ui/test_api_mount_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes the canonical route prefix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/test_api_mount_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test_api_matches returns true only for /api/test/ paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/test_api_mount_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatch_test_api returns the ready probe against any session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
