# Worker Static File Specification

> Tests covering HTTP worker static-file routing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Worker Static File Specification

## Scenarios

### HTTP worker static-file routing

#### uses portable body sends for normal responses

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses portable body sends for normal responses
   - Expected: worker_static_file_route(caps, resp) equals `body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses portable body sends for normal responses")
val caps = portable_net_backend_capabilities()
val resp = build_ok("hello", "text/plain")

expect(worker_static_file_route(caps, resp)).to_equal("body")
```

</details>

#### falls back to portable reads when sendfile is unsupported

- falls back to portable reads when sendfile is unsupported
   - Expected: worker_static_file_route(caps, resp) equals `portable-read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to portable reads when sendfile is unsupported")
val caps = portable_net_backend_capabilities()
val resp = build_file_response("/tmp/large.bin", "application/octet-stream", 131072)

expect(worker_static_file_route(caps, resp)).to_equal("portable-read")
```

</details>

#### uses sendfile only when the backend reports support

- uses sendfile only when the backend reports support
   - Expected: worker_static_file_route(caps, resp) equals `sendfile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses sendfile only when the backend reports support")
val caps = net_backend_capabilities("sendfile-test", true, true, true, false)
val resp = build_file_response("/tmp/large.bin", "application/octet-stream", 131072)

expect(worker_static_file_route(caps, resp)).to_equal("sendfile")
```

</details>

#### does not route to sendfile for a zero-copy-only backend

- does not route to sendfile for a zero-copy-only backend
   - Expected: worker_static_file_route(caps, resp) equals `portable-read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not route to sendfile for a zero-copy-only backend")
val caps = net_backend_capabilities("zero-copy-only", true, true, false, true)
val resp = build_file_response("/tmp/large.bin", "application/octet-stream", 131072)

expect(worker_static_file_route(caps, resp)).to_equal("portable-read")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/http_server/worker_static_file_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HTTP worker static-file routing.
- HTTP worker static-file routing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `b8cb0e8b5164fd0e7123614ce11b01b14dff9bafe5b5318441cf168da1344cb0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b8cb0e8b5164fd0e7123614ce11b01b14dff9bafe5b5318441cf168da1344cb0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b8cb0e8b5164fd0e7123614ce11b01b14dff9bafe5b5318441cf168da1344cb0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/http_server/worker_static_file_spec.spl
mirror: doc/06_spec/01_unit/lib/http_server/worker_static_file_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/http_server/worker_static_file_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/http_server/worker_static_file_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/http_server/worker_static_file_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses portable body sends for normal responses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http_server/worker_static_file_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back to portable reads when sendfile is unsupported' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http_server/worker_static_file_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses sendfile only when the backend reports support' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
