# Http Dynamic Dispatch Live Socket Specification

> Tests covering sync http server — dynamic dispatch over a live loopback socket.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Http Dynamic Dispatch Live Socket Specification

## Scenarios

### sync http server — dynamic dispatch over a live loopback socket

#### runs the registered dynamic handler for a real TCP request

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs the registered dynamic handler for a real TCP request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs the registered dynamic handler for a real TCP request")
val wire = drive_one_request("GET /api/dyn HTTP/1.1\r\nHost: loopback\r\nConnection: close\r\n\r\n")
expect(wire).to_contain("HTTP/1.1 200")
expect(wire).to_contain(DYN_MARKER)
```

</details>

#### handler observes the transport-established security identity

- handler observes the transport-established security identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handler observes the transport-established security identity")
val wire = drive_one_request("GET /api/dyn HTTP/1.1\r\nHost: loopback\r\nConnection: close\r\n\r\n")
expect(wire).to_contain("addr=127.0.0.1")
```

</details>

#### live response carries the default security headers on the wire

- live response carries the default security headers on the wire


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("live response carries the default security headers on the wire")
val wire = drive_one_request("GET /api/dyn HTTP/1.1\r\nHost: loopback\r\nConnection: close\r\n\r\n")
expect(wire).to_contain("X-Content-Type-Options: nosniff")
expect(wire).to_contain("X-Frame-Options: DENY")
```

</details>

#### rejects an unsafe path before any dynamic handler over the wire

- rejects an unsafe path before any dynamic handler over the wire
   - Expected: wire does not contain `DYN_MARKER`
   - Expected: wire does not contain `200 OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects an unsafe path before any dynamic handler over the wire")
val wire = drive_one_request("GET /api/../secret HTTP/1.1\r\nHost: loopback\r\nConnection: close\r\n\r\n")
expect(wire.contains(DYN_MARKER)).to_equal(false)
expect(wire.contains("200 OK")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/web/server/http_dynamic_dispatch_live_socket_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sync http server — dynamic dispatch over a live loopback socket.
- sync http server — dynamic dispatch over a live loopback socket

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `22aaf32d965e22c9b1de6b4fdba2cf9f6bace637005464fb9f2d41b5626e3956`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `22aaf32d965e22c9b1de6b4fdba2cf9f6bace637005464fb9f2d41b5626e3956`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `22aaf32d965e22c9b1de6b4fdba2cf9f6bace637005464fb9f2d41b5626e3956`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/web/server/http_dynamic_dispatch_live_socket_spec.spl
mirror: doc/06_spec/03_system/web/server/http_dynamic_dispatch_live_socket_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/web/server/http_dynamic_dispatch_live_socket_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/web/server/http_dynamic_dispatch_live_socket_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/web/server/http_dynamic_dispatch_live_socket_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs the registered dynamic handler for a real TCP request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/web/server/http_dynamic_dispatch_live_socket_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handler observes the transport-established security identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/web/server/http_dynamic_dispatch_live_socket_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'live response carries the default security headers on the wire' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
