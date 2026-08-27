# Net Http Sendfile Routing Specification

> Tests covering FR-NET-0003 HTTP static-file capability routing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Http Sendfile Routing Specification

## Scenarios

### FR-NET-0003 HTTP static-file capability routing

#### worker startup capability model

#### summarizes portable backend capabilities for worker records

- summarizes portable backend capabilities for worker records
   - Expected: net_backend_summary(caps) equals `portable-socket:portable`
   - Expected: net_backend_can_accelerate_static_files(caps) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("summarizes portable backend capabilities for worker records")
val caps = portable_net_backend_capabilities()
expect(net_backend_summary(caps)).to_equal("portable-socket:portable")
expect(net_backend_can_accelerate_static_files(caps)).to_equal(false)
```

</details>

#### summarizes sendfile-capable backends as static-file accelerators

- summarizes sendfile-capable backends as static-file accelerators
   - Expected: net_backend_summary(caps) equals `sendfile-test:sendfile`
   - Expected: net_backend_can_accelerate_static_files(caps) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("summarizes sendfile-capable backends as static-file accelerators")
val caps = net_backend_capabilities("sendfile-test", true, true, true, false)
expect(net_backend_summary(caps)).to_equal("sendfile-test:sendfile")
expect(net_backend_can_accelerate_static_files(caps)).to_equal(true)
```

</details>

#### static file route selection

#### keeps ordinary response bodies on the portable body path

- keeps ordinary response bodies on the portable body path
   - Expected: net_backend_static_file_route(caps, false) equals `body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps ordinary response bodies on the portable body path")
val caps = net_backend_capabilities("sendfile-test", true, true, true, false)
expect(net_backend_static_file_route(caps, false)).to_equal("body")
```

</details>

#### uses portable read plus send when sendfile is unavailable

- uses portable read plus send when sendfile is unavailable
   - Expected: net_backend_static_file_route(caps, true) equals `portable-read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses portable read plus send when sendfile is unavailable")
val caps = portable_net_backend_capabilities()
expect(net_backend_static_file_route(caps, true)).to_equal("portable-read")
```

</details>

#### uses sendfile only when the backend explicitly supports sendfile

- uses sendfile only when the backend explicitly supports sendfile
   - Expected: net_backend_static_file_route(caps, true) equals `sendfile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses sendfile only when the backend explicitly supports sendfile")
val caps = net_backend_capabilities("sendfile-test", true, true, true, false)
expect(net_backend_static_file_route(caps, true)).to_equal("sendfile")
```

</details>

#### does not treat zero-copy-only as a file-to-socket sendfile path

- does not treat zero-copy-only as a file-to-socket sendfile path
   - Expected: net_backend_can_accelerate_static_files(caps) is true
   - Expected: net_backend_static_file_route(caps, true) equals `portable-read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not treat zero-copy-only as a file-to-socket sendfile path")
val caps = net_backend_capabilities("zero-copy-only", true, true, false, true)
expect(net_backend_can_accelerate_static_files(caps)).to_equal(true)
expect(net_backend_static_file_route(caps, true)).to_equal("portable-read")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/net_http_sendfile_routing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FR-NET-0003 HTTP static-file capability routing.
- FR-NET-0003 HTTP static-file capability routing

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0c2a67b754e98c195eb68e7a2c199c637a5e9c227e501281baa638757f2c83b8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0c2a67b754e98c195eb68e7a2c199c637a5e9c227e501281baa638757f2c83b8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0c2a67b754e98c195eb68e7a2c199c637a5e9c227e501281baa638757f2c83b8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/net_http_sendfile_routing_spec.spl
mirror: doc/06_spec/03_system/os/net_http_sendfile_routing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/net_http_sendfile_routing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/net_http_sendfile_routing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/net_http_sendfile_routing_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'summarizes portable backend capabilities for worker records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_http_sendfile_routing_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'summarizes sendfile-capable backends as static-file accelerators' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_http_sendfile_routing_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps ordinary response bodies on the portable body path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
