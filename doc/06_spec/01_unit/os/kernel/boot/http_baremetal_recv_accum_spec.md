# Http Baremetal Recv Accum Specification

> Tests covering http_recv_accum_feed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Http Baremetal Recv Accum Specification

## Scenarios

### http_recv_accum_feed

#### is incomplete until the full request line + headers + blank line arrive

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is incomplete until the full request line + headers + blank line arrive
   - Expected: state.complete is false
   - Expected: state.complete is false
   - Expected: state.complete is true
   - Expected: state.error equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is incomplete until the full request line + headers + blank line arrive")
var state = http_recv_accum_new()
expect(state.complete).to_equal(false)
state = http_recv_accum_feed(state, "GET /x HTTP/1.1\r\n", 65536)
expect(state.complete).to_equal(false)
state = http_recv_accum_feed(state, "Host: a\r\n\r\n", 65536)
expect(state.complete).to_equal(true)
expect(state.error).to_equal("")
```

</details>

#### completes a bodyless GET request split across many small chunks

- completes a bodyless GET request split across many small chunks
   - Expected: state.complete is false
   - Expected: state.complete is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("completes a bodyless GET request split across many small chunks")
var state = http_recv_accum_new()
state = http_recv_accum_feed(state, "G", 65536)
state = http_recv_accum_feed(state, "ET /x HTTP", 65536)
state = http_recv_accum_feed(state, "/1.1\r\n", 65536)
expect(state.complete).to_equal(false)
state = http_recv_accum_feed(state, "Hos", 65536)
state = http_recv_accum_feed(state, "t: a\r", 65536)
state = http_recv_accum_feed(state, "\n\r\n", 65536)
expect(state.complete).to_equal(true)
```

</details>

#### waits for the full body once Content-Length is known

- waits for the full body once Content-Length is known
   - Expected: state.complete is false
   - Expected: state.complete is false
   - Expected: state.complete is true
   - Expected: state.buffer.ends_with("helloworld") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("waits for the full body once Content-Length is known")
var state = http_recv_accum_new()
state = http_recv_accum_feed(state, "POST /x HTTP/1.1\r\nContent-Length: 10\r\n\r\n", 65536)
expect(state.complete).to_equal(false)
state = http_recv_accum_feed(state, "hello", 65536)
expect(state.complete).to_equal(false)
state = http_recv_accum_feed(state, "world", 65536)
expect(state.complete).to_equal(true)
expect(state.buffer.ends_with("helloworld")).to_equal(true)
```

</details>

#### rejects oversize input via .error instead of growing without bound

- rejects oversize input via .error instead of growing without bound
   - Expected: state.error equals `request too large`
   - Expected: state.complete is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects oversize input via .error instead of growing without bound")
var state = http_recv_accum_new()
state = http_recv_accum_feed(state, "GET /this/path/is/long/enough HTTP/1.1\r\n", 10)
expect(state.error).to_equal("request too large")
expect(state.complete).to_equal(false)
```

</details>

#### does not keep re-feeding a completed or errored state (idempotent)

- does not keep re-feeding a completed or errored state (idempotent)
   - Expected: state.complete is true
   - Expected: state.buffer equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not keep re-feeding a completed or errored state (idempotent)")
var state = http_recv_accum_new()
state = http_recv_accum_feed(state, "GET /x HTTP/1.1\r\n\r\n", 65536)
expect(state.complete).to_equal(true)
val before = state.buffer
state = http_recv_accum_feed(state, "more data that should be ignored", 65536)
expect(state.buffer).to_equal(before)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/boot/http_baremetal_recv_accum_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering http_recv_accum_feed.
- http_recv_accum_feed

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `c126d11f8013d3c12eaa5b27da78ab239ad9161bb9e298a6ae7e68fa14d432f6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c126d11f8013d3c12eaa5b27da78ab239ad9161bb9e298a6ae7e68fa14d432f6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c126d11f8013d3c12eaa5b27da78ab239ad9161bb9e298a6ae7e68fa14d432f6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/kernel/boot/http_baremetal_recv_accum_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/boot/http_baremetal_recv_accum_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/boot/http_baremetal_recv_accum_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/boot/http_baremetal_recv_accum_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/boot/http_baremetal_recv_accum_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is incomplete until the full request line + headers + blank line arrive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/boot/http_baremetal_recv_accum_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'completes a bodyless GET request split across many small chunks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/boot/http_baremetal_recv_accum_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'waits for the full body once Content-Length is known' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
