# Watcher Protocol Specification

> Tests covering WatcherProtocol, write_request, read_requests, request_path_for, cleanup.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Watcher Protocol Specification

## Scenarios

### WatcherProtocol

### write_request

#### creates request file in request directory

- creates request file in request directory
   - Expected: proto_exists(path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates request file in request directory")
proto_reset()
val path = mock_write_request("src/main.spl", "shb", ".build/watcher/requests")
expect(path).to_end_with(".req")
expect(proto_exists(path)).to_equal(true)
```

</details>

#### serializes source_path and kind

- serializes source_path and kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("serializes source_path and kind")
proto_reset()
val path = mock_write_request("src/lib/math.spl", "smf", ".build/watcher/requests")
val content = proto_read(path)
expect(content).to_contain("source_path=src/lib/math.spl")
expect(content).to_contain("kind=smf")
```

</details>

### read_requests

#### reads all request files

- reads all request files
   - Expected: requests.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads all request files")
proto_reset()
mock_write_request("src/a.spl", "shb", ".build/watcher/requests")
mock_write_request("src/b.spl", "smf", ".build/watcher/requests")
val requests = mock_read_requests(".build/watcher/requests")
expect(requests.len()).to_equal(2)
```

</details>

#### returns empty for no requests

- returns empty for no requests
   - Expected: requests.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns empty for no requests")
proto_reset()
val requests = mock_read_requests(".build/watcher/requests")
expect(requests.len()).to_equal(0)
```

</details>

#### parses source_path and kind correctly

- parses source_path and kind correctly
   - Expected: requests[0][0] equals `src/main.spl`
   - Expected: requests[0][1] equals `both`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses source_path and kind correctly")
proto_reset()
mock_write_request("src/main.spl", "both", ".build/watcher/requests")
val requests = mock_read_requests(".build/watcher/requests")
expect(requests[0][0]).to_equal("src/main.spl")
expect(requests[0][1]).to_equal("both")
```

</details>

### request_path_for

#### generates deterministic path

- generates deterministic path
   - Expected: path1 equals `path2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("generates deterministic path")
val path1 = make_req_path("src/main.spl", ".build/watcher/requests")
val path2 = make_req_path("src/main.spl", ".build/watcher/requests")
expect(path1).to_equal(path2)
```

</details>

#### generates different paths for different sources

- generates different paths for different sources
   - Expected: path1 != path2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("generates different paths for different sources")
val path1 = make_req_path("src/a.spl", ".build/watcher/requests")
val path2 = make_req_path("src/b.spl", ".build/watcher/requests")
expect(path1 != path2).to_equal(true)
```

</details>

### cleanup

#### deletes processed request files

- deletes processed request files
   - Expected: proto_exists(path) is true
   - Expected: proto_exists(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("deletes processed request files")
proto_reset()
val path = mock_write_request("src/main.spl", "shb", ".build/watcher/requests")
expect(proto_exists(path)).to_equal(true)
proto_delete(path)
expect(proto_exists(path)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/watcher/watcher_protocol_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WatcherProtocol, write_request, read_requests, request_path_for, cleanup.
- WatcherProtocol
- write_request
- read_requests
- request_path_for
- cleanup

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0eff163776c9b4a75a7ec7760a1fde52b295c384fb161561bf71b874cc9ec74a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0eff163776c9b4a75a7ec7760a1fde52b295c384fb161561bf71b874cc9ec74a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0eff163776c9b4a75a7ec7760a1fde52b295c384fb161561bf71b874cc9ec74a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/watcher/watcher_protocol_spec.spl
mirror: doc/06_spec/01_unit/compiler/watcher/watcher_protocol_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/watcher/watcher_protocol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/watcher/watcher_protocol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/watcher/watcher_protocol_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/watcher/watcher_protocol_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates request file in request directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/watcher/watcher_protocol_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serializes source_path and kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/watcher/watcher_protocol_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads all request files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
