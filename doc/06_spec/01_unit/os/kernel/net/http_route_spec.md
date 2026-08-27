# in-guest HTTP route classification + hardening (Lane C2)

> Proves the boot HTTP server's routing and request hardening in-process,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# in-guest HTTP route classification + hardening (Lane C2)

Proves the boot HTTP server's routing and request hardening in-process,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/net/http_route_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the boot HTTP server's routing and request hardening in-process,
without a socket or a mounted disk, by driving the pure classifier
(src/os/kernel/net/http_route.spl) that both boot transports
(src/os/kernel/boot/http_baremetal.spl and src/os/kernel/net/http_baremetal.spl)
sit on top of.

The classifier reuses the REAL Simple web server pipeline
(std.nogc_sync_mut.http_server): parse_request_line for the request line and
path_is_safe for the traversal check. These specs assert the three-route
decision (GET /, GET /health, and GET /files/<name>) plus fail-closed handling of
malformed, non-GET, unknown-route, nested, and path-traversal requests.

## Scenarios

### http route: happy paths

#### GET / classifies as Status

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- GET / classifies as Status


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GET / classifies as Status")
val route = http_classify_request("GET / HTTP/1.1\r\nHost: x\r\n\r\n")
match route.kind:
    HttpRouteKind.Status: expect(true).to_equal(true)
    _: expect("status").to_equal("other")
```

</details>

#### GET /health classifies as Health

- GET /health classifies as Health


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GET /health classifies as Health")
val route = http_classify_request("GET /health HTTP/1.1\r\nHost: x\r\n\r\n")
match route.kind:
    HttpRouteKind.Health: expect(true).to_equal(true)
    _: expect("health").to_equal("other")
```

</details>

#### GET /files/<name> classifies as File with a rooted path

- GET /files/<name> classifies as File with a rooted path


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GET /files/<name> classifies as File with a rooted path")
val route = http_classify_request("GET /files/VERSION.TXT HTTP/1.1\r\n\r\n")
match route.kind:
    HttpRouteKind.File: expect(route.file_path).to_equal("/VERSION.TXT")
    _: expect("file").to_equal("other")
```

</details>

### http route: fail-closed hardening

#### a malformed request line is BadRequest

- a malformed request line is BadRequest


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a malformed request line is BadRequest")
match _kind("GARBAGE\r\n\r\n"):
    HttpRouteKind.BadRequest: expect(true).to_equal(true)
    _: expect("badrequest").to_equal("other")
```

</details>

#### a request with no HTTP version is BadRequest

- a request with no HTTP version is BadRequest


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a request with no HTTP version is BadRequest")
match _kind("GET /\r\n\r\n"):
    HttpRouteKind.BadRequest: expect(true).to_equal(true)
    _: expect("badrequest").to_equal("other")
```

</details>

#### a non-GET method is NotFound

- a non-GET method is NotFound


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a non-GET method is NotFound")
match _kind("POST / HTTP/1.1\r\n\r\n"):
    HttpRouteKind.NotFound: expect(true).to_equal(true)
    _: expect("notfound").to_equal("other")
```

</details>

#### an unknown route is NotFound

- an unknown route is NotFound


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unknown route is NotFound")
match _kind("GET /nope HTTP/1.1\r\n\r\n"):
    HttpRouteKind.NotFound: expect(true).to_equal(true)
    _: expect("notfound").to_equal("other")
```

</details>

#### an empty /files/ name is NotFound

- an empty /files/ name is NotFound


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an empty /files/ name is NotFound")
match _kind("GET /files/ HTTP/1.1\r\n\r\n"):
    HttpRouteKind.NotFound: expect(true).to_equal(true)
    _: expect("notfound").to_equal("other")
```

</details>

#### a nested /files/ path (extra segment) is NotFound

- a nested /files/ path (extra segment) is NotFound


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a nested /files/ path (extra segment) is NotFound")
match _kind("GET /files/sub/file.txt HTTP/1.1\r\n\r\n"):
    HttpRouteKind.NotFound: expect(true).to_equal(true)
    _: expect("notfound").to_equal("other")
```

</details>

#### a dot-dot traversal under /files/ is NotFound

- a dot-dot traversal under /files/ is NotFound


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a dot-dot traversal under /files/ is NotFound")
match _kind("GET /files/../etc/passwd HTTP/1.1\r\n\r\n"):
    HttpRouteKind.NotFound: expect(true).to_equal(true)
    _: expect("notfound").to_equal("other")
```

</details>

#### an encoded dot-dot traversal under /files/ is NotFound

- an encoded dot-dot traversal under /files/ is NotFound


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an encoded dot-dot traversal under /files/ is NotFound")
match _kind("GET /files/..%2fpasswd HTTP/1.1\r\n\r\n"):
    HttpRouteKind.NotFound: expect(true).to_equal(true)
    _: expect("notfound").to_equal("other")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `e79b72e09b5d717ffc18b8440fc70b0f544a31b8b29448aef9b744ba0f65d278`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e79b72e09b5d717ffc18b8440fc70b0f544a31b8b29448aef9b744ba0f65d278`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e79b72e09b5d717ffc18b8440fc70b0f544a31b8b29448aef9b744ba0f65d278`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/kernel/net/http_route_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/net/http_route_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/net/http_route_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/net/http_route_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/net/http_route_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'GET / classifies as Status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/net/http_route_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'GET /health classifies as Health' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/net/http_route_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'GET /files/<name> classifies as File with a rooted path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
