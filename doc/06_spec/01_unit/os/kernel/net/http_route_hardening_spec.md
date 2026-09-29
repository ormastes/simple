# in-guest HTTP route hardening — malformed / hostile requests (Lane HARDEN-ROBUST)

> Feeds the boot HTTP route classifier (src/os/kernel/net/http_route.spl)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# in-guest HTTP route hardening — malformed / hostile requests (Lane HARDEN-ROBUST)

Feeds the boot HTTP route classifier (src/os/kernel/net/http_route.spl)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/net/http_route_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Feeds the boot HTTP route classifier (src/os/kernel/net/http_route.spl)
malformed, oversized, injection, mixed-line-ending, percent-encoded and
method-confusion request lines and asserts every one FAILS CLOSED
(BadRequest / NotFound) — never a crash and never a partial File accept of a
hostile filename. Complements the happy-path coverage in
http_route_spec.spl.

Regression note: a `/files/` segment carrying a raw CR/LF or other control
byte now fails closed to NotFound, matching path_is_safe()'s NUL policy, so a
bare-LF-injected filename can no longer ride through as a "safe" segment.

## Scenarios

### http route hardening: method confusion

#### lowercase method is NotFound (case-sensitive GET)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lowercase method is NotFound (case-sensitive GET)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowercase method is NotFound (case-sensitive GET)")
assert_true(_is_notfound("get / HTTP/1.1\r\n\r\n"))
```

</details>

#### mixed-case method is NotFound

- mixed-case method is NotFound


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mixed-case method is NotFound")
assert_true(_is_notfound("GeT / HTTP/1.1\r\n\r\n"))
```

</details>

#### a leading space shifts the method and fails closed (BadRequest)

- a leading space shifts the method and fails closed (BadRequest)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a leading space shifts the method and fails closed (BadRequest)")
# split(' ') yields ["", "GET", "/"...]; method="" path="GET" version="/"
assert_true(_is_badrequest(" GET / HTTP/1.1\r\n\r\n"))
```

</details>

#### TRACE/CONNECT-style methods are NotFound

- TRACE/CONNECT-style methods are NotFound


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TRACE/CONNECT-style methods are NotFound")
assert_true(_is_notfound("TRACE / HTTP/1.1\r\n\r\n"))
assert_true(_is_notfound("CONNECT / HTTP/1.1\r\n\r\n"))
```

</details>

### http route hardening: version confusion

#### HTTP/2.0 is rejected (BadRequest)

- HTTP/2.0 is rejected (BadRequest)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("HTTP/2.0 is rejected (BadRequest)")
assert_true(_is_badrequest("GET / HTTP/2.0\r\n\r\n"))
```

</details>

#### HTTP/0.9 is rejected (BadRequest)

- HTTP/0.9 is rejected (BadRequest)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("HTTP/0.9 is rejected (BadRequest)")
assert_true(_is_badrequest("GET / HTTP/0.9\r\n\r\n"))
```

</details>

#### a missing version token is BadRequest

- a missing version token is BadRequest


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a missing version token is BadRequest")
assert_true(_is_badrequest("GET /\r\n\r\n"))
```

</details>

#### a bogus protocol token is BadRequest

- a bogus protocol token is BadRequest


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a bogus protocol token is BadRequest")
assert_true(_is_badrequest("GET / SPDY/3\r\n\r\n"))
```

</details>

### http route hardening: empty / truncated request lines

#### an empty request is BadRequest

- an empty request is BadRequest


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an empty request is BadRequest")
assert_true(_is_badrequest(""))
```

</details>

#### method-only (no path/version) is BadRequest

- method-only (no path/version) is BadRequest


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("method-only (no path/version) is BadRequest")
assert_true(_is_badrequest("GET\r\n\r\n"))
```

</details>

#### a double-space empty path is BadRequest

- a double-space empty path is BadRequest


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a double-space empty path is BadRequest")
assert_true(_is_badrequest("GET  HTTP/1.1\r\n\r\n"))
```

</details>

#### a non-absolute path is BadRequest

- a non-absolute path is BadRequest


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a non-absolute path is BadRequest")
assert_true(_is_badrequest("GET files/x HTTP/1.1\r\n\r\n"))
```

</details>

### http route hardening: CRLF handling / header injection

#### an embedded CRLF that truncates before the version is BadRequest

- an embedded CRLF that truncates before the version is BadRequest


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an embedded CRLF that truncates before the version is BadRequest")
# first \r\n cuts the line to "GET /files/a" -> no version token
assert_true(_is_badrequest("GET /files/a\r\nInjected: 1 HTTP/1.1\r\n\r\n"))
```

</details>

#### a raw-LF-injected /files segment fails closed (NotFound, not File)

- a raw-LF-injected /files segment fails closed (NotFound, not File)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a raw-LF-injected /files segment fails closed (NotFound, not File)")
# bare LF survives into the filename; must not be served as a safe segment
assert_false(_is_file("GET /files/a\nb HTTP/1.1\r\n\r\n"))
assert_true(_is_notfound("GET /files/a\nb HTTP/1.1\r\n\r\n"))
```

</details>

#### a raw-CR-injected /files segment fails closed (NotFound)

- a raw-CR-injected /files segment fails closed (NotFound)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a raw-CR-injected /files segment fails closed (NotFound)")
assert_true(_is_notfound("GET /files/a\rb HTTP/1.1\r\n\r\n"))
```

</details>

#### a NUL-injected /files segment fails closed (NotFound)

- a NUL-injected /files segment fails closed (NotFound)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a NUL-injected /files segment fails closed (NotFound)")
assert_true(_is_notfound("GET /files/a\0b HTTP/1.1\r\n\r\n"))
```

</details>

### http route hardening: percent-encoding + traversal

#### a NUL byte in the path (%00) is NotFound

- a NUL byte in the path (%00) is NotFound


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a NUL byte in the path (%00) is NotFound")
assert_true(_is_notfound("GET /files/a%00b HTTP/1.1\r\n\r\n"))
```

</details>

#### encoded slash + encoded dot-dot is NotFound

- encoded slash + encoded dot-dot is NotFound


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encoded slash + encoded dot-dot is NotFound")
assert_true(_is_notfound("GET /files/a%2f%2e%2e HTTP/1.1\r\n\r\n"))
```

</details>

#### encoded backslash traversal is NotFound

- encoded backslash traversal is NotFound


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encoded backslash traversal is NotFound")
assert_true(_is_notfound("GET /files/..%5cwin HTTP/1.1\r\n\r\n"))
```

</details>

#### a nested (multi-segment) /files path is NotFound

- a nested (multi-segment) /files path is NotFound


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a nested (multi-segment) /files path is NotFound")
assert_true(_is_notfound("GET /files/sub/secret HTTP/1.1\r\n\r\n"))
```

</details>

### http route hardening: oversized inputs

#### an oversized /files segment (>200) is NotFound

- an oversized /files segment (>200) is NotFound


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an oversized /files segment (>200) is NotFound")
val req = "GET /files/" + _repeat("a", 250) + " HTTP/1.1\r\n\r\n"
assert_true(_is_notfound(req))
```

</details>

#### an absurdly long unknown path does not crash and is NotFound

- an absurdly long unknown path does not crash and is NotFound


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an absurdly long unknown path does not crash and is NotFound")
val req = "GET /" + _repeat("x", 9000) + " HTTP/1.1\r\n\r\n"
assert_true(_is_notfound(req))
```

</details>

#### a legitimate flat filename still classifies as File (control positive)

- a legitimate flat filename still classifies as File (control positive)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a legitimate flat filename still classifies as File (control positive)")
assert_true(_is_file("GET /files/VERSION.TXT HTTP/1.1\r\n\r\n"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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

- Canonical SPipe generation for source `c4068688d75ded87aa8176e93e88fef9f01803a33dd93f9c90c8c976e3e59308`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c4068688d75ded87aa8176e93e88fef9f01803a33dd93f9c90c8c976e3e59308`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c4068688d75ded87aa8176e93e88fef9f01803a33dd93f9c90c8c976e3e59308`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/kernel/net/http_route_hardening_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/net/http_route_hardening_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/net/http_route_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/net/http_route_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/net/http_route_hardening_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowercase method is NotFound (case-sensitive GET)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/net/http_route_hardening_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mixed-case method is NotFound' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/net/http_route_hardening_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a leading space shifts the method and fails closed (BadRequest)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
