# tcp_socket_resource_wrapper_spec

> Resource wrapper for TcpSocket — WP-J pilot migration

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# tcp_socket_resource_wrapper_spec

Resource wrapper for TcpSocket — WP-J pilot migration

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/01_unit/io/tcp_socket_resource_wrapper_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

```simple
Resource wrapper for TcpSocket — WP-J pilot migration

Tests the TcpSocket wrapper class with resource ownership pattern:
- Sentinel-based validity checks (-1 = invalid/closed fd)
- Consuming close() method
- Double-close guard (one-shot safety)
- Borrow methods refuse to touch an invalid handle

NOTE: close()/borrow paths on a VALID-looking fabricated fd are deliberately
NOT tested — they call real C externs (rt_io_tcp_close etc.) on a bogus fd,
which can close/corrupt the test runner's own descriptors. All guard proofs
below use only the invalid sentinel (-1), which short-circuits before any
use std.spec.step

extern call.

```
## Scenarios

### TcpSocket resource wrapper

#### is_valid accepts a non-negative fd

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is_valid accepts a non-negative fd


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_valid accepts a non-negative fd")
val sock = TcpSocket(fd: 7)
assert_true(sock.is_valid())
```

</details>

#### is_valid detects the invalid sentinel (-1)

- is_valid detects the invalid sentinel (-1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_valid detects the invalid sentinel (-1)")
val sock = TcpSocket(fd: -1)
assert_false(sock.is_valid())
```

</details>

#### sentinel is -1 not 0 (fd 0 is a legal descriptor)

- sentinel is -1 not 0 (fd 0 is a legal descriptor)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sentinel is -1 not 0 (fd 0 is a legal descriptor)")
val sock_zero = TcpSocket(fd: 0)
assert_true(sock_zero.is_valid())
val sock_neg = TcpSocket(fd: -1)
assert_false(sock_neg.is_valid())
```

</details>

#### close on invalid handle is safe and idempotent

- close on invalid handle is safe and idempotent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close on invalid handle is safe and idempotent")
val sock = TcpSocket(fd: -1)
sock.close()
assert_equal(sock.fd, -1)
sock.close()
assert_equal(sock.fd, -1)
```

</details>

#### bind refuses an invalid handle

- bind refuses an invalid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bind refuses an invalid handle")
val sock = TcpSocket(fd: -1)
assert_false(sock.bind("127.0.0.1:0"))
```

</details>

#### listen refuses an invalid handle

- listen refuses an invalid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("listen refuses an invalid handle")
val sock = TcpSocket(fd: -1)
assert_false(sock.listen(1))
```

</details>

#### local_addr returns nil on invalid handle

- local_addr returns nil on invalid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("local_addr returns nil on invalid handle")
val sock = TcpSocket(fd: -1)
assert_nil(sock.local_addr())
```

</details>

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

- Canonical SPipe generation for source `720a741f3ec5db098ede56352cef19f1833e00bf83d21286efae3247559cb2a8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `720a741f3ec5db098ede56352cef19f1833e00bf83d21286efae3247559cb2a8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `720a741f3ec5db098ede56352cef19f1833e00bf83d21286efae3247559cb2a8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/io/tcp_socket_resource_wrapper_spec.spl
mirror: doc/06_spec/01_unit/io/tcp_socket_resource_wrapper_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/io/tcp_socket_resource_wrapper_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/io/tcp_socket_resource_wrapper_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/io/tcp_socket_resource_wrapper_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_valid accepts a non-negative fd' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/io/tcp_socket_resource_wrapper_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_valid detects the invalid sentinel (-1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/io/tcp_socket_resource_wrapper_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sentinel is -1 not 0 (fd 0 is a legal descriptor)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
