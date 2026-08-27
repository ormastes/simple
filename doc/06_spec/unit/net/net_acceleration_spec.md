# net_acceleration_spec

> Net Acceleration Remaining — Spipe Spec

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# net_acceleration_spec

Net Acceleration Remaining — Spipe Spec

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/net/net_acceleration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Net Acceleration Remaining — Spipe Spec

20 tests covering:
  - TCP connection behavior (states, connect results, recv, send buffer, terminal transitions)
  - Socket connect semantics (POSIX outcomes, readiness, poll)
  - HTTP capability router (static-file routing, worker startup)
  - Packet ring ownership (RX/TX descriptors, ring config)

All classes and helpers are defined inline — no imports from source files.

Feature IDs: FR-NET-0001, FR-NET-0002, FR-NET-0003, FR-NET-0004
Plan: doc/03_plan/agent_tasks/net_acceleration_remaining_2026-04-21.md

## Scenarios

### TCP Connection Behavior

#### connect completion results

#### established result marks success true

- established result marks success true
   - Expected: r.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("established result marks success true")
val r = make_connect_established()
expect(r.success).to_equal(true)
```

</details>

#### in-progress result carries EINPROGRESS code

- in-progress result carries EINPROGRESS code
   - Expected: r.error_msg equals `EINPROGRESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("in-progress result carries EINPROGRESS code")
val r = make_connect_in_progress()
expect(r.error_msg).to_equal("EINPROGRESS")
```

</details>

#### refused result is a terminal outcome

- refused result is a terminal outcome
   - Expected: tcp_is_terminal(r) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refused result is a terminal outcome")
val r = make_connect_refused()
expect(tcp_is_terminal(r)).to_equal(true)
```

</details>

#### in-progress result is NOT terminal

- in-progress result is NOT terminal
   - Expected: tcp_is_terminal(r) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("in-progress result is NOT terminal")
val r = make_connect_in_progress()
expect(tcp_is_terminal(r)).to_equal(false)
```

</details>

#### timed-out result carries ETIMEDOUT and is terminal

- timed-out result carries ETIMEDOUT and is terminal
   - Expected: r.error_msg equals `ETIMEDOUT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("timed-out result carries ETIMEDOUT and is terminal")
val r = make_connect_timed_out()
expect(r.error_msg).to_equal("ETIMEDOUT")
```

</details>

### TCP Recv and Send Buffer

#### recv results

#### data recv carries the correct byte count

- data recv carries the correct byte count
   - Expected: r.bytes_read equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("data recv carries the correct byte count")
val r = make_recv_data(512)
expect(r.bytes_read).to_equal(512)
```

</details>

#### would-block recv returns zero bytes

- would-block recv returns zero bytes
   - Expected: r.bytes_read equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("would-block recv returns zero bytes")
val r = make_recv_would_block()
expect(r.bytes_read).to_equal(0)
```

</details>

#### peer-closed recv sets peer_closed flag

- peer-closed recv sets peer_closed flag
   - Expected: r.peer_closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("peer-closed recv sets peer_closed flag")
val r = make_recv_peer_closed()
expect(r.peer_closed).to_equal(true)
```

</details>

#### reset recv sets was_reset flag

- reset recv sets was_reset flag
   - Expected: r.was_reset is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reset recv sets was_reset flag")
val r = make_recv_reset()
expect(r.was_reset).to_equal(true)
```

</details>

#### send buffer window

#### send buffer allows queuing within window

- send buffer allows queuing within window
   - Expected: send_buf_can_queue(buf, 1024) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("send buffer allows queuing within window")
val buf = make_send_buf(4096, 2048)
expect(send_buf_can_queue(buf, 1024)).to_equal(true)
```

</details>

### Socket Connect Semantics

#### connect outcomes

#### ok outcome is writable

- ok outcome is writable
   - Expected: o.readiness.writable is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ok outcome is writable")
val o = make_connect_ok()
expect(o.readiness.writable).to_equal(true)
```

</details>

#### in-progress outcome is not ready

- in-progress outcome is not ready
   - Expected: o.ready is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("in-progress outcome is not ready")
val o = make_connect_progress()
expect(o.ready).to_equal(false)
```

</details>

#### in-progress outcome label is in-progress

- in-progress outcome label is in-progress
   - Expected: outcome_label(o) equals `in-progress`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("in-progress outcome label is in-progress")
val o = make_connect_progress()
expect(outcome_label(o)).to_equal("in-progress")
```

</details>

#### refused outcome has error bit set

- refused outcome has error bit set
   - Expected: o.readiness.is_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refused outcome has error bit set")
val o = make_connect_err("ECONNREFUSED")
expect(o.readiness.is_error).to_equal(true)
```

</details>

#### ok outcome label is connected

- ok outcome label is connected
   - Expected: outcome_label(o) equals `connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ok outcome label is connected")
val o = make_connect_ok()
expect(outcome_label(o)).to_equal("connected")
```

</details>

### HTTP Capability Router and Packet Ring

#### static file routing

#### portable backend routes to portable-read

- portable backend routes to portable-read
   - Expected: action.use_portable_read is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("portable backend routes to portable-read")
val caps = make_caps_portable("portable-socket")
val action = route_static_file(caps, true)
expect(action.use_portable_read).to_equal(true)
```

</details>

#### sendfile backend routes via sendfile

- sendfile backend routes via sendfile
   - Expected: action.use_sendfile is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sendfile backend routes via sendfile")
val caps = make_caps_sendfile("linux-io-uring")
val action = route_static_file(caps, true)
expect(action.use_sendfile).to_equal(true)
```

</details>

#### zero-copy backend reports sendfile tier

- zero-copy backend reports sendfile tier
   - Expected: http_tier(caps) equals `zero-copy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-copy backend reports sendfile tier")
val caps = make_caps_zero_copy("dma-engine")
expect(http_tier(caps)).to_equal("zero-copy")
```

</details>

#### packet ring ownership

#### rx descriptor ready transfers ownership to app

- rx descriptor ready transfers ownership to app
   - Expected: desc.owner.owner_name equals `app`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rx descriptor ready transfers ownership to app")
val desc = rx_ready(0, 64)
expect(desc.owner.owner_name).to_equal("app")
```

</details>

#### af-xdp ring config enables packet io

- af-xdp ring config enables packet io
   - Expected: cfg.supports_packet_io is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("af-xdp ring config enables packet io")
val cfg = ring_cfg_afxdp(1024)
expect(cfg.supports_packet_io).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `f328be9b9997e4466e8b3894a94831fd060360b7e5cf2db4ab7fb09a7392b2c4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f328be9b9997e4466e8b3894a94831fd060360b7e5cf2db4ab7fb09a7392b2c4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f328be9b9997e4466e8b3894a94831fd060360b7e5cf2db4ab7fb09a7392b2c4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/net/net_acceleration_spec.spl
mirror: doc/06_spec/unit/net/net_acceleration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/net/net_acceleration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/net/net_acceleration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/net/net_acceleration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/net/net_acceleration_spec.spl:208:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'established result marks success true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/net/net_acceleration_spec.spl:214:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'in-progress result carries EINPROGRESS code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/net/net_acceleration_spec.spl:220:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refused result is a terminal outcome' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
