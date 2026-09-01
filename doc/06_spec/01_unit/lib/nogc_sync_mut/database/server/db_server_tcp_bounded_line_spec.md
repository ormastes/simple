# DB server TCP transport — bounded request line read

> `TcpDbTransport.read_message` used to call `read_line_nullable()`, which has

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DB server TCP transport — bounded request line read

`TcpDbTransport.read_message` used to call `read_line_nullable()`, which has

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

`TcpDbTransport.read_message` used to call `read_line_nullable()`, which has
no byte bound: a client that sends bytes forever without a newline makes the
server buffer all of it before `protocol.spl`'s `MAX_REQUEST_BYTES` check ever
runs. This pins the fix at the stream layer (`TcpStream.read_line_bounded`)
and at the transport call site, using a real socket pair — not a mock — so
the bound is proven against the actual blocking read path.

## Scenarios

### TcpStream.read_line_bounded

#### returns a line at or under the bound

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns a line at or under the bound
   - Expected: got equals `hello\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns a line at or under the bound")
val bind_result = TcpListener.bind("127.0.0.1:0")
var listener = match bind_result:
    Err(e): panic("bind failed: {e.message}")
    Ok(l): l
val addr = match listener.local_addr():
    Err(e): panic("local_addr failed: {e.message}")
    Ok(a): a
var client = match TcpStream.connect(addr):
    Err(e): panic("connect failed: {e.message}")
    Ok(c): c
match client.write_all("hello\n".bytes()):
    Err(e): panic("write failed: {e.message}")
    Ok(_): pass
val _ = client.flush()
var server = match listener.accept():
    Err(e): panic("accept failed: {e.message}")
    Ok(s): s

val got = match server.read_line_bounded(8192):
    Err(e): panic("read_line_bounded failed: {e.message}")
    Ok(line): line
expect(got).to_equal("hello\n")

val _ = server.close()
val _ = client.close()
val _ = listener.close()
```

</details>

#### fails closed instead of buffering an over-cap line with no newline

- fails closed instead of buffering an over-cap line with no newline
   - Expected: failed_closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed instead of buffering an over-cap line with no newline")
val bind_result = TcpListener.bind("127.0.0.1:0")
var listener = match bind_result:
    Err(e): panic("bind failed: {e.message}")
    Ok(l): l
val addr = match listener.local_addr():
    Err(e): panic("local_addr failed: {e.message}")
    Ok(a): a
var client = match TcpStream.connect(addr):
    Err(e): panic("connect failed: {e.message}")
    Ok(c): c

# Send MAX_REQUEST_BYTES(8192) + 1 bytes, no newline. Over the
# (max_bytes = 8192) bound the read must fail rather than buffer.
var payload: [u8] = []
var i = 0
while i < 8193:
    payload = payload.append(65)
    i = i + 1
match client.write_all(payload):
    Err(e): panic("write failed: {e.message}")
    Ok(_): pass
val _ = client.flush()
var server = match listener.accept():
    Err(e): panic("accept failed: {e.message}")
    Ok(s): s

val result = server.read_line_bounded(8192)
val failed_closed = match result:
    Err(_e): true
    Ok(_line): false
expect(failed_closed).to_equal(true)

val _ = server.close()
val _ = client.close()
val _ = listener.close()
```

</details>

### TcpDbTransport.read_message — byte-level bound

#### closes the connection rather than buffering an unbounded no-newline line

- closes the connection rather than buffering an unbounded no-newline line
   - Expected: closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("closes the connection rather than buffering an unbounded no-newline line")
val bind_result = TcpDbListener.bind("127.0.0.1:0")
var listener = match bind_result:
    Err(e): panic("bind failed: {e.message}")
    Ok(l): l
val addr = match listener.listener.local_addr():
    Err(e): panic("local_addr failed: {e.message}")
    Ok(a): a
var client = match TcpStream.connect(addr):
    Err(e): panic("connect failed: {e.message}")
    Ok(c): c

# Well over MAX_REQUEST_BYTES(8192) + 1, still no newline, so the
# bound trips without needing to wait on the read timeout for EOF.
var payload: [u8] = []
var i = 0
while i < 20000:
    payload = payload.append(65)
    i = i + 1
match client.write_all(payload):
    Err(e): panic("write failed: {e.message}")
    Ok(_): pass
val _ = client.flush()

var transport = match listener.accept_timeout(5000):
    Err(e): panic("accept failed: {e.message}")
    Ok(t): t

val message = transport.read_message()
val closed = message == nil
expect(closed).to_equal(true)

val _ = client.close()
val _ = listener.close()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-DBSERVER-002`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `26ea8684cac793db11db82db1e90cc4fd63030098975636eb41f44225c1393e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `26ea8684cac793db11db82db1e90cc4fd63030098975636eb41f44225c1393e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `26ea8684cac793db11db82db1e90cc4fd63030098975636eb41f44225c1393e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a line at or under the bound' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed instead of buffering an over-cap line with no newline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'closes the connection rather than buffering an unbounded no-newline line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
