# DB server TCP transport — bounded request line read

> Verifies the db server tcp bounded line behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DB server TCP transport — bounded request line read

Verifies the db server tcp bounded line behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the db server tcp bounded line behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### TcpStream.read_line_bounded

#### returns a line at or under the bound

- Verify: returns a line at or under the bound
   - Expected: got equals `hello\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-DBSERVER-002
step("Verify: returns a line at or under the bound")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: fails closed instead of buffering an over-cap line with no newline
   - Expected: failed_closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-DBSERVER-002
step("Verify: fails closed instead of buffering an over-cap line with no newline")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: closes the connection rather than buffering an unbounded no-newline line
   - Expected: closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-DBSERVER-002
step("Verify: closes the connection rather than buffering an unbounded no-newline line")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `02fa41b8e003c30910b6e4c743c15d1789f260b871c84e9da9b2d7a928ce9e6d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `02fa41b8e003c30910b6e4c743c15d1789f260b871c84e9da9b2d7a928ce9e6d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `02fa41b8e003c30910b6e4c743c15d1789f260b871c84e9da9b2d7a928ce9e6d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
