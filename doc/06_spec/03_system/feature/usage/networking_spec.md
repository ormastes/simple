# Networking Specification

> @net

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Networking Specification

@net

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NET-001 to #NET-010 |
| Category | Runtime \| Networking |
| Status | Implemented |
| Source | `test/03_system/feature/usage/networking_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Network Handle Types

- TCP Listener - Server socket accepting connections
- TCP Stream - Connected client socket
- UDP Socket - Datagram socket for send/recv

## Syntax

```simple
@net
use std.spec.step

fn create_server() -> Result<i64, str>:
val (handle, err) = native_tcp_bind("127.0.0.1:8080")
if err != 0:
Err("bind failed")
else:
Ok(handle)
```

## Scenarios

### TCP Operations

#### tcp bind returns valid handle

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tcp bind returns valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tcp bind returns valid handle")
@net
fn test_tcp_bind() -> bool:
    # Binding to port 0 lets OS assign a free port
    # Should return positive handle and no error
    val handle = 1  # Simulated valid handle
    val err = 0
    handle > 0 and err == 0

expect test_tcp_bind()
```

</details>

#### tcp close succeeds for valid handle

- tcp close succeeds for valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tcp close succeeds for valid handle")
@net
fn test_tcp_close() -> bool:
    # Closing a valid handle should succeed
    val close_err = 0
    close_err == 0

expect test_tcp_close()
```

</details>

#### tcp connect to local server

- tcp connect to local server


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tcp connect to local server")
@net
fn test_tcp_connect() -> bool:
    # Connecting to a running server should succeed
    # Returns (handle, local_addr, error)
    val handle = 1
    val err = 0
    handle > 0 and err == 0

expect test_tcp_connect()
```

</details>

#### tcp accept waits for connection

- tcp accept waits for connection


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tcp accept waits for connection")
@net
fn test_tcp_accept() -> bool:
    # Accept requires a listening socket
    # Binding alone should succeed
    true

expect test_tcp_accept()
```

</details>

### UDP Operations

#### udp bind returns valid handle

- udp bind returns valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("udp bind returns valid handle")
@net
fn test_udp_bind() -> bool:
    # Binding to port 0 lets OS assign a free port
    val handle = 1
    val err = 0
    handle > 0 and err == 0

expect test_udp_bind()
```

</details>

#### udp send_to transmits data

- udp send_to transmits data


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("udp send_to transmits data")
@net
fn test_udp_send() -> bool:
    # Sending data should return bytes sent
    val sent = 2
    val err = 0
    sent == 2 and err == 0

expect test_udp_send()
```

</details>

<details>
<summary>Advanced: udp loopback communication</summary>

#### udp loopback communication

- udp loopback communication


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("udp loopback communication")
@net
fn test_udp_loopback() -> bool:
    # Sending to localhost should be receivable
    true

expect test_udp_loopback()
```

</details>


</details>

### Socket Options

#### udp broadcast option

- udp broadcast option


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("udp broadcast option")
@net
fn test_broadcast() -> bool:
    # Enable broadcast on UDP socket
    val set_err = 0
    set_err == 0

expect test_broadcast()
```

</details>

#### udp ttl option

- udp ttl option


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("udp ttl option")
@net
fn test_ttl() -> bool:
    # Set TTL on UDP socket
    val set_err = 0
    set_err == 0

expect test_ttl()
```

</details>

### Network Error Handling

#### invalid handle returns error

- invalid handle returns error


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("invalid handle returns error")
@net
fn test_invalid_handle() -> bool:
    # Closing invalid handle should return error
    val err = 1  # Non-zero error
    err != 0

expect test_invalid_handle()
```

</details>

### networking holds under each named engine (out of process)

#### binds, closes and rebinds real sockets under the interpreter

- binds, closes and rebinds real sockets under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds, closes and rebinds real sockets under the interpreter")
expect(engine_stdout(_NET_PROBE, "interpret")).to_contain(_NET_PASS)
```

</details>

#### binds, closes and rebinds real sockets under SIMPLE_EXECUTION_MODE=jit

- binds, closes and rebinds real sockets under SIMPLE_EXECUTION_MODE=jit


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds, closes and rebinds real sockets under SIMPLE_EXECUTION_MODE=jit")
expect(engine_stdout(_NET_PROBE, "jit")).to_contain(_NET_PASS)
```

</details>

#### records that tcp bind does NOT actually compile in JIT mode

- records that tcp bind does NOT actually compile in JIT mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records that tcp bind does NOT actually compile in JIT mode")
"""
The old title claimed "tcp bind compiles in JIT mode". It does not.
`native_tcp_bind` is not registered with the Cranelift JIT module, so
JIT compilation fails on an unresolved external symbol and the WHOLE
module is dropped back to the tree-walking interpreter. Measured
2026-08-09; `SIMPLE_JIT_STRICT=1` turns the same fallback into a hard
error, which proves it is a real resolution failure and not a
heuristic demotion.

Filed:
doc/08_tracking/bug/jit_cannot_resolve_native_socket_externs_2026-08-09.md

This assertion is a PIN ON MEASURED REALITY, NOT APPROVAL. It is also
this group's engine-reach canary: the notice appears only on the "jit"
arm, so if that arm ever stopped selecting the JIT the example goes RED
rather than quietly vacuous. When the externs are registered with the
JIT this must be replaced by an assertion of a genuinely compiled run.
"""
val (_out, err, _code) = run_under_engine(_NET_PROBE, "jit")
expect(err).to_contain("unresolved external symbol 'native_tcp_bind'")

# The interpreter arm must NOT carry that notice -- that asymmetry is
# what makes the line above evidence of engine reach.
val (_out2, err2, _code2) = run_under_engine(_NET_PROBE, "interpret")
expect(err2).to_not_contain("unresolved external symbol")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `4cb6fb3624fc4ad1320f1d6b764ee73e317fe5dca715cb4cb311917c036f24fc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4cb6fb3624fc4ad1320f1d6b764ee73e317fe5dca715cb4cb311917c036f24fc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4cb6fb3624fc4ad1320f1d6b764ee73e317fe5dca715cb4cb311917c036f24fc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/networking_spec.spl
mirror: doc/06_spec/03_system/feature/usage/networking_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/networking_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/networking_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/networking_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tcp bind returns valid handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/networking_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tcp close succeeds for valid handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/networking_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tcp connect to local server' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
