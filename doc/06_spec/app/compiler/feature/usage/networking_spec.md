# Networking Specification

Tests networking functionality including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NET-001 to #NET-010 |
| Category | Runtime \| Networking |
| Status | Implemented |
| Source | `test/feature/usage/networking_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests networking functionality including:
- TCP socket binding and connection
- UDP socket operations
- Socket options (broadcast, TTL)
- Error handling for invalid handles
- JIT compilation mode networking

## Network Handle Types

- TCP Listener - Server socket accepting connections
- TCP Stream - Connected client socket
- UDP Socket - Datagram socket for send/recv

## Syntax

```simple
@net
fn create_server() -> Result<i64, str>:
val (handle, err) = native_tcp_bind("127.0.0.1:8080")
if err != 0:
Err("bind failed")
else:
Ok(handle)
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/networking/result.json` |

## Scenarios

- tcp bind returns valid handle
- tcp close succeeds for valid handle
- tcp connect to local server
- tcp accept waits for connection
- udp bind returns valid handle
- udp send_to transmits data
- udp loopback communication
- udp broadcast option
- udp ttl option
- invalid handle returns error
- tcp bind compiles in JIT mode
- udp bind compiles in JIT mode
