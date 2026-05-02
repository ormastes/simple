# Networking Specification

**Feature ID:** #NET-001 to #NET-010 | **Category:** Runtime | Networking | **Status:** Implemented

_Source: `test/feature/usage/networking_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 12 |

## Test Structure

### TCP Operations

- ✅ tcp bind returns valid handle
- ✅ tcp close succeeds for valid handle
- ✅ tcp connect to local server
- ✅ tcp accept waits for connection
### UDP Operations

- ✅ udp bind returns valid handle
- ✅ udp send_to transmits data
- ✅ udp loopback communication
### Socket Options

- ✅ udp broadcast option
- ✅ udp ttl option
### Network Error Handling

- ✅ invalid handle returns error
### JIT Compilation Mode

- ✅ tcp bind compiles in JIT mode
- ✅ udp bind compiles in JIT mode

