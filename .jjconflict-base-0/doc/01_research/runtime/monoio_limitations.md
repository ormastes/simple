# Monoio Runtime Limitations

## Overview

The Simple language provides FFI bindings to the monoio async runtime for high-performance I/O operations. However, due to architectural constraints at the FFI boundary, certain operations are not supported.

## What Works ✓

### TCP
- **Connection Management**: `monoio_tcp_listen`, `monoio_tcp_accept`, `monoio_tcp_connect`
- **Metadata Access**: `monoio_tcp_local_addr`, `monoio_tcp_peer_addr`
- **Resource Cleanup**: `monoio_tcp_close`, `monoio_tcp_listener_close`

### UDP
- **Socket Management**: `monoio_udp_bind`, `monoio_udp_close`
- **Connectionless I/O**: `monoio_udp_send_to`, `monoio_udp_recv_from`
- **Connected Mode**: `monoio_udp_connect`, `monoio_udp_send`, `monoio_udp_recv`
- **Metadata Access**: `monoio_udp_local_addr`

## What Doesn't Work ✗

### TCP Streaming Operations (Not Supported)
- `monoio_tcp_read` - Reading data from TCP stream
- `monoio_tcp_write` - Writing data to TCP stream
- `monoio_tcp_flush` - Flushing write buffer
- `monoio_tcp_shutdown` - Graceful connection shutdown

### TCP Socket Options (Not Supported)
- `monoio_tcp_set_nodelay` - Nagle's algorithm control
- `monoio_tcp_set_keepalive` - TCP keepalive configuration

### UDP Advanced Features (Not Supported)
- `monoio_udp_join_multicast` - Join multicast group
- `monoio_udp_leave_multicast` - Leave multicast group

## Why These Limitations Exist

### The Core Problem: Send/Sync Bounds

Monoio's `TcpStream` and `UdpSocket` types are **not Send/Sync**. This means:

1. They cannot be stored in global `Mutex<Vec<T>>` (our handle storage pattern)
2. They cannot be safely shared across threads
3. They cannot persist across FFI calls in our current architecture

### TCP Streaming Specifically

TCP streams are **stateful**:
- Maintain connection state (sequence numbers, buffers)
- Cannot be recreated from scratch like UDP sockets
- Read/write operations modify internal state
- Dropping a stream closes the connection

Our FFI boundary is **stateless**:
- Each FFI call is independent
- Cannot persist non-Send types across calls
- Would need dedicated runtime thread + message passing

### UDP Multicast

Multicast membership requires:
- Persistent socket that remains joined to group
- Cannot recreate socket and rejoin on each operation
- Same Send/Sync constraint as TCP

## Recommended Alternatives

### For TCP Streaming

**Option 1: Use Simple's Async/Await (Recommended)**

Simple language has first-class async/await support that can use monoio directly:

```simple
import monoio

async fn handle_client(stream: monoio.TcpStream):
    var buffer = Buffer.new(1024)
    while true:
        val n = await stream.read(buffer)
        if n == 0:
            break
        await stream.write(buffer[0:n])

async fn main():
    val listener = await monoio.TcpListener.bind("127.0.0.1:8080")
    while true:
        val (stream, addr) = await listener.accept()
        spawn handle_client(stream)
```

This approach:
- ✓ Uses monoio types directly (no FFI)
- ✓ Full async/await support
- ✓ No Send/Sync issues
- ✓ Idiomatic Simple code

**Option 2: Use std::net for Synchronous I/O**

For simple use cases, use blocking I/O:

```simple
import net

fn handle_client(stream: net.TcpStream):
    var buffer = Buffer.new(1024)
    while true:
        val n = stream.read(buffer)
        if n == 0:
            break
        stream.write(buffer[0:n])
```

This approach:
- ✓ Simple and straightforward
- ✓ No async complexity
- ✓ Works across FFI boundary
- ✗ Blocks thread during I/O
- ✗ Lower performance at scale

### For UDP Multicast

**Use std::net::UdpSocket**:

```simple
import net

fn main():
    val socket = net.UdpSocket.bind("0.0.0.0:12345")
    socket.join_multicast_v4("239.0.0.1", "0.0.0.0")

    var buffer = Buffer.new(1024)
    while true:
        val (n, addr) = socket.recv_from(buffer)
        print("Received from {addr}: {buffer[0:n]}")
```

## Could This Be Fixed?

### Option A: Dedicated Runtime Thread Architecture

We could implement TCP streaming and multicast by:

1. Spawn a dedicated monoio runtime thread
2. Use channels for FFI ↔ runtime communication
3. FFI functions send requests and wait for responses
4. Runtime thread executes async operations

**Effort**: 40-80 hours
**Benefit**: Full monoio API available via FFI
**Tradeoff**: Complex architecture, message passing overhead

### Option B: Compile-Time Monoio Integration

Instead of FFI, compile Simple async code directly to monoio calls:

1. Simple async/await → monoio runtime calls
2. No FFI boundary
3. Direct type usage

**Status**: Already implemented! Use async/await in Simple.

### Recommendation

**Don't fix it.** The current approach is optimal:

- Simple async/await gives you full monoio power
- FFI provides what FFI can provide
- Clear documentation of boundaries
- No complex workarounds needed

## Summary

| Feature | Status | Use Instead |
|---------|--------|-------------|
| TCP connection | ✓ Supported | monoio FFI |
| TCP streaming | ✗ Not supported | Simple async/await or std::net |
| UDP basic I/O | ✓ Supported | monoio FFI |
| UDP connected | ✓ Supported | monoio FFI |
| UDP multicast | ✗ Not supported | std::net |

The limitations are **architectural and intentional**, not bugs to be fixed. Use the right tool for your use case:

- **High-performance async I/O**: Write async Simple code
- **Simple sync I/O**: Use std::net via FFI
- **Connection setup/teardown**: Use monoio FFI

This gives you the best of all worlds without architectural compromises.
