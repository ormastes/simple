# Tls Stream Socket Specification

> <details>

<!-- sdn-diagram:id=tls_stream_socket_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tls_stream_socket_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tls_stream_socket_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tls_stream_socket_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tls Stream Socket Specification

## Scenarios

### TlsStream socket round-trip

#### TlsStream.from_tcp derives non-empty keys from master secret

- client tls close
- server tls close
- listener close


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify the constructor doesn't silently zero-out keys
# by using a known-good master hex and checking key fields via
# the round-trip (if keys were empty, encrypt would produce garbage)
val listener_res = TcpListener.bind(TEST_ADDR)
expect(listener_res.is_ok()).to_equal(true)
val listener = listener_res.unwrap()

val client_tcp_res = TcpStream.connect(TEST_ADDR)
expect(client_tcp_res.is_ok()).to_equal(true)
val client_tcp = client_tcp_res.unwrap()

val server_tcp_res = listener.accept_timeout(5000)
expect(server_tcp_res.is_ok()).to_equal(true)
val server_tcp = server_tcp_res.unwrap()

val client_tls = TlsStream.from_tcp(client_tcp, TEST_MASTER_HEX, TEST_CLIENT_RANDOM, TEST_SERVER_RANDOM, true)
val server_tls = TlsStream.from_tcp(server_tcp, TEST_MASTER_HEX, TEST_CLIENT_RANDOM, TEST_SERVER_RANDOM, false)

# Keys are derived from master[0..32] and master[40..72] — non-zero
# We verify by checking they're non-empty: the spec will fail at send
# if keys are empty (AES-128 requires a 16-byte key)
expect(client_tls.client_key_hex.len().to_i64()).to_equal(32)
expect(client_tls.client_iv_hex.len().to_i64()).to_equal(8)
expect(server_tls.server_key_hex.len().to_i64()).to_equal(32)
expect(server_tls.server_iv_hex.len().to_i64()).to_equal(8)

client_tls.close()
server_tls.close()
listener.close()
```

</details>

#### send_app_record transmits encrypted bytes (client→server direction)

- var client tls = TlsStream from tcp
   - Expected: send_res.is_ok() is true
   - Expected: client_tls.send_seq equals `1`
- client tls close
- server tcp close
- listener close


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This test only exercises encrypt+send (no decrypt) to check that
# the socket send path doesn't error out.
val listener_res = TcpListener.bind("127.0.0.1:19745")
expect(listener_res.is_ok()).to_equal(true)
val listener = listener_res.unwrap()

val client_tcp_res = TcpStream.connect("127.0.0.1:19745")
expect(client_tcp_res.is_ok()).to_equal(true)
val client_tcp = client_tcp_res.unwrap()

val server_tcp_res = listener.accept_timeout(5000)
expect(server_tcp_res.is_ok()).to_equal(true)
val server_tcp = server_tcp_res.unwrap()

var client_tls = TlsStream.from_tcp(client_tcp, TEST_MASTER_HEX, TEST_CLIENT_RANDOM, TEST_SERVER_RANDOM, true)

val plaintext = _make_payload(0x48, 0x49, 0x4a, 0x4b)  # "HIJK"
val send_res = client_tls.send_app_record(plaintext)
expect(send_res.is_ok()).to_equal(true)

# seq advanced
expect(client_tls.send_seq).to_equal(1)

client_tls.close()
server_tcp.close()
listener.close()
```

</details>

#### recv_app_record decrypts client→server record (full round-trip)

- var client tls = TlsStream from tcp
- var server tls = TlsStream from tcp
- server tls tcp set read timeout
   - Expected: send_res.is_ok() is true
   - Expected: recv_res.is_ok() is true
   - Expected: got_hex equals `orig_hex`
   - Expected: client_tls.send_seq equals `1`
   - Expected: server_tls.recv_seq equals `1`
- client tls close
- server tls close
- listener close


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# THE CORE TEST: exercises the full TlsStream class:
#   from_tcp → send_app_record → [socket] → recv_app_record
# Plaintext must come back byte-exact after AEAD encrypt+decrypt.
#
# NOTE: AES-128-GCM takes ~4s/op; this test ≈ 8s total (within timeout).
val listener_res = TcpListener.bind("127.0.0.1:19746")
expect(listener_res.is_ok()).to_equal(true)
val listener = listener_res.unwrap()

# Connect first (loopback: connection goes to OS backlog)
val client_tcp_res = TcpStream.connect("127.0.0.1:19746")
expect(client_tcp_res.is_ok()).to_equal(true)
val client_tcp = client_tcp_res.unwrap()

# Accept — connection is already in backlog, won't block
val server_tcp_res = listener.accept_timeout(5000)
expect(server_tcp_res.is_ok()).to_equal(true)
val server_tcp = server_tcp_res.unwrap()

# Both sides construct TlsStream with the SAME master secret
# is_client=true for client (uses client_key to encrypt)
# is_client=false for server (uses client_key to decrypt)
var client_tls = TlsStream.from_tcp(client_tcp, TEST_MASTER_HEX, TEST_CLIENT_RANDOM, TEST_SERVER_RANDOM, true)
var server_tls = TlsStream.from_tcp(server_tcp, TEST_MASTER_HEX, TEST_CLIENT_RANDOM, TEST_SERVER_RANDOM, false)

# Set read timeout on server so recv doesn't block forever if send fails
server_tls.tcp.set_read_timeout(30000)

# Client encrypts and sends "PING" (4 bytes)
val plaintext = _make_payload(0x50, 0x49, 0x4e, 0x47)  # P I N G
val send_res = client_tls.send_app_record(plaintext)
expect(send_res.is_ok()).to_equal(true)

# Server receives and decrypts — should get back "PING" bytes
val recv_res = server_tls.recv_app_record()
expect(recv_res.is_ok()).to_equal(true)

val decrypted = recv_res.unwrap()

# Byte-exact equality via hex comparison
val orig_hex = _ts_bytes_to_hex(plaintext)
val got_hex = _ts_bytes_to_hex(decrypted)
expect(got_hex).to_equal(orig_hex)

# Sequence numbers advanced on both sides
expect(client_tls.send_seq).to_equal(1)
expect(server_tls.recv_seq).to_equal(1)

client_tls.close()
server_tls.close()
listener.close()
```

</details>

#### recv_app_record returns error on wrong decryption key (auth failure)

- var client tls = TlsStream from tcp
- var server tls = TlsStream from tcp
- server tls tcp set read timeout
   - Expected: send_res.is_ok() is true
   - Expected: recv_res.is_err() is true
- client tls close
- server tls close
- listener close


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Wire client with key A, server with key B (different master secrets).
# AEAD tag mismatch → recv_app_record must return Err (not silently
# corrupt data). This verifies the auth-failure path in recv_app_record.
val master_a = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f"
val master_b = "ff0102030405060708090a0b0c0d0e0fff101112131415161718191a1b1c1d1eff202122232425262728292a2b2c2dff"

val listener_res = TcpListener.bind("127.0.0.1:19747")
expect(listener_res.is_ok()).to_equal(true)
val listener = listener_res.unwrap()

val client_tcp_res = TcpStream.connect("127.0.0.1:19747")
expect(client_tcp_res.is_ok()).to_equal(true)
val client_tcp = client_tcp_res.unwrap()

val server_tcp_res = listener.accept_timeout(5000)
expect(server_tcp_res.is_ok()).to_equal(true)
val server_tcp = server_tcp_res.unwrap()

# Client uses master_a, server uses master_b → key mismatch
var client_tls = TlsStream.from_tcp(client_tcp, master_a, TEST_CLIENT_RANDOM, TEST_SERVER_RANDOM, true)
var server_tls = TlsStream.from_tcp(server_tcp, master_b, TEST_CLIENT_RANDOM, TEST_SERVER_RANDOM, false)

server_tls.tcp.set_read_timeout(30000)

val plaintext = _make_payload(0x41, 0x42, 0x43, 0x44)  # A B C D
val send_res = client_tls.send_app_record(plaintext)
expect(send_res.is_ok()).to_equal(true)

# Server's decrypt must FAIL (wrong key → AEAD tag mismatch)
val recv_res = server_tls.recv_app_record()
expect(recv_res.is_err()).to_equal(true)

client_tls.close()
server_tls.close()
listener.close()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/01_unit/io/tls_stream_socket_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TlsStream socket round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
