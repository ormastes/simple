# quic_udp_initial_spec

> var out: [u8] = []

<!-- sdn-diagram:id=quic_udp_initial_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=quic_udp_initial_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

quic_udp_initial_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=quic_udp_initial_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# quic_udp_initial_spec

var out: [u8] = []

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/quic/quic_udp_initial_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

var out: [u8] = []
    out.push(QUIC_LONG_HDR | QUIC_FIXED | (QUIC_INITIAL_TYPE << 4))
    out.push(0x00)
    out.push(0x00)
    out.push(0x00)
    out.push(0x01)
    out.push(dcid.len())
    _append(out, dcid)
    out.push(scid.len())
    _append(out, scid)
    out.push(0x00)
    _append(out, _varint1(1))
    out.push(pkt_num & 0xff)
    return out

fn recv_bytes(res: Result<[i64], text>) -> [u8]:
    """Extract payload bytes from native_udp_recv_from result.

    Ok payload is [recv_len:i64, from_addr:text, data:[i64]] — a 3-element array.
    Coerces data array from [i64] to [u8] by masking each element to 0xFF.
    Returns [] on timeout/error.

## Scenarios

### QUIC Initial packet wire format

#### encodes first byte as 0xC0 (long-header + fixed + Initial + PN_len=0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dcid: [u8] = [0x01, 0x02, 0x03, 0x04]
val scid: [u8] = [0x0a, 0x0b]
val pkt = build_initial(dcid, scid, 0)
expect(byte_at(pkt, 0)).to_equal(192)     # 0xC0
```

</details>

#### encodes QUIC v1 in bytes 1-4 (big-endian 0x00000001)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dcid: [u8] = [0x01, 0x02]
val scid: [u8] = [0x03]
val pkt = build_initial(dcid, scid, 0)
expect(byte_at(pkt, 1)).to_equal(0)
expect(byte_at(pkt, 2)).to_equal(0)
expect(byte_at(pkt, 3)).to_equal(0)
expect(byte_at(pkt, 4)).to_equal(1)
```

</details>

#### encodes DCID length and DCID bytes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dcid: [u8] = [0xaa, 0xbb, 0xcc, 0xdd]
val scid: [u8] = [0x11]
val pkt = build_initial(dcid, scid, 0)
expect(byte_at(pkt, 5)).to_equal(4)       # dcid_len
expect(byte_at(pkt, 6)).to_equal(170)     # 0xaa
expect(byte_at(pkt, 7)).to_equal(187)     # 0xbb
expect(byte_at(pkt, 9)).to_equal(221)     # 0xdd
```

</details>

#### encodes SCID length and SCID bytes after DCID

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# layout: 1+4+1+2+1+2+1+1+1 = 14 bytes total
val dcid: [u8] = [0x01, 0x02]
val scid: [u8] = [0xfe, 0xfd]
val pkt = build_initial(dcid, scid, 0)
expect(byte_at(pkt, 8)).to_equal(2)       # scid_len
expect(byte_at(pkt, 9)).to_equal(254)     # 0xfe
expect(byte_at(pkt, 10)).to_equal(253)    # 0xfd
```

</details>

#### encodes token_len=0 then length=1 then packet_number

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# layout: 1+4+1+1+1+1+1+1+1 = 12 bytes
val dcid: [u8] = [0x01]
val scid: [u8] = [0x02]
val pkt = build_initial(dcid, scid, 7)
expect(byte_at(pkt, 9)).to_equal(0)       # token_len
expect(byte_at(pkt, 10)).to_equal(1)      # length varint = 1
expect(byte_at(pkt, 11)).to_equal(7)      # pkt_num
```

</details>

#### total packet length = 1+4+1+dcid.len+1+scid.len+1+1+1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dcid: [u8] = [0x01, 0x02, 0x03]      # 3 bytes
val scid: [u8] = [0x04, 0x05]             # 2 bytes
val pkt = build_initial(dcid, scid, 0)
# 1(first)+4(ver)+1(dcidlen)+3(dcid)+1(scidlen)+2(scid)+1(token)+1(length)+1(pn)=15
expect(pkt.len()).to_equal(15)
```

</details>

### QUIC Initial packet round-trip over loopback UDP

#### sends an Initial packet and receives exact bytes back

- native udp set read timeout
   - Expected: cli_err equals `0`
   - Expected: send_err equals `0`
   - Expected: sent equals `n`
   - Expected: rx.len() equals `pkt.len()`
   - Expected: byte_at(rx, 0) equals `192)      # 0xC0 — long|fixed|Initial`
   - Expected: byte_at(rx, 4) equals `1)        # QUIC v1 LSB`
   - Expected: byte_at(rx, 5) equals `8)        # DCID length = 8`
   - Expected: byte_at(rx, 6) equals `8)        # DCID[0] = 0x08`
- native udp close
- native udp close


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (srv, srv_err) = native_udp_bind("127.0.0.1:19211")
expect(srv_err).to_equal(0)
native_udp_set_read_timeout(srv, 1000)

val (cli, cli_err) = native_udp_bind("127.0.0.1:19210")
expect(cli_err).to_equal(0)

val dcid: [u8] = [0x08, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]
val scid: [u8] = [0x04, 0xaa, 0xbb, 0xcc]
val pkt = build_initial(dcid, scid, 0)
val n: i64 = pkt.len()

val (sent, send_err) = native_udp_send_to(cli, pkt, n, "127.0.0.1:19211")
expect(send_err).to_equal(0)
expect(sent).to_equal(n)

val raw_res = native_udp_recv_from(srv, 65535)
val rx = recv_bytes(raw_res)

# Length must exactly match sent
expect(rx.len()).to_equal(pkt.len())

# Exact wire bytes: first_byte=0xC0, version_lsb=1, dcid_len=8, dcid[0]=0x08
expect(byte_at(rx, 0)).to_equal(192)      # 0xC0 — long|fixed|Initial
expect(byte_at(rx, 4)).to_equal(1)        # QUIC v1 LSB
expect(byte_at(rx, 5)).to_equal(8)        # DCID length = 8
expect(byte_at(rx, 6)).to_equal(8)        # DCID[0] = 0x08

native_udp_close(cli)
native_udp_close(srv)
```

</details>

#### round-trips an Initial packet with packet_number=42

- native udp set read timeout
   - Expected: cli_err equals `0`
   - Expected: send_err equals `0`
   - Expected: rx.len() equals `pkt.len()`
   - Expected: byte_at(rx, last_idx) equals `42`
- native udp close
- native udp close


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (srv, srv_err) = native_udp_bind("127.0.0.1:19213")
expect(srv_err).to_equal(0)
native_udp_set_read_timeout(srv, 1000)
val (cli, cli_err) = native_udp_bind("127.0.0.1:19212")
expect(cli_err).to_equal(0)

val dcid: [u8] = [0xde, 0xad]
val scid: [u8] = [0xbe, 0xef]
val pkt = build_initial(dcid, scid, 42)
val n: i64 = pkt.len()
val (sent, send_err) = native_udp_send_to(cli, pkt, n, "127.0.0.1:19213")
expect(send_err).to_equal(0)

val raw_res = native_udp_recv_from(srv, 65535)
val rx = recv_bytes(raw_res)
expect(rx.len()).to_equal(pkt.len())

# Packet number is the last byte of the header
val last_idx: i64 = rx.len() - 1
expect(byte_at(rx, last_idx)).to_equal(42)

native_udp_close(cli)
native_udp_close(srv)
```

</details>

#### connection IDs survive the UDP round-trip byte-for-byte

- native udp set read timeout
   - Expected: cli_err equals `0`
   - Expected: send_err equals `0`
   - Expected: rx.len() equals `pkt.len()`
   - Expected: byte_at(rx, 6) equals `16)       # 0x10`
   - Expected: byte_at(rx, 7) equals `32)       # 0x20`
   - Expected: byte_at(rx, 8) equals `48)       # 0x30`
   - Expected: byte_at(rx, 10) equals `64)      # 0x40`
   - Expected: byte_at(rx, 11) equals `80)      # 0x50`
- native udp close
- native udp close


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (srv, srv_err) = native_udp_bind("127.0.0.1:19215")
expect(srv_err).to_equal(0)
native_udp_set_read_timeout(srv, 1000)
val (cli, cli_err) = native_udp_bind("127.0.0.1:19214")
expect(cli_err).to_equal(0)

val dcid: [u8] = [0x10, 0x20, 0x30]
val scid: [u8] = [0x40, 0x50]
val pkt = build_initial(dcid, scid, 0)
val n: i64 = pkt.len()
val (sent, send_err) = native_udp_send_to(cli, pkt, n, "127.0.0.1:19215")
expect(send_err).to_equal(0)

val raw_res = native_udp_recv_from(srv, 65535)
val rx = recv_bytes(raw_res)
expect(rx.len()).to_equal(pkt.len())

# DCID at byte offset 6 (after 1+4+1)
expect(byte_at(rx, 6)).to_equal(16)       # 0x10
expect(byte_at(rx, 7)).to_equal(32)       # 0x20
expect(byte_at(rx, 8)).to_equal(48)       # 0x30

# SCID at byte offset 10 (after 6+3+1)
expect(byte_at(rx, 10)).to_equal(64)      # 0x40
expect(byte_at(rx, 11)).to_equal(80)      # 0x50

native_udp_close(cli)
native_udp_close(srv)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
