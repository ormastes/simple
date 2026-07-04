# P256 Ecdhe Handshake Secret Specification

> 1. sc push

<!-- sdn-diagram:id=p256_ecdhe_handshake_secret_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=p256_ecdhe_handshake_secret_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

p256_ecdhe_handshake_secret_spec -> std
p256_ecdhe_handshake_secret_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=p256_ecdhe_handshake_secret_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# P256 Ecdhe Handshake Secret Specification

## Scenarios

### P-256 ephemeral pubkeys are 65-byte uncompressed SEC1 points

#### client pub is 65 bytes

1. sc push
   - Expected: pub_c.len().to_u64() equals `65u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Inline build of client scalar 0x31..0x50 (32 bytes BE).
var sc: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc.push((0x31u8 + i.to_u8()))
    i = i + 1u64
val pub_c = p256_keypair_pub(sc)
expect(pub_c.len().to_u64()).to_equal(65u64)
```

</details>

#### server pub is 65 bytes

1. sc push
   - Expected: pub_s.len().to_u64() equals `65u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Inline build of server scalar 0x91..0xb0 (32 bytes BE).
var sc: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_s = p256_keypair_pub(sc)
expect(pub_s.len().to_u64()).to_equal(65u64)
```

</details>

### P-256 ECDHE produces a symmetric 32-byte shared X

#### client_priv * server_pub yields 32 bytes

1. sc c push
2. sc s push
   - Expected: sh_c.len().to_u64() equals `32u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_s = p256_keypair_pub(sc_s)
val sh_c = p256_ecdh_shared_x(sc_c, pub_s)
expect(sh_c.len().to_u64()).to_equal(32u64)
```

</details>

#### server_priv * client_pub yields 32 bytes

1. sc c push
2. sc s push
   - Expected: sh_s.len().to_u64() equals `32u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_c = p256_keypair_pub(sc_c)
val sh_s = p256_ecdh_shared_x(sc_s, pub_c)
expect(sh_s.len().to_u64()).to_equal(32u64)
```

</details>

#### client and server agree byte-for-byte on shared X

1. sc c push
2. sc s push
3. var equal: bool = sh c len
   - Expected: equal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_c = p256_keypair_pub(sc_c)
val pub_s = p256_keypair_pub(sc_s)
val sh_c = p256_ecdh_shared_x(sc_c, pub_s)
val sh_s = p256_ecdh_shared_x(sc_s, pub_c)
# Byte-equal check (avoid fn-call helper for the same regression
# surface; inline the loop).
var equal: bool = sh_c.len() == sh_s.len()
var j: u64 = 0u64
while equal and j < sh_c.len():
    if sh_c[j] != sh_s[j]:
        equal = false
    j = j + 1u64
expect(equal).to_equal(true)
```

</details>

### tls13_compute_handshake_secrets fed with P-256 shared X

#### yields 32-byte handshake_secret + 32-byte hs traffic secrets

1. sc c push
2. sc s push
3. seed push
4. var t = transcript new
5. t = transcript add
   - Expected: secrets.handshake_secret.len().to_u64() equals `32u64`
   - Expected: secrets.client_hs_traffic.len().to_u64() equals `32u64`
   - Expected: secrets.server_hs_traffic.len().to_u64() equals `32u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_s = p256_keypair_pub(sc_s)
val sh_c = p256_ecdh_shared_x(sc_c, pub_s)
# Build a synthetic transcript inline.
var seed: [u8] = []
var k: u64 = 0u64
while k < 64u64:
    seed.push((k.to_u8() ^ 0x5au8))
    k = k + 1u64
var t = transcript_new()
t = transcript_add(t, seed)
val secrets = tls13_compute_handshake_secrets(sh_c, t)
expect(secrets.handshake_secret.len().to_u64()).to_equal(32u64)
expect(secrets.client_hs_traffic.len().to_u64()).to_equal(32u64)
expect(secrets.server_hs_traffic.len().to_u64()).to_equal(32u64)
```

</details>

#### client and server derive byte-identical handshake_secret

1. sc c push
2. sc s push
3. seed push
4. var t1 = transcript new
5. t1 = transcript add
6. var t2 = transcript new
7. t2 = transcript add
8. var equal: bool = secrets c handshake secret len
   - Expected: equal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_c = p256_keypair_pub(sc_c)
val pub_s = p256_keypair_pub(sc_s)
val sh_c = p256_ecdh_shared_x(sc_c, pub_s)
val sh_s = p256_ecdh_shared_x(sc_s, pub_c)
var seed: [u8] = []
var k: u64 = 0u64
while k < 64u64:
    seed.push((k.to_u8() ^ 0x5au8))
    k = k + 1u64
var t1 = transcript_new()
t1 = transcript_add(t1, seed)
var t2 = transcript_new()
t2 = transcript_add(t2, seed)
val secrets_c = tls13_compute_handshake_secrets(sh_c, t1)
val secrets_s = tls13_compute_handshake_secrets(sh_s, t2)
var equal: bool = secrets_c.handshake_secret.len() == secrets_s.handshake_secret.len()
var j: u64 = 0u64
while equal and j < secrets_c.handshake_secret.len():
    if secrets_c.handshake_secret[j] != secrets_s.handshake_secret[j]:
        equal = false
    j = j + 1u64
expect(equal).to_equal(true)
```

</details>

#### client and server derive byte-identical client_hs_traffic

1. sc c push
2. sc s push
3. seed push
4. var t1 = transcript new
5. t1 = transcript add
6. var t2 = transcript new
7. t2 = transcript add
8. var equal: bool = secrets c client hs traffic len
   - Expected: equal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_c = p256_keypair_pub(sc_c)
val pub_s = p256_keypair_pub(sc_s)
val sh_c = p256_ecdh_shared_x(sc_c, pub_s)
val sh_s = p256_ecdh_shared_x(sc_s, pub_c)
var seed: [u8] = []
var k: u64 = 0u64
while k < 64u64:
    seed.push((k.to_u8() ^ 0x5au8))
    k = k + 1u64
var t1 = transcript_new()
t1 = transcript_add(t1, seed)
var t2 = transcript_new()
t2 = transcript_add(t2, seed)
val secrets_c = tls13_compute_handshake_secrets(sh_c, t1)
val secrets_s = tls13_compute_handshake_secrets(sh_s, t2)
var equal: bool = secrets_c.client_hs_traffic.len() == secrets_s.client_hs_traffic.len()
var j: u64 = 0u64
while equal and j < secrets_c.client_hs_traffic.len():
    if secrets_c.client_hs_traffic[j] != secrets_s.client_hs_traffic[j]:
        equal = false
    j = j + 1u64
expect(equal).to_equal(true)
```

</details>

#### client and server derive byte-identical server_hs_traffic

1. sc c push
2. sc s push
3. seed push
4. var t1 = transcript new
5. t1 = transcript add
6. var t2 = transcript new
7. t2 = transcript add
8. var equal: bool = secrets c server hs traffic len
   - Expected: equal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_c = p256_keypair_pub(sc_c)
val pub_s = p256_keypair_pub(sc_s)
val sh_c = p256_ecdh_shared_x(sc_c, pub_s)
val sh_s = p256_ecdh_shared_x(sc_s, pub_c)
var seed: [u8] = []
var k: u64 = 0u64
while k < 64u64:
    seed.push((k.to_u8() ^ 0x5au8))
    k = k + 1u64
var t1 = transcript_new()
t1 = transcript_add(t1, seed)
var t2 = transcript_new()
t2 = transcript_add(t2, seed)
val secrets_c = tls13_compute_handshake_secrets(sh_c, t1)
val secrets_s = tls13_compute_handshake_secrets(sh_s, t2)
var equal: bool = secrets_c.server_hs_traffic.len() == secrets_s.server_hs_traffic.len()
var j: u64 = 0u64
while equal and j < secrets_c.server_hs_traffic.len():
    if secrets_c.server_hs_traffic[j] != secrets_s.server_hs_traffic[j]:
        equal = false
    j = j + 1u64
expect(equal).to_equal(true)
```

</details>

### tls13_traffic_keys over P-256-derived handshake-traffic secrets

#### client AES-128 key is 16 bytes and IV is 12 bytes

1. sc c push
2. sc s push
3. seed push
4. var t = transcript new
5. t = transcript add
   - Expected: tk.key.len().to_u64() equals `16u64`
   - Expected: tk.iv.len().to_u64() equals `12u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_s = p256_keypair_pub(sc_s)
val sh_c = p256_ecdh_shared_x(sc_c, pub_s)
var seed: [u8] = []
var k: u64 = 0u64
while k < 64u64:
    seed.push((k.to_u8() ^ 0x5au8))
    k = k + 1u64
var t = transcript_new()
t = transcript_add(t, seed)
val secrets = tls13_compute_handshake_secrets(sh_c, t)
val tk = tls13_traffic_keys(secrets.client_hs_traffic)
expect(tk.key.len().to_u64()).to_equal(16u64)
expect(tk.iv.len().to_u64()).to_equal(12u64)
```

</details>

#### server AES-128 key is 16 bytes and IV is 12 bytes

1. sc c push
2. sc s push
3. seed push
4. var t = transcript new
5. t = transcript add
   - Expected: tk.key.len().to_u64() equals `16u64`
   - Expected: tk.iv.len().to_u64() equals `12u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_s = p256_keypair_pub(sc_s)
val sh_c = p256_ecdh_shared_x(sc_c, pub_s)
var seed: [u8] = []
var k: u64 = 0u64
while k < 64u64:
    seed.push((k.to_u8() ^ 0x5au8))
    k = k + 1u64
var t = transcript_new()
t = transcript_add(t, seed)
val secrets = tls13_compute_handshake_secrets(sh_c, t)
val tk = tls13_traffic_keys(secrets.server_hs_traffic)
expect(tk.key.len().to_u64()).to_equal(16u64)
expect(tk.iv.len().to_u64()).to_equal(12u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/p256_ecdhe_handshake_secret_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- P-256 ephemeral pubkeys are 65-byte uncompressed SEC1 points
- P-256 ECDHE produces a symmetric 32-byte shared X
- tls13_compute_handshake_secrets fed with P-256 shared X
- tls13_traffic_keys over P-256-derived handshake-traffic secrets

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
