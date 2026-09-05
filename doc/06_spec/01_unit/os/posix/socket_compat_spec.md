# POSIX socket_compat pure helpers

> Covers the address helpers and constant contract. The IPC path

<!-- sdn-diagram:id=socket_compat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=socket_compat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

socket_compat_spec -> std
socket_compat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=socket_compat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# POSIX socket_compat pure helpers

Covers the address helpers and constant contract. The IPC path

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE3-G14 |
| Category | POSIX shim |
| Status | Active |
| Source | `test/01_unit/os/posix/socket_compat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Covers the address helpers and constant contract. The IPC path
(`posix_socket`, `posix_bind`, …) requires netstack to be running
and is exercised in system tests.

## Scenarios

### sockaddr_in
_IPv4 address packing matches little-endian wire order of octets._

#### packs four octets into the addr field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = sockaddr_in(8080u16, 127u8, 0u8, 0u8, 1u8)
expect a.family.to_equal(AF_INET)
expect a.port.to_equal(8080u16)
expect a.addr.to_equal(0x0100007Fu32)
```

</details>

#### INADDR_ANY has addr=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = sockaddr_any(22u16)
expect a.family.to_equal(AF_INET)
expect a.port.to_equal(22u16)
expect a.addr.to_equal(0u32)
```

</details>

### socket constants
_Pin POSIX socket-type constants so ABI drift fails here first._

#### AF_INET is 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect AF_INET.to_equal(2)
```

</details>

#### SOCK_STREAM is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect SOCK_STREAM.to_equal(1)
```

</details>

#### SOCK_DGRAM is 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect SOCK_DGRAM.to_equal(2)
```

</details>

### AI CLI socket network grants
_Socket boundary operations must deny ungranted endpoints before netstack IPC._

#### denies connect endpoints outside the active manifest grants

1. fd table init
   - Expected: fd_set(3, 4, 0, 42u64) equals `0`
2. set ai cli socket manifest for test
   - Expected: denied equals `-13`
3. clear ai cli socket manifest for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
expect(fd_set(3, 4, 0, 42u64)).to_equal(0)
set_ai_cli_socket_manifest_for_test(codex_cli_smoke_manifest())
val denied = posix_connect(3, sockaddr_in(443u16, 127u8, 0u8, 0u8, 1u8))
expect(denied).to_equal(-13)
clear_ai_cli_socket_manifest_for_test()
```

</details>

#### denies bind endpoints outside the active manifest grants

1. fd table init
   - Expected: fd_set(3, 4, 0, 42u64) equals `0`
2. set ai cli socket manifest for test
   - Expected: denied equals `-13`
3. clear ai cli socket manifest for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
expect(fd_set(3, 4, 0, 42u64)).to_equal(0)
set_ai_cli_socket_manifest_for_test(codex_cli_smoke_manifest())
val denied = posix_bind(3, sockaddr_any(3000u16))
expect(denied).to_equal(-13)
clear_ai_cli_socket_manifest_for_test()
```

</details>

#### denies listen without a granted bound endpoint

1. fd table init
   - Expected: fd_set(3, 4, 0, 42u64) equals `0`
2. set ai cli socket manifest for test
   - Expected: denied equals `-13`
3. clear ai cli socket manifest for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
expect(fd_set(3, 4, 0, 42u64)).to_equal(0)
set_ai_cli_socket_manifest_for_test(codex_cli_smoke_manifest())
val denied = posix_listen(3, 16)
expect(denied).to_equal(-13)
clear_ai_cli_socket_manifest_for_test()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
