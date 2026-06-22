# WM ↔ SPM client RPC parity Specification

> Same encoded bytes for the same request on both transports.

<!-- sdn-diagram:id=wm_spm_client_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_spm_client_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_spm_client_spec -> std
wm_spm_client_spec -> lib
wm_spm_client_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_spm_client_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM ↔ SPM client RPC parity Specification

Same encoded bytes for the same request on both transports.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Red (no impl yet) |
| Source | `test/01_unit/os/compositor/wm_spm_client_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Same encoded bytes for the same request on both transports.

## Scenarios

### wm_spm_client

### RPC payload parity

#### AC-3: register_window produces identical bytes on both transports

1. geometry: Rect
2. buffer ref: BufferRef
3. acl id path: id path intern
4. expect host bytes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = WindowRecord(
    wid: 42, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 10, y: 20, w: 800, h: 600),
    buffer_ref: BufferRef(kind: "shm", handle: 7, bytes: 4096),
    acl_id_path: id_path_intern("id.user.banking.view"))
val client_host = WmSpmClient.new(SpmTransportHost.mock_loopback())
val client_os = WmSpmClient.new(SpmTransportMock.new())
val host_bytes = client_host.test_encode_register(rec)
val os_bytes = client_os.test_encode_register(rec)
expect host_bytes.len() to_equal os_bytes.len()
```

</details>

#### AC-3: free encoder matches client-encoded bytes

1. geometry: Rect
2. buffer ref: BufferRef
3. acl id path: id path intern
4. expect direct len


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = WindowRecord(
    wid: 42, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 10, y: 20, w: 800, h: 600),
    buffer_ref: BufferRef(kind: "shm", handle: 7, bytes: 4096),
    acl_id_path: id_path_intern("id.user.banking.view"))
val direct = encode_register_window(rec)
val client = WmSpmClient.new(SpmTransportHost.mock_loopback())
val via_client = client.test_encode_register(rec)
expect direct.len() to_equal via_client.len()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
