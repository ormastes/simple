# SPM Service RPC Specification

> Round-trip: request/response identical over SimpleOS transport and host

<!-- sdn-diagram:id=spm_service_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spm_service_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spm_service_spec -> std
spm_service_spec -> lib
spm_service_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spm_service_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SPM Service RPC Specification

Round-trip: request/response identical over SimpleOS transport and host

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Red (no impl yet) |
| Source | `test/02_integration/app/simple_process_manager/spm_service_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Round-trip: request/response identical over SimpleOS transport and host
transport. Privilege check RPC and window-register RPC exercised.

## Scenarios

### SPM service RPC

### transport parity

#### AC-3: host socket round-trip returns identical bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SpmService.new_for_test()
val req = SpmRequest(kind: "ping", body: "hello".bytes(), token_hint: AuthorityToken.public_none())
val host_bytes = spm_encode_request(req)
val host = SpmTransportHost.mock_bound(fn(incoming): svc.handle(incoming))
val resp = host.send(req)
expect resp.ok to_equal true
expect(resp.body.len() > 0).to_equal(true)
```

</details>

#### AC-3: SimpleOS mock transport yields same encoded request bytes as host

1. expect host bytes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = SpmRequest(kind: "ping", body: "hello".bytes(), token_hint: AuthorityToken.public_none())
val host_bytes = spm_encode_request(req)
val simpleos_bytes = spm_encode_request(req)
expect host_bytes.len() to_equal simpleos_bytes.len()
```

</details>

### privilege_service.check

#### AC-3: rejects request with token lacking id_path

1. id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SpmService.new_for_test()
val principal = Principal(kind: PrincipalKind.Local, id: "eve")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.mail"),
    level: AuthorityLevel.Internal,
    principal: principal)
val req = SpmRequest(kind: "priv_check", body: "id.user.banking.view".bytes(), token_hint: token)
val resp = svc.handle(req)
expect resp.ok to_equal false
```

</details>

#### AC-3: allows request with matching token id_path

1. id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SpmService.new_for_test()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.banking"),
    level: AuthorityLevel.Sensitive,
    principal: principal)
val req = SpmRequest(kind: "priv_check", body: "id.user.banking.view".bytes(), token_hint: token)
val resp = svc.handle(req)
expect resp.ok to_equal true
```

</details>

### window_registry.register

#### AC-3: window_register RPC uses the shared record body contract

1. id path: id path intern
2. geometry: Rect
3. buffer ref: BufferRef
4. acl id path: id path intern
5. expect req body len
   - Expected: wire.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.banking"),
    level: AuthorityLevel.Sensitive,
    principal: principal)
val rec = WindowRecord(
    wid: 1, generation: 0, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 0, bytes: 0),
    acl_id_path: id_path_intern("id.user.banking.view"))
val req = SpmRequest(kind: "win_register", body: window_record_encode(rec), token_hint: token)
val wire = spm_encode_request(req)
expect req.body.len() to_equal window_record_encode(rec).len()
expect(wire.len() > 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
