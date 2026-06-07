# Win-FS ACL Specification

> Exercises `acl_check(rec, token, op)` — deny when token id_path lacks required

<!-- sdn-diagram:id=acl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=acl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

acl_spec -> std
acl_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=acl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Win-FS ACL Specification

Exercises `acl_check(rec, token, op)` — deny when token id_path lacks required

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Red (no impl yet) |
| Source | `test/01_unit/lib/common/win_fs/acl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises `acl_check(rec, token, op)` — deny when token id_path lacks required
prefix; allow when it matches.

## Scenarios

### Win-FS ACL

### open()

#### AC-2: allows open when token id_path matches required prefix

1. geometry: Rect
2. buffer ref: BufferRef
3. acl id path: id path intern
4. id path: id path intern
5. expect acl check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = WindowRecord(
    wid: 1, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 0, bytes: 0),
    acl_id_path: id_path_intern("id.user.banking.view"))
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.banking"),
    level: AuthorityLevel.Sensitive,
    principal: principal)
expect acl_check(rec, token, FsOp.Open) to_equal true
```

</details>

#### AC-2: denies open when token id_path lacks required prefix

1. geometry: Rect
2. buffer ref: BufferRef
3. acl id path: id path intern
4. id path: id path intern
5. expect acl check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = WindowRecord(
    wid: 1, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 0, bytes: 0),
    acl_id_path: id_path_intern("id.user.banking.view"))
val principal = Principal(kind: PrincipalKind.Local, id: "eve")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.mail"),
    level: AuthorityLevel.Internal,
    principal: principal)
expect acl_check(rec, token, FsOp.Open) to_equal false
```

</details>

#### AC-2: revoked token is denied

1. geometry: Rect
2. buffer ref: BufferRef
3. acl id path: id path intern
4. id path: id path intern
5. expect acl check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = WindowRecord(
    wid: 1, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 0, bytes: 0),
    acl_id_path: id_path_intern("id.user.banking.view"))
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken.mock_with_trust(
    id_path: id_path_intern("id.user.banking.view"),
    level: AuthorityLevel.Sensitive,
    principal: principal,
    trust: TrustSource.Revoked)
expect acl_check(rec, token, FsOp.Open) to_equal false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
