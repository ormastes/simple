# Win-VFS Kernel Driver Specification

> Mount at `/win`, readdir, read title bytes, destroy→ENOENT, ACL-denied→EACCES.

<!-- sdn-diagram:id=win_vfs_driver_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=win_vfs_driver_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

win_vfs_driver_spec -> std
win_vfs_driver_spec -> lib
win_vfs_driver_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=win_vfs_driver_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Win-VFS Kernel Driver Specification

Mount at `/win`, readdir, read title bytes, destroy→ENOENT, ACL-denied→EACCES.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Red (no impl yet) |
| Source | `test/01_unit/os/kernel/fs/win_vfs/win_vfs_driver_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Mount at `/win`, readdir, read title bytes, destroy→ENOENT, ACL-denied→EACCES.
Grep sentinel: driver imports from shared encoder; no inlined encoding in
`src/os/kernel/fs/win_vfs/`.

## Scenarios

### Win-VFS kernel driver

### mount

#### AC-4: mount at /win succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = win_vfs_make_for_test()
val result = drv.mount("win", "")
expect result.ok to_equal true
```

</details>

#### AC-4: register_win_vfs publishes driver under /win

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = register_win_vfs()
expect status.ok to_equal true
expect status.value to_equal "/win"
```

</details>

### readdir

#### AC-4: /win lists <app> directories

1. drv mount
2. geometry: Rect
3. buffer ref: BufferRef
4. acl id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = win_vfs_make_for_test()
drv.mount("win", "")
drv.test_insert(WindowRecord(
    wid: 1, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 0, bytes: 0),
    acl_id_path: id_path_intern("id.user.public")))
val result = drv.readdir("/")
expect result.ok to_equal true
val names = drv.test_entry_names(result.value)
expect names to_contain "banking"
```

</details>

#### AC-4: /win/<app>/<wid> lists schema entries

1. drv mount
2. geometry: Rect
3. buffer ref: BufferRef
4. acl id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = win_vfs_make_for_test()
drv.mount("win", "")
drv.test_insert(WindowRecord(
    wid: 1, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 0, bytes: 0),
    acl_id_path: id_path_intern("id.user.public")))
val result = drv.readdir("/banking/1")
expect result.ok to_equal true
val names = drv.test_entry_names(result.value)
expect names to_contain "title"
expect names to_contain "state"
expect names to_contain "geometry"
```

</details>

### read title

#### AC-4: read(/banking/1/title) returns window title bytes

1. drv mount
2. geometry: Rect
3. buffer ref: BufferRef
4. acl id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = win_vfs_make_for_test()
drv.mount("win", "")
drv.test_insert(WindowRecord(
    wid: 1, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 0, bytes: 0),
    acl_id_path: id_path_intern("id.user.public")))
val fd = drv.open("/banking/1/title", FileFlags.read_only())
expect fd.ok to_equal true
val data = drv.read(fd.value, 64)
expect data.ok to_equal true
val text = data.value.as_text()
expect text to_equal "Acct"
```

</details>

### destroy → ENOENT

#### AC-4: after destroy, open returns ENOENT

1. drv mount
2. geometry: Rect
3. buffer ref: BufferRef
4. acl id path: id path intern
5. drv test destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = win_vfs_make_for_test()
drv.mount("win", "")
drv.test_insert(WindowRecord(
    wid: 1, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 0, bytes: 0),
    acl_id_path: id_path_intern("id.user.public")))
drv.test_destroy(1)
val fd = drv.open("/banking/1/title", FileFlags.read_only())
expect fd.ok to_equal false
expect fd.error to_contain "ENOENT"
```

</details>

### ACL denial

#### AC-4: denied caller gets EACCES on open

1. drv mount
2. geometry: Rect
3. buffer ref: BufferRef
4. acl id path: id path intern
5. id path: id path intern
6. drv test set current token


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = win_vfs_make_for_test()
drv.mount("win", "")
drv.test_insert(WindowRecord(
    wid: 1, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 0, bytes: 0),
    acl_id_path: id_path_intern("id.user.banking.view")))
val principal = Principal(kind: PrincipalKind.Local, id: "eve")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.mail"),
    level: AuthorityLevel.Internal,
    principal: principal)
drv.test_set_current_token(token)
val fd = drv.open("/banking/1/title", FileFlags.read_only())
expect fd.ok to_equal false
expect fd.error to_contain "EACCES"
```

</details>

### grep sentinel (no inlined encoding)

#### AC-4: win_vfs_driver.spl imports from common/win_fs/fs_encoder

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/kernel/fs/win_vfs/win_vfs_driver.spl")
expect source to_contain "use lib.common.win_fs.fs_encoder"
```

</details>

#### AC-4: win_vfs_driver.spl imports from common/win_fs/acl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/kernel/fs/win_vfs/win_vfs_driver.spl")
expect source to_contain "use lib.common.win_fs.acl"
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
