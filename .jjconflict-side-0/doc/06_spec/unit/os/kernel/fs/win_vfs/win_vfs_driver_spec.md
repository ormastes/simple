# Win-VFS Kernel Driver Specification

> Mount at `/win`, readdir, read title bytes, destroy→ENOENT, ACL-denied→EACCES.

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
| Source | `test/unit/os/kernel/fs/win_vfs/win_vfs_driver_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mount at `/win`, readdir, read title bytes, destroy→ENOENT, ACL-denied→EACCES.
Grep sentinel: driver imports from shared encoder; no inlined encoding in
`src/os/kernel/fs/win_vfs/`.

## Scenarios

### Win-VFS kernel driver

### mount

#### AC-4: mount at /win succeeds

- AC-4: mount at /win succeeds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: mount at /win succeeds")
val drv = win_vfs_make_for_test()
val result = drv.mount("win", "")
expect result.ok to_equal true
```

</details>

#### AC-4: register_win_vfs publishes driver under /win

- AC-4: register_win_vfs publishes driver under /win


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: register_win_vfs publishes driver under /win")
val status = register_win_vfs()
expect status.ok to_equal true
expect status.value to_equal "/win"
```

</details>

### readdir

#### AC-4: /win lists <app> directories

- AC-4: /win lists <app> directories


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: /win lists <app> directories")
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

- AC-4: /win/<app>/<wid> lists schema entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: /win/<app>/<wid> lists schema entries")
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

- AC-4: read(/banking/1/title) returns window title bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: read(/banking/1/title) returns window title bytes")
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

- AC-4: after destroy, open returns ENOENT


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: after destroy, open returns ENOENT")
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

- AC-4: denied caller gets EACCES on open


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: denied caller gets EACCES on open")
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

- AC-4: win_vfs_driver.spl imports from common/win_fs/fs_encoder


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: win_vfs_driver.spl imports from common/win_fs/fs_encoder")
val source = read_file("src/os/kernel/fs/win_vfs/win_vfs_driver.spl")
expect source to_contain "use lib.common.win_fs.fs_encoder"
```

</details>

#### AC-4: win_vfs_driver.spl imports from common/win_fs/acl

- AC-4: win_vfs_driver.spl imports from common/win_fs/acl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: win_vfs_driver.spl imports from common/win_fs/acl")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `64b8cb31b725e8577b7b0cc8a329cc1912f2b9bf022b88a6e6bd1589aaef0040`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `64b8cb31b725e8577b7b0cc8a329cc1912f2b9bf022b88a6e6bd1589aaef0040`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `64b8cb31b725e8577b7b0cc8a329cc1912f2b9bf022b88a6e6bd1589aaef0040`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/fs/win_vfs/win_vfs_driver_spec.spl
mirror: doc/06_spec/unit/os/kernel/fs/win_vfs/win_vfs_driver_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/fs/win_vfs/win_vfs_driver_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/fs/win_vfs/win_vfs_driver_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/fs/win_vfs/win_vfs_driver_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: mount at /win succeeds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/fs/win_vfs/win_vfs_driver_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: register_win_vfs publishes driver under /win' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/fs/win_vfs/win_vfs_driver_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: /win lists <app> directories' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
