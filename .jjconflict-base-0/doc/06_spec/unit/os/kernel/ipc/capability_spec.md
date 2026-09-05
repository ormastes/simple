# Capability Enforcement Specification

> Tests for the capability enforcement manager. Validates grant/revoke lifecycle, pledge() monotonic restriction, unveil() file path restriction, and file access checking with prefix matching.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Capability Enforcement Specification

Tests for the capability enforcement manager. Validates grant/revoke lifecycle, pledge() monotonic restriction, unveil() file path restriction, and file access checking with prefix matching.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-007 |
| Category | Runtime |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/unit/os/kernel/ipc/capability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the capability enforcement manager. Validates grant/revoke lifecycle,
pledge() monotonic restriction, unveil() file path restriction, and file access
checking with prefix matching.

## Scenarios

### CapabilityManager

### construction

#### creates with empty records

- creates with empty records
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with empty records")
val mgr = CapabilityManager.new()
val task = TaskId(id: 1)
val result = mgr.check(task, CapabilityKind.ProcessSpawn)
expect(result).to_equal(false)
```

</details>

### init_task

#### initializes a task with given capabilities

- initializes a task with given capabilities
   - Expected: has is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes a task with given capabilities")
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
val token = CapabilityToken(
    kind: CapabilityKind.ProcessSpawn,
    generation: 1,
    owner: 1
)
val caps = CapabilitySet(caps: [token], is_pledged: false)
mgr.init_task(task, caps)
val has = mgr.check(task, CapabilityKind.ProcessSpawn)
expect(has).to_equal(true)
```

</details>

#### initializes a task with empty capabilities

- initializes a task with empty capabilities
   - Expected: has is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes a task with empty capabilities")
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
mgr.init_task(task, CapabilitySet.empty())
val has = mgr.check(task, CapabilityKind.ProcessSpawn)
expect(has).to_equal(false)
```

</details>

#### lowers non-init ambient full sets to deny-all

- lowers non-init ambient full sets to deny-all
   - Expected: mgr.check(task, CapabilityKind.ProcessSpawn) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers non-init ambient full sets to deny-all")
var mgr = CapabilityManager.new()
val task = TaskId(id: 2)
mgr.init_task(task, CapabilitySet.full())
expect(mgr.check(task, CapabilityKind.ProcessSpawn)).to_equal(false)
```

</details>

### CapabilityManager check

#### returns false for unregistered task

- returns false for unregistered task
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for unregistered task")
val mgr = CapabilityManager.new()
val result = mgr.check(TaskId(id: 999), CapabilityKind.SystemReboot)
expect(result).to_equal(false)
```

</details>

#### returns true when task has matching capability

- returns true when task has matching capability
   - Expected: mgr.check(task, CapabilityKind.NetRaw) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true when task has matching capability")
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
val token = CapabilityToken(
    kind: CapabilityKind.NetRaw,
    generation: 1,
    owner: 1
)
mgr.init_task(task, CapabilitySet(caps: [token], is_pledged: false))
expect(mgr.check(task, CapabilityKind.NetRaw)).to_equal(true)
```

</details>

#### returns false for non-matching capability kind

- returns false for non-matching capability kind
   - Expected: mgr.check(task, CapabilityKind.SystemReboot) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-matching capability kind")
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
val token = CapabilityToken(
    kind: CapabilityKind.NetRaw,
    generation: 1,
    owner: 1
)
mgr.init_task(task, CapabilitySet(caps: [token], is_pledged: false))
expect(mgr.check(task, CapabilityKind.SystemReboot)).to_equal(false)
```

</details>

#### allows dataset rights by object and generation

- allows dataset rights by object and generation
   - Expected: mgr.check(task, CapabilityKind.SharedDataset(object_id: 7u64, generation: 3u64, rights: CAP_RIGHT_READ)) is true
   - Expected: mgr.check(task, CapabilityKind.SharedDataset(object_id: 7u64, generation: 3u64, rights: CAP_RIGHT_MAP)) is true
   - Expected: mgr.check(task, CapabilityKind.SharedDataset(object_id: 7u64, generation: 4u64, rights: CAP_RIGHT_READ)) is false
   - Expected: mgr.check(task, CapabilityKind.SharedDataset(object_id: 8u64, generation: 3u64, rights: CAP_RIGHT_READ)) is false
   - Expected: mgr.check(task, CapabilityKind.SharedDataset(object_id: 7u64, generation: 3u64, rights: CAP_RIGHT_DATASET_BUILD)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows dataset rights by object and generation")
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
val token = CapabilityToken(
    kind: CapabilityKind.SharedDataset(object_id: 7u64, generation: 3u64, rights: CAP_RIGHT_READ | CAP_RIGHT_MAP | CAP_RIGHT_ADMIN),
    generation: 3u64,
    owner: 1u64
)
mgr.init_task(task, CapabilitySet(caps: [token], is_pledged: false))

expect(mgr.check(task, CapabilityKind.SharedDataset(object_id: 7u64, generation: 3u64, rights: CAP_RIGHT_READ))).to_equal(true)
expect(mgr.check(task, CapabilityKind.SharedDataset(object_id: 7u64, generation: 3u64, rights: CAP_RIGHT_MAP))).to_equal(true)
expect(mgr.check(task, CapabilityKind.SharedDataset(object_id: 7u64, generation: 4u64, rights: CAP_RIGHT_READ))).to_equal(false)
expect(mgr.check(task, CapabilityKind.SharedDataset(object_id: 8u64, generation: 3u64, rights: CAP_RIGHT_READ))).to_equal(false)
expect(mgr.check(task, CapabilityKind.SharedDataset(object_id: 7u64, generation: 3u64, rights: CAP_RIGHT_DATASET_BUILD))).to_equal(false)
```

</details>

#### allows process queue submit and receive rights by generation

- allows process queue submit and receive rights by generation
   - Expected: mgr.check(task, CapabilityKind.ProcessQueue(queue_id: 11u64, generation: 5u64, rights: CAP_RIGHT_QUEUE_SUBMIT)) is true
   - Expected: mgr.check(task, CapabilityKind.ProcessQueue(queue_id: 11u64, generation: 5u64, rights: CAP_RIGHT_QUEUE_RECV)) is true
   - Expected: mgr.check(task, CapabilityKind.ProcessQueue(queue_id: 11u64, generation: 6u64, rights: CAP_RIGHT_QUEUE_RECV)) is false
   - Expected: mgr.check(task, CapabilityKind.ProcessQueue(queue_id: 12u64, generation: 5u64, rights: CAP_RIGHT_QUEUE_RECV)) is false
   - Expected: mgr.check(task, CapabilityKind.ProcessQueue(queue_id: 11u64, generation: 5u64, rights: CAP_RIGHT_ADMIN)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows process queue submit and receive rights by generation")
var mgr = CapabilityManager.new()
val task = TaskId(id: 2)
val token = CapabilityToken(
    kind: CapabilityKind.ProcessQueue(queue_id: 11u64, generation: 5u64, rights: CAP_RIGHT_QUEUE_SUBMIT | CAP_RIGHT_QUEUE_RECV),
    generation: 5u64,
    owner: 2u64
)
mgr.init_task(task, CapabilitySet(caps: [token], is_pledged: false))

expect(mgr.check(task, CapabilityKind.ProcessQueue(queue_id: 11u64, generation: 5u64, rights: CAP_RIGHT_QUEUE_SUBMIT))).to_equal(true)
expect(mgr.check(task, CapabilityKind.ProcessQueue(queue_id: 11u64, generation: 5u64, rights: CAP_RIGHT_QUEUE_RECV))).to_equal(true)
expect(mgr.check(task, CapabilityKind.ProcessQueue(queue_id: 11u64, generation: 6u64, rights: CAP_RIGHT_QUEUE_RECV))).to_equal(false)
expect(mgr.check(task, CapabilityKind.ProcessQueue(queue_id: 12u64, generation: 5u64, rights: CAP_RIGHT_QUEUE_RECV))).to_equal(false)
expect(mgr.check(task, CapabilityKind.ProcessQueue(queue_id: 11u64, generation: 5u64, rights: CAP_RIGHT_ADMIN))).to_equal(false)
```

</details>

### CapabilityManager grant

#### grants capability from source to target

- grants capability from source to target
   - Expected: ok is true
   - Expected: mgr.check(dst, CapabilityKind.ProcessSpawn) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("grants capability from source to target")
var mgr = CapabilityManager.new()
val src = TaskId(id: 1)
val dst = TaskId(id: 2)
val token = CapabilityToken(
    kind: CapabilityKind.ProcessSpawn,
    generation: 1,
    owner: 1,
    token_id: 1u64,
    parent_token_id: 0u64,
    depth: 2
)
mgr.init_task(src, CapabilitySet(caps: [token], is_pledged: false))
mgr.init_task(dst, CapabilitySet.empty())

val ok = mgr.grant(src, dst, token)
expect(ok).to_equal(true)
expect(mgr.check(dst, CapabilityKind.ProcessSpawn)).to_equal(true)
```

</details>

#### fails to grant if source does not hold capability

- fails to grant if source does not hold capability
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails to grant if source does not hold capability")
var mgr = CapabilityManager.new()
val src = TaskId(id: 1)
val dst = TaskId(id: 2)
mgr.init_task(src, CapabilitySet.empty())
mgr.init_task(dst, CapabilitySet.empty())

val token = CapabilityToken(
    kind: CapabilityKind.SystemReboot,
    generation: 1,
    owner: 1
)
val ok = mgr.grant(src, dst, token)
expect(ok).to_equal(false)
```

</details>

### CapabilityManager revoke

#### revokes a capability token

- revokes a capability token
   - Expected: revoked is true
   - Expected: mgr.check(task, CapabilityKind.NetRaw) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("revokes a capability token")
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
val token = CapabilityToken(
    kind: CapabilityKind.NetRaw,
    generation: 1,
    owner: 1
)
mgr.init_task(task, CapabilitySet(caps: [token], is_pledged: false))

val revoked = mgr.revoke(token)
expect(revoked).to_equal(true)
# After revoke, the capability should be gone
expect(mgr.check(task, CapabilityKind.NetRaw)).to_equal(false)
```

</details>

#### revoke returns false for unknown token

- revoke returns false for unknown token
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("revoke returns false for unknown token")
var mgr = CapabilityManager.new()
val token = CapabilityToken(
    kind: CapabilityKind.SystemMount,
    generation: 99,
    owner: 999
)
val result = mgr.revoke(token)
expect(result).to_equal(false)
```

</details>

### CapabilityManager pledge

#### restricts capabilities to allowed list

- restricts capabilities to allowed list
   - Expected: mgr.check(task, CapabilityKind.ProcessSpawn) is true
   - Expected: mgr.check(task, CapabilityKind.SystemReboot) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restricts capabilities to allowed list")
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
val spawn_token = CapabilityToken(
    kind: CapabilityKind.ProcessSpawn,
    generation: 1,
    owner: 1
)
val reboot_token = CapabilityToken(
    kind: CapabilityKind.SystemReboot,
    generation: 2,
    owner: 1
)
mgr.init_task(task, CapabilitySet(
    caps: [spawn_token, reboot_token],
    is_pledged: false
))

# Pledge to only ProcessSpawn
mgr.pledge(task, [CapabilityKind.ProcessSpawn])

expect(mgr.check(task, CapabilityKind.ProcessSpawn)).to_equal(true)
expect(mgr.check(task, CapabilityKind.SystemReboot)).to_equal(false)
```

</details>

#### pledge with empty list removes all capabilities

- pledge with empty list removes all capabilities
   - Expected: mgr.check(task, CapabilityKind.NetRaw) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pledge with empty list removes all capabilities")
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
val token = CapabilityToken(
    kind: CapabilityKind.NetRaw,
    generation: 1,
    owner: 1
)
mgr.init_task(task, CapabilitySet(caps: [token], is_pledged: false))

mgr.pledge(task, [])

expect(mgr.check(task, CapabilityKind.NetRaw)).to_equal(false)
```

</details>

#### second pledge is no-op (already pledged)

- second pledge is no-op (already pledged)
   - Expected: mgr.check(task, CapabilityKind.ProcessSpawn) is true
   - Expected: mgr.check(task, CapabilityKind.ProcessSpawn) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("second pledge is no-op (already pledged)")
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
val token = CapabilityToken(
    kind: CapabilityKind.ProcessSpawn,
    generation: 1,
    owner: 1
)
mgr.init_task(task, CapabilitySet(caps: [token], is_pledged: false))

# First pledge: keep ProcessSpawn
mgr.pledge(task, [CapabilityKind.ProcessSpawn])
expect(mgr.check(task, CapabilityKind.ProcessSpawn)).to_equal(true)

# Second pledge: try to remove all - should be no-op
mgr.pledge(task, [])
# ProcessSpawn should still be present because second pledge was ignored
expect(mgr.check(task, CapabilityKind.ProcessSpawn)).to_equal(true)
```

</details>

### CapabilityManager unveil

#### before unveil, all paths are allowed

- before unveil, all paths are allowed
   - Expected: allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("before unveil, all paths are allowed")
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
mgr.init_task(task, CapabilitySet.full())
val allowed = mgr.check_file_access(task, "/any/path", "r")
expect(allowed).to_equal(true)
```

</details>

#### before unveil, file access still requires matching capability

- before unveil, file access still requires matching capability
   - Expected: mgr.check_file_access(task, "/any/path", "r") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("before unveil, file access still requires matching capability")
var mgr = CapabilityManager.new()
val task = TaskId(id: 2)
mgr.init_task(task, CapabilitySet.empty())
expect(mgr.check_file_access(task, "/any/path", "r")).to_equal(false)
```

</details>

#### before unveil, explicit file capability allows matching path

- before unveil, explicit file capability allows matching path
   - Expected: mgr.check_file_access(task, "/tmp/data.txt", "r") is true
   - Expected: mgr.check_file_access(task, "/tmp/data.txt", "w") is false
   - Expected: mgr.check_file_access(task, "/tmp/data.txt", "rw") is false
   - Expected: mgr.check_file_access(task, "/tmp/data.txt", "rz") is false
   - Expected: mgr.check_file_access(task, "/tmp2/data.txt", "r") is false
   - Expected: mgr.check_file_access(task, "/etc/passwd", "r") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("before unveil, explicit file capability allows matching path")
var mgr = CapabilityManager.new()
val task = TaskId(id: 3)
val token = CapabilityToken(
    kind: CapabilityKind.FileRead(path_prefix: "/tmp"),
    generation: 1u64,
    owner: 3u64,
    token_id: 30u64,
    parent_token_id: 0u64,
    depth: 1
)
mgr.init_task(task, CapabilitySet(caps: [token], is_pledged: false))
expect(mgr.check_file_access(task, "/tmp/data.txt", "r")).to_equal(true)
expect(mgr.check_file_access(task, "/tmp/data.txt", "w")).to_equal(false)
expect(mgr.check_file_access(task, "/tmp/data.txt", "rw")).to_equal(false)
expect(mgr.check_file_access(task, "/tmp/data.txt", "rz")).to_equal(false)
expect(mgr.check_file_access(task, "/tmp2/data.txt", "r")).to_equal(false)
expect(mgr.check_file_access(task, "/etc/passwd", "r")).to_equal(false)
```

</details>

#### after unveil, only unveiled paths are allowed

- after unveil, only unveiled paths are allowed
   - Expected: tmp_ok is true
   - Expected: etc_denied is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("after unveil, only unveiled paths are allowed")
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
mgr.init_task(task, CapabilitySet.full())

# Unveil /tmp with read permission
mgr.unveil(task, "/tmp", "r")

val tmp_ok = mgr.check_file_access(task, "/tmp/file.txt", "r")
expect(tmp_ok).to_equal(true)

val etc_denied = mgr.check_file_access(task, "/etc/passwd", "r")
expect(etc_denied).to_equal(false)
```

</details>

#### unveil supports write permission

- unveil supports write permission
   - Expected: write_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unveil supports write permission")
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
mgr.init_task(task, CapabilitySet.full())

mgr.unveil(task, "/var/log", "rw")

val write_ok = mgr.check_file_access(task, "/var/log/app.log", "w")
expect(write_ok).to_equal(true)
```

</details>

#### multiple unveil calls add entries

- multiple unveil calls add entries
   - Expected: tmp_ok is true
   - Expected: home_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple unveil calls add entries")
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
mgr.init_task(task, CapabilitySet.full())

mgr.unveil(task, "/tmp", "r")
mgr.unveil(task, "/home", "rw")

val tmp_ok = mgr.check_file_access(task, "/tmp/data", "r")
expect(tmp_ok).to_equal(true)

val home_ok = mgr.check_file_access(task, "/home/user/file", "r")
expect(home_ok).to_equal(true)
```

</details>

#### unveil denies paths not in the list

- unveil denies paths not in the list
   - Expected: unsafe is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unveil denies paths not in the list")
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
mgr.init_task(task, CapabilitySet.full())

mgr.unveil(task, "/safe", "r")

val unsafe = mgr.check_file_access(task, "/unsafe/secret", "r")
expect(unsafe).to_equal(false)
```

</details>

#### path prefix matching works correctly

- path prefix matching works correctly
   - Expected: sub is true
   - Expected: parent is false
   - Expected: sibling_prefix is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("path prefix matching works correctly")
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
mgr.init_task(task, CapabilitySet.full())

mgr.unveil(task, "/home/user", "r")

# Subpath should match
val sub = mgr.check_file_access(task, "/home/user/docs/file.txt", "r")
expect(sub).to_equal(true)

# Parent path should NOT match
val parent = mgr.check_file_access(task, "/home", "r")
expect(parent).to_equal(false)

val sibling_prefix = mgr.check_file_access(task, "/home/user2/docs/file.txt", "r")
expect(sibling_prefix).to_equal(false)
```

</details>

### CapabilityManager destroy_task

#### removes all records for the destroyed task

- removes all records for the destroyed task
   - Expected: mgr.check(task, CapabilityKind.ProcessSpawn) is true
   - Expected: mgr.check(task, CapabilityKind.ProcessSpawn) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes all records for the destroyed task")
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
val token = CapabilityToken(
    kind: CapabilityKind.ProcessSpawn,
    generation: 1,
    owner: 1
)
mgr.init_task(task, CapabilitySet(caps: [token], is_pledged: false))
expect(mgr.check(task, CapabilityKind.ProcessSpawn)).to_equal(true)

mgr.destroy_task(task)
expect(mgr.check(task, CapabilityKind.ProcessSpawn)).to_equal(false)
```

</details>

### CapabilityManager init_task_record

#### new tasks get full capability record at spawn

- new tasks get full capability record at spawn
   - Expected: mgr.check(task, CapabilityKind.ProcessSpawn) is false
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new tasks get full capability record at spawn")
"""After init_task_record(task, full: true), the record carries
explicit finite boot capabilities rather than ambient wildcard full."""
var mgr = CapabilityManager.new()
val task = TaskId(id: 42)

# Before init_task_record: no record, check returns false
expect(mgr.check(task, CapabilityKind.ProcessSpawn)).to_equal(false)

# After init_task_record(full: true): ProcessSpawn is explicitly present.
mgr.init_task_record(task, true)
val result = mgr.check(task, CapabilityKind.ProcessSpawn)
expect(result).to_equal(true)
```

</details>

#### init_task_record is idempotent

- init_task_record is idempotent
   - Expected: mgr.check(task, CapabilityKind.NetRaw) is true
   - Expected: mgr.check(task, CapabilityKind.NetRaw) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("init_task_record is idempotent")
"""Calling init_task_record twice for the same task must not
overwrite an existing record."""
var mgr = CapabilityManager.new()
val task = TaskId(id: 7)
val token = CapabilityToken(
    kind: CapabilityKind.NetRaw,
    generation: 1,
    owner: 7
)
# Initialize with an explicit token
mgr.init_task(task, CapabilitySet(caps: [token], is_pledged: false))
expect(mgr.check(task, CapabilityKind.NetRaw)).to_equal(true)

# Second init_task_record must not overwrite
mgr.init_task_record(task, false)
expect(mgr.check(task, CapabilityKind.NetRaw)).to_equal(true)
```

</details>

#### init_task_record with full=false creates pledged empty record

- init_task_record with full=false creates pledged empty record
   - Expected: mgr.check(task, CapabilityKind.SystemReboot) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("init_task_record with full=false creates pledged empty record")
var mgr = CapabilityManager.new()
val task = TaskId(id: 99)
mgr.init_task_record(task, false)
# Pledged + empty: check returns false
expect(mgr.check(task, CapabilityKind.SystemReboot)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
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

- Canonical SPipe generation for source `35638398ae293c5626ac943bb964cc4e30da03fe7c19ded143451371ea27f6ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `35638398ae293c5626ac943bb964cc4e30da03fe7c19ded143451371ea27f6ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `35638398ae293c5626ac943bb964cc4e30da03fe7c19ded143451371ea27f6ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/ipc/capability_spec.spl
mirror: doc/06_spec/unit/os/kernel/ipc/capability_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/ipc/capability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/ipc/capability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/ipc/capability_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates with empty records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/ipc/capability_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes a task with given capabilities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/ipc/capability_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes a task with empty capabilities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
