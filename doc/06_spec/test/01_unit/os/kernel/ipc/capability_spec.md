# Capability Enforcement Specification

> Tests for the capability enforcement manager. Validates grant/revoke lifecycle, pledge() monotonic restriction, unveil() file path restriction, and file access checking with prefix matching.

<!-- sdn-diagram:id=capability_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=capability_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

capability_spec -> std
capability_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=capability_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

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
| Source | `test/01_unit/os/kernel/ipc/capability_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the capability enforcement manager. Validates grant/revoke lifecycle,
pledge() monotonic restriction, unveil() file path restriction, and file access
checking with prefix matching.

## Scenarios

### CapabilityManager

### construction

#### creates with empty records

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = CapabilityManager.new()
val task = TaskId(id: 1)
val result = mgr.check(task, CapabilityKind.ProcessSpawn)
expect(result).to_equal(false)
```

</details>

### init_task

#### initializes a task with given capabilities

1. var mgr = CapabilityManager new
2. mgr init task
   - Expected: has is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = CapabilityManager new
2. mgr init task
   - Expected: has is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
mgr.init_task(task, CapabilitySet.full())
val has = mgr.check(task, CapabilityKind.ProcessSpawn)
expect(has).to_equal(false)
```

</details>

### CapabilityManager check

#### returns false for unregistered task

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = CapabilityManager.new()
val result = mgr.check(TaskId(id: 999), CapabilityKind.SystemReboot)
expect(result).to_equal(false)
```

</details>

#### returns true when task has matching capability

1. var mgr = CapabilityManager new
2. mgr init task
   - Expected: mgr.check(task, CapabilityKind.NetRaw) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = CapabilityManager new
2. mgr init task
   - Expected: mgr.check(task, CapabilityKind.SystemReboot) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = CapabilityManager new
2. kind: CapabilityKind SharedDataset
3. mgr init task
   - Expected: mgr.check(task, CapabilityKind.SharedDataset(object_id: 7u64, generation: 3u64, rights: CAP_RIGHT_READ)) is true
   - Expected: mgr.check(task, CapabilityKind.SharedDataset(object_id: 7u64, generation: 3u64, rights: CAP_RIGHT_MAP)) is true
   - Expected: mgr.check(task, CapabilityKind.SharedDataset(object_id: 7u64, generation: 4u64, rights: CAP_RIGHT_READ)) is false
   - Expected: mgr.check(task, CapabilityKind.SharedDataset(object_id: 8u64, generation: 3u64, rights: CAP_RIGHT_READ)) is false
   - Expected: mgr.check(task, CapabilityKind.SharedDataset(object_id: 7u64, generation: 3u64, rights: CAP_RIGHT_DATASET_BUILD)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = CapabilityManager new
2. kind: CapabilityKind ProcessQueue
3. mgr init task
   - Expected: mgr.check(task, CapabilityKind.ProcessQueue(queue_id: 11u64, generation: 5u64, rights: CAP_RIGHT_QUEUE_SUBMIT)) is true
   - Expected: mgr.check(task, CapabilityKind.ProcessQueue(queue_id: 11u64, generation: 5u64, rights: CAP_RIGHT_QUEUE_RECV)) is true
   - Expected: mgr.check(task, CapabilityKind.ProcessQueue(queue_id: 11u64, generation: 6u64, rights: CAP_RIGHT_QUEUE_RECV)) is false
   - Expected: mgr.check(task, CapabilityKind.ProcessQueue(queue_id: 12u64, generation: 5u64, rights: CAP_RIGHT_QUEUE_RECV)) is false
   - Expected: mgr.check(task, CapabilityKind.ProcessQueue(queue_id: 11u64, generation: 5u64, rights: CAP_RIGHT_ADMIN)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = CapabilityManager new
2. mgr init task
3. mgr init task
   - Expected: ok is true
   - Expected: mgr.check(dst, CapabilityKind.ProcessSpawn) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val src = TaskId(id: 1)
val dst = TaskId(id: 2)
val token = CapabilityToken(
    kind: CapabilityKind.ProcessSpawn,
    generation: 1,
    owner: 1
)
mgr.init_task(src, CapabilitySet(caps: [token], is_pledged: false))
mgr.init_task(dst, CapabilitySet.full())

val ok = mgr.grant(src, dst, token)
expect(ok).to_equal(true)
expect(mgr.check(dst, CapabilityKind.ProcessSpawn)).to_equal(true)
```

</details>

#### fails to grant if source does not hold capability

1. var mgr = CapabilityManager new
2. mgr init task
3. mgr init task
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val src = TaskId(id: 1)
val dst = TaskId(id: 2)
mgr.init_task(src, CapabilitySet.full())  # Empty caps
mgr.init_task(dst, CapabilitySet.full())

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

1. var mgr = CapabilityManager new
2. mgr init task
   - Expected: revoked is true
   - Expected: mgr.check(task, CapabilityKind.NetRaw) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = CapabilityManager new
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = CapabilityManager new
2. mgr pledge
   - Expected: mgr.check(task, CapabilityKind.ProcessSpawn) is true
   - Expected: mgr.check(task, CapabilityKind.SystemReboot) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = CapabilityManager new
2. mgr init task
3. mgr pledge
   - Expected: mgr.check(task, CapabilityKind.NetRaw) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = CapabilityManager new
2. mgr init task
3. mgr pledge
   - Expected: mgr.check(task, CapabilityKind.ProcessSpawn) is true
4. mgr pledge
   - Expected: mgr.check(task, CapabilityKind.ProcessSpawn) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = CapabilityManager new
2. mgr init task
   - Expected: allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
mgr.init_task(task, CapabilitySet.full())
val allowed = mgr.check_file_access(task, "/any/path", "r")
expect(allowed).to_equal(true)
```

</details>

#### after unveil, only unveiled paths are allowed

1. var mgr = CapabilityManager new
2. mgr init task
3. mgr unveil
   - Expected: tmp_ok is true
   - Expected: etc_denied is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = CapabilityManager new
2. mgr init task
3. mgr unveil
   - Expected: write_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
mgr.init_task(task, CapabilitySet.full())

mgr.unveil(task, "/var/log", "rw")

val write_ok = mgr.check_file_access(task, "/var/log/app.log", "w")
expect(write_ok).to_equal(true)
```

</details>

#### multiple unveil calls add entries

1. var mgr = CapabilityManager new
2. mgr init task
3. mgr unveil
4. mgr unveil
   - Expected: tmp_ok is true
   - Expected: home_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = CapabilityManager new
2. mgr init task
3. mgr unveil
   - Expected: unsafe is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val task = TaskId(id: 1)
mgr.init_task(task, CapabilitySet.full())

mgr.unveil(task, "/safe", "r")

val unsafe = mgr.check_file_access(task, "/unsafe/secret", "r")
expect(unsafe).to_equal(false)
```

</details>

#### path prefix matching works correctly

1. var mgr = CapabilityManager new
2. mgr init task
3. mgr unveil
   - Expected: sub is true
   - Expected: parent is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
```

</details>

### CapabilityManager destroy_task

#### removes all records for the destroyed task

1. var mgr = CapabilityManager new
2. mgr init task
   - Expected: mgr.check(task, CapabilityKind.ProcessSpawn) is true
3. mgr destroy task
   - Expected: mgr.check(task, CapabilityKind.ProcessSpawn) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = CapabilityManager new
   - Expected: mgr.check(task, CapabilityKind.ProcessSpawn) is false
2. mgr init task record
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val task = TaskId(id: 42)

# Before init_task_record: no record, check returns false
expect(mgr.check(task, CapabilityKind.ProcessSpawn)).to_equal(false)

# After init_task_record(full: true): record exists, still false
# because CapabilitySet.full() starts as empty (unpledged full trust)
mgr.init_task_record(task, true)
val result = mgr.check(task, CapabilityKind.ProcessSpawn)
expect(result).to_equal(false)
```

</details>

#### init_task_record is idempotent

1. var mgr = CapabilityManager new
2. mgr init task
   - Expected: mgr.check(task, CapabilityKind.NetRaw) is true
3. mgr init task record
   - Expected: mgr.check(task, CapabilityKind.NetRaw) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = CapabilityManager new
2. mgr init task record
   - Expected: mgr.check(task, CapabilityKind.SystemReboot) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
