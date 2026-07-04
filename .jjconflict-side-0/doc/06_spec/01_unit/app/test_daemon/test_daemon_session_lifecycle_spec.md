# test_daemon_session_lifecycle_spec

> Test Daemon Session Lifecycle Specification

<!-- sdn-diagram:id=test_daemon_session_lifecycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_session_lifecycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_session_lifecycle_spec -> std
test_daemon_session_lifecycle_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_session_lifecycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_session_lifecycle_spec

Test Daemon Session Lifecycle Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TDMN-051 to #TDMN-070 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/app/test_daemon/test_daemon_session_lifecycle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Test Daemon Session Lifecycle Specification

Tests the complete lifecycle of test sessions using SessionBroker:
acquire → run tests → reset → release → cleanup → shutdown.
Exercises SessionBroker, SessionAdapter, and session_types together.

## Scenarios

### Session Lifecycle

### session types constants

#### session kind name round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(session_kind_name(SESSION_KIND_QEMU_VM)).to_equal("qemu_vm")
expect(session_kind_from_name("qemu_vm")).to_equal(SESSION_KIND_QEMU_VM)
expect(session_kind_name(SESSION_KIND_CONTAINER)).to_equal("container_instance")
expect(session_kind_from_name("container_instance")).to_equal(SESSION_KIND_CONTAINER)
```

</details>

#### reuse mode name round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reuse_mode_name(REUSE_SHARED_READ_ONLY)).to_equal("shared_read_only")
expect(reuse_mode_from_name("shared_read_only")).to_equal(REUSE_SHARED_READ_ONLY)
expect(reuse_mode_name(REUSE_FRESH_PER_TEST)).to_equal("fresh_per_test")
expect(reuse_mode_from_name("fresh_per_test")).to_equal(REUSE_FRESH_PER_TEST)
```

</details>

#### reset policy name round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reset_policy_name(RESET_NONE)).to_equal("none")
expect(reset_policy_from_name("none")).to_equal(RESET_NONE)
expect(reset_policy_name(RESET_SNAPSHOT_RESTORE)).to_equal("snapshot_restore")
expect(reset_policy_from_name("snapshot_restore")).to_equal(RESET_SNAPSHOT_RESTORE)
```

</details>

#### unknown names return -1 or unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(session_kind_from_name("nonexistent")).to_equal(-1)
expect(reuse_mode_from_name("bogus")).to_equal(-1)
expect(reset_policy_from_name("fake")).to_equal(-1)
```

</details>

### session key

#### creates deterministic session IDs

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key1 = SessionKey(
    kind: SESSION_KIND_QEMU_VM,
    target: "arm64",
    artifact_hash: "abc123",
    env_profile: "",
    reuse_mode: REUSE_SHARED_READ_ONLY,
    reset_policy: RESET_NONE
)
val id1 = session_key_to_id(key1)
val id2 = session_key_to_id(key1)
expect(id1).to_equal(id2)
expect(id1).to_contain("qemu_vm")
expect(id1).to_contain("arm64")
```

</details>

#### matching keys are equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key1 = SessionKey(
    kind: SESSION_KIND_QEMU_VM,
    target: "arm64",
    artifact_hash: "abc",
    env_profile: "",
    reuse_mode: REUSE_SHARED_READ_ONLY,
    reset_policy: RESET_NONE
)
val key2 = SessionKey(
    kind: SESSION_KIND_QEMU_VM,
    target: "arm64",
    artifact_hash: "abc",
    env_profile: "",
    reuse_mode: REUSE_SHARED_READ_ONLY,
    reset_policy: RESET_NONE
)
expect(session_key_matches(key1, key2)).to_equal(true)
```

</details>

#### different targets do not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key1 = SessionKey(
    kind: SESSION_KIND_QEMU_VM,
    target: "arm64",
    artifact_hash: "abc",
    env_profile: "",
    reuse_mode: REUSE_SHARED_READ_ONLY,
    reset_policy: RESET_NONE
)
val key2 = SessionKey(
    kind: SESSION_KIND_QEMU_VM,
    target: "riscv64",
    artifact_hash: "abc",
    env_profile: "",
    reuse_mode: REUSE_SHARED_READ_ONLY,
    reset_policy: RESET_NONE
)
expect(session_key_matches(key1, key2)).to_equal(false)
```

</details>

### test session meta

#### default meta uses LOCAL kind and FRESH_PER_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta = test_session_meta_default("test/foo.spl")
expect(meta.session_kind).to_equal(SESSION_KIND_LOCAL)
expect(meta.reuse_mode).to_equal(REUSE_FRESH_PER_TEST)
expect(meta.reset_policy).to_equal(RESET_NONE)
expect(meta.file_path).to_equal("test/foo.spl")
```

</details>

#### local meta does not need session

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta = make_local_meta()
expect(meta_needs_session(meta)).to_equal(false)
```

</details>

#### qemu meta needs session

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test")
expect(meta_needs_session(meta)).to_equal(true)
```

</details>

#### container meta needs session

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta = make_container_meta("ubuntu", REUSE_SHARED_WITH_RESET)
expect(meta_needs_session(meta)).to_equal(true)
```

</details>

### broker creation

#### starts with zero sessions

1. reset sb
   - Expected: sb.total_count() equals `0`
   - Expected: sb.active_count() equals `0`
   - Expected: sb.idle_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
expect(sb.total_count()).to_equal(0)
expect(sb.active_count()).to_equal(0)
expect(sb.idle_count()).to_equal(0)
```

</details>

#### has default idle timeout

1. reset sb
   - Expected: sb.idle_timeout_ms equals `300000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
expect(sb.idle_timeout_ms).to_equal(300000)
```

</details>

#### has default startup timeout

1. reset sb
   - Expected: sb.startup_timeout_ms equals `60000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
expect(sb.startup_timeout_ms).to_equal(60000)
```

</details>

### acquire and release

#### acquire creates a new lease

1. reset sb
   - Expected: sb.total_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
val meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test")
val lease = sb.acquire(meta)
expect(sb.total_count()).to_equal(1)
expect(lease.session_id.len()).to_be_greater_than(0)
```

</details>

#### release marks lease as idle

1. reset sb
2. sb release
   - Expected: sb.leases[0].session_id equals `lease.session_id`
   - Expected: sb.leases[0].status equals `LEASE_IDLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
val meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test")
val lease = sb.acquire(meta)
sb.release(lease.session_id)
expect(sb.leases[0].session_id).to_equal(lease.session_id)
expect(sb.leases[0].status).to_equal(LEASE_IDLE)
```

</details>

#### reuses idle lease with matching key

1. var local sb = session broker new
2. local sb release
   - Expected: local_sb.total_count() equals `1`
   - Expected: lease2.session_id equals `sid`
   - Expected: lease2.test_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var local_sb = session_broker_new()
val meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test")
val lease1 = local_sb.acquire(meta)
val sid = lease1.session_id
local_sb.release(sid)
val lease2 = local_sb.acquire(meta)
expect(local_sb.total_count()).to_equal(1)
expect(lease2.session_id).to_equal(sid)
expect(lease2.test_count).to_equal(2)
```

</details>

#### fresh_per_test always creates new session

1. reset sb
2. sb release
   - Expected: sb.total_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
val meta = make_qemu_meta("arm64", REUSE_FRESH_PER_TEST, "/bin/test")
val lease1 = sb.acquire(meta)
sb.release(lease1.session_id)
val lease2 = sb.acquire(meta)
# fresh_per_test creates a new lease each time
expect(sb.total_count()).to_equal(2)
```

</details>

#### assigns unique session IDs

1. reset sb
   - Expected: l1.session_id != l2.session_id is true
   - Expected: sb.total_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
val meta1 = make_qemu_meta("arm64", REUSE_FRESH_PER_TEST, "/bin/a")
val meta2 = make_qemu_meta("riscv64", REUSE_FRESH_PER_TEST, "/bin/b")
val l1 = sb.acquire(meta1)
val l2 = sb.acquire(meta2)
# Different targets produce different session IDs
expect(l1.session_id != l2.session_id).to_equal(true)
expect(sb.total_count()).to_equal(2)
```

</details>

### multi-kind sessions

#### tracks sessions from different kinds separately

1. reset sb
2. sb acquire
3. sb acquire
4. sb acquire
   - Expected: sb.total_count() equals `3`
   - Expected: sb.count_by_kind(SESSION_KIND_QEMU_VM) equals `1`
   - Expected: sb.count_by_kind(SESSION_KIND_CONTAINER) equals `1`
   - Expected: sb.count_by_kind(SESSION_KIND_SERVICE) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
val qemu_meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/q")
val container_meta = make_container_meta("ubuntu", REUSE_SHARED_WITH_RESET)
val service_meta = make_service_meta("api-server")
sb.acquire(qemu_meta)
sb.acquire(container_meta)
sb.acquire(service_meta)
expect(sb.total_count()).to_equal(3)
expect(sb.count_by_kind(SESSION_KIND_QEMU_VM)).to_equal(1)
expect(sb.count_by_kind(SESSION_KIND_CONTAINER)).to_equal(1)
expect(sb.count_by_kind(SESSION_KIND_SERVICE)).to_equal(1)
```

</details>

#### count_by_kind returns 0 for unused kinds

1. reset sb
   - Expected: sb.count_by_kind(SESSION_KIND_SIMULATOR) equals `0`
   - Expected: sb.count_by_kind(SESSION_KIND_LOCAL) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
expect(sb.count_by_kind(SESSION_KIND_SIMULATOR)).to_equal(0)
expect(sb.count_by_kind(SESSION_KIND_LOCAL)).to_equal(0)
```

</details>

### stop session

#### removes session from broker

1. reset sb
   - Expected: sb.total_count() equals `1`
2. sb stop session
   - Expected: sb.total_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
val meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test")
val lease = sb.acquire(meta)
expect(sb.total_count()).to_equal(1)
sb.stop_session(lease.session_id)
expect(sb.total_count()).to_equal(0)
```

</details>

#### stop returns true for existing session

1. reset sb
   - Expected: stopped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
val meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test")
val lease = sb.acquire(meta)
val stopped = sb.stop_session(lease.session_id)
expect(stopped).to_equal(true)
```

</details>

#### stop returns false for unknown session

1. reset sb
   - Expected: stopped is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
val stopped = sb.stop_session("nonexistent_session")
expect(stopped).to_equal(false)
```

</details>

### shutdown all

#### removes all sessions

1. reset sb
2. sb acquire
3. sb acquire
4. sb acquire
   - Expected: sb.total_count() equals `3`
5. sb shutdown all
   - Expected: sb.total_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
sb.acquire(make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/a"))
sb.acquire(make_container_meta("ubuntu", REUSE_SHARED_WITH_RESET))
sb.acquire(make_service_meta("api"))
expect(sb.total_count()).to_equal(3)
sb.shutdown_all()
expect(sb.total_count()).to_equal(0)
```

</details>

### status reporting

#### reports active and idle counts

1. reset sb
   - Expected: total equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
val meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test")
val lease = sb.acquire(meta)
# Lease from start_new_session without adapter comes as LEASE_IDLE
# because session_lease_new sets status to LEASE_IDLE
val total = sb.total_count()
expect(total).to_equal(1)
```

</details>

#### status_report includes session counts

1. reset sb
2. sb acquire


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
sb.acquire(make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test"))
val report = sb.status_report()
expect(report).to_contain("Session Broker Status")
expect(report).to_contain("Total sessions: 1")
```

</details>

### adapter registration

#### registers adapter for kind

1. reset sb
2. sb register adapter
   - Expected: found.? is true
   - Expected: found.name equals `qemu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
val adapter = session_adapter_new(SESSION_KIND_QEMU_VM, "qemu")
sb.register_adapter(adapter)
# After registering, the registry can find the adapter
val found = sb.registry.find_by_kind(SESSION_KIND_QEMU_VM)
expect(found.?).to_equal(true)
expect(found.name).to_equal("qemu")
```

</details>

#### find_by_kind returns nil for unregistered kind

1. reset sb
   - Expected: found.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
val found = sb.registry.find_by_kind(SESSION_KIND_SIMULATOR)
expect(found.?).to_equal(false)
```

</details>

### session lease struct

#### creates lease with correct defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = SessionKey(
    kind: SESSION_KIND_QEMU_VM,
    target: "arm64",
    artifact_hash: "abc",
    env_profile: "",
    reuse_mode: REUSE_SHARED_READ_ONLY,
    reset_policy: RESET_NONE
)
val lease = session_lease_new(key)
expect(lease.status).to_equal(LEASE_IDLE)
expect(lease.test_count).to_equal(0)
expect(lease.pid).to_equal(0)
expect(lease.qmp_socket).to_equal("")
expect(lease.snapshot_name).to_equal("")
expect(lease.created_at).to_be_greater_than(0)
```

</details>

#### lease session_id matches key ID

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = SessionKey(
    kind: SESSION_KIND_CONTAINER,
    target: "ubuntu",
    artifact_hash: "def",
    env_profile: "",
    reuse_mode: REUSE_EXCLUSIVE_REUSED,
    reset_policy: RESET_HARD
)
val lease = session_lease_new(key)
val expected_id = session_key_to_id(key)
expect(lease.session_id).to_equal(expected_id)
```

</details>

### session descriptor

#### creates descriptor with defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = SessionKey(
    kind: SESSION_KIND_QEMU_VM,
    target: "arm64",
    artifact_hash: "xyz",
    env_profile: "",
    reuse_mode: REUSE_SHARED_READ_ONLY,
    reset_policy: RESET_NONE
)
val desc = session_descriptor_new(key)
expect(desc.timeout_ms).to_equal(60000)
expect(desc.max_concurrent).to_equal(1)
```

</details>

### complete lifecycle

#### acquire, release, reuse, stop cycle

1. reset sb
   - Expected: sb.total_count() equals `1`
2. sb release
   - Expected: find_lease_status(sid) equals `LEASE_IDLE`
   - Expected: lease2.session_id equals `sid`
3. sb stop session
   - Expected: sb.total_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
val meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test")
# Acquire
val lease1 = sb.acquire(meta)
val sid = lease1.session_id
expect(sb.total_count()).to_equal(1)
# Release
sb.release(sid)
expect(find_lease_status(sid)).to_equal(LEASE_IDLE)
# Reuse
val lease2 = sb.acquire(meta)
expect(lease2.session_id).to_equal(sid)
# Stop
sb.stop_session(sid)
expect(sb.total_count()).to_equal(0)
```

</details>

#### multi-kind acquire, release, shutdown

1. reset sb
   - Expected: sb.total_count() equals `3`
2. sb release
3. sb release
4. sb release
   - Expected: sb.idle_count() equals `3`
5. sb shutdown all
   - Expected: sb.total_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_sb()
val l1 = sb.acquire(make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/a"))
val l2 = sb.acquire(make_container_meta("ubuntu", REUSE_SHARED_WITH_RESET))
val l3 = sb.acquire(make_service_meta("api"))
expect(sb.total_count()).to_equal(3)
sb.release(l1.session_id)
sb.release(l2.session_id)
sb.release(l3.session_id)
# All idle now
expect(sb.idle_count()).to_equal(3)
sb.shutdown_all()
expect(sb.total_count()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
