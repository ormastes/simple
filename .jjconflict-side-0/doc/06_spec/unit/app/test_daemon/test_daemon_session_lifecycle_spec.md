# test_daemon_session_lifecycle_spec

> Purpose: Prove that Session Lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_session_lifecycle_spec

Purpose: Prove that Session Lifecycle.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/test_daemon/test_daemon_session_lifecycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Session Lifecycle.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Session Lifecycle

### session types constants

#### session kind name round-trips

- session kind name round-trips
- Verify: session kind name round-trips
   - Expected: session_kind_name(SESSION_KIND_QEMU_VM) equals `qemu_vm`
   - Expected: session_kind_from_name("qemu_vm") equals `SESSION_KIND_QEMU_VM`
   - Expected: session_kind_name(SESSION_KIND_CONTAINER) equals `container_instance`
   - Expected: session_kind_from_name("container_instance") equals `SESSION_KIND_CONTAINER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("session kind name round-trips")
step("Verify: session kind name round-trips")
# @req: REQ-APP-TEST-DAEMON-001
expect(session_kind_name(SESSION_KIND_QEMU_VM)).to_equal("qemu_vm")
expect(session_kind_from_name("qemu_vm")).to_equal(SESSION_KIND_QEMU_VM)
expect(session_kind_name(SESSION_KIND_CONTAINER)).to_equal("container_instance")
expect(session_kind_from_name("container_instance")).to_equal(SESSION_KIND_CONTAINER)
```

</details>

#### reuse mode name round-trips

- reuse mode name round-trips
- Verify: reuse mode name round-trips
   - Expected: reuse_mode_name(REUSE_SHARED_READ_ONLY) equals `shared_read_only`
   - Expected: reuse_mode_from_name("shared_read_only") equals `REUSE_SHARED_READ_ONLY`
   - Expected: reuse_mode_name(REUSE_FRESH_PER_TEST) equals `fresh_per_test`
   - Expected: reuse_mode_from_name("fresh_per_test") equals `REUSE_FRESH_PER_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuse mode name round-trips")
step("Verify: reuse mode name round-trips")
expect(reuse_mode_name(REUSE_SHARED_READ_ONLY)).to_equal("shared_read_only")
expect(reuse_mode_from_name("shared_read_only")).to_equal(REUSE_SHARED_READ_ONLY)
expect(reuse_mode_name(REUSE_FRESH_PER_TEST)).to_equal("fresh_per_test")
expect(reuse_mode_from_name("fresh_per_test")).to_equal(REUSE_FRESH_PER_TEST)
```

</details>

#### reset policy name round-trips

- reset policy name round-trips
- Verify: reset policy name round-trips
   - Expected: reset_policy_name(RESET_NONE) equals `none`
   - Expected: reset_policy_from_name("none") equals `RESET_NONE`
   - Expected: reset_policy_name(RESET_SNAPSHOT_RESTORE) equals `snapshot_restore`
   - Expected: reset_policy_from_name("snapshot_restore") equals `RESET_SNAPSHOT_RESTORE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reset policy name round-trips")
step("Verify: reset policy name round-trips")
expect(reset_policy_name(RESET_NONE)).to_equal("none")
expect(reset_policy_from_name("none")).to_equal(RESET_NONE)
expect(reset_policy_name(RESET_SNAPSHOT_RESTORE)).to_equal("snapshot_restore")
expect(reset_policy_from_name("snapshot_restore")).to_equal(RESET_SNAPSHOT_RESTORE)
```

</details>

#### unknown names return -1 or unknown

- unknown names return -1 or unknown
- Verify: unknown names return -1 or unknown
   - Expected: session_kind_from_name("nonexistent") equals `-1`
   - Expected: reuse_mode_from_name("bogus") equals `-1`
   - Expected: reset_policy_from_name("fake") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown names return -1 or unknown")
step("Verify: unknown names return -1 or unknown")
expect(session_kind_from_name("nonexistent")).to_equal(-1)
expect(reuse_mode_from_name("bogus")).to_equal(-1)
expect(reset_policy_from_name("fake")).to_equal(-1)
```

</details>

### session key

#### creates deterministic session IDs

- creates deterministic session IDs
- Verify: creates deterministic session IDs
   - Expected: id1 equals `id2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates deterministic session IDs")
step("Verify: creates deterministic session IDs")
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

- matching keys are equal
- Verify: matching keys are equal
   - Expected: session_key_matches(key1, key2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matching keys are equal")
step("Verify: matching keys are equal")
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

- different targets do not match
- Verify: different targets do not match
   - Expected: session_key_matches(key1, key2) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different targets do not match")
step("Verify: different targets do not match")
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

- default meta uses LOCAL kind and FRESH_PER_TEST
- Verify: default meta uses LOCAL kind and FRESH_PER_TEST
   - Expected: meta.session_kind equals `SESSION_KIND_LOCAL`
   - Expected: meta.reuse_mode equals `REUSE_FRESH_PER_TEST`
   - Expected: meta.reset_policy equals `RESET_NONE`
   - Expected: meta.file_path equals `test/foo.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default meta uses LOCAL kind and FRESH_PER_TEST")
step("Verify: default meta uses LOCAL kind and FRESH_PER_TEST")
val meta = test_session_meta_default("test/foo.spl")
expect(meta.session_kind).to_equal(SESSION_KIND_LOCAL)
expect(meta.reuse_mode).to_equal(REUSE_FRESH_PER_TEST)
expect(meta.reset_policy).to_equal(RESET_NONE)
expect(meta.file_path).to_equal("test/foo.spl")
```

</details>

#### local meta does not need session

- local meta does not need session
- Verify: local meta does not need session
   - Expected: meta_needs_session(meta) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("local meta does not need session")
step("Verify: local meta does not need session")
val meta = make_local_meta()
expect(meta_needs_session(meta)).to_equal(false)
```

</details>

#### qemu meta needs session

- qemu meta needs session
- Verify: qemu meta needs session
   - Expected: meta_needs_session(meta) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("qemu meta needs session")
step("Verify: qemu meta needs session")
val meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test")
expect(meta_needs_session(meta)).to_equal(true)
```

</details>

#### container meta needs session

- container meta needs session
- Verify: container meta needs session
   - Expected: meta_needs_session(meta) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("container meta needs session")
step("Verify: container meta needs session")
val meta = make_container_meta("ubuntu", REUSE_SHARED_WITH_RESET)
expect(meta_needs_session(meta)).to_equal(true)
```

</details>

### broker creation

#### starts with zero sessions

- starts with zero sessions
- Verify: starts with zero sessions
   - Expected: sb.total_count() equals `0`
   - Expected: sb.active_count() equals `0`
   - Expected: sb.idle_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with zero sessions")
step("Verify: starts with zero sessions")
reset_sb()
expect(sb.total_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(sb.active_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(sb.idle_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### has default idle timeout

- has default idle timeout
- Verify: has default idle timeout
   - Expected: sb.idle_timeout_ms equals `300000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has default idle timeout")
step("Verify: has default idle timeout")
reset_sb()
expect(sb.idle_timeout_ms).to_equal(300000)  # oracle: 300000 — named expected value from the requirement
```

</details>

#### has default startup timeout

- has default startup timeout
- Verify: has default startup timeout
   - Expected: sb.startup_timeout_ms equals `60000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has default startup timeout")
step("Verify: has default startup timeout")
reset_sb()
expect(sb.startup_timeout_ms).to_equal(60000)  # oracle: 60000 — named expected value from the requirement
```

</details>

### acquire and release

#### acquire creates a new lease

- acquire creates a new lease
- Verify: acquire creates a new lease
   - Expected: sb.total_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("acquire creates a new lease")
step("Verify: acquire creates a new lease")
reset_sb()
val meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test")
val lease = sb.acquire(meta)
expect(sb.total_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(lease.session_id.len()).to_be_greater_than(0)
```

</details>

#### release marks lease as idle

- release marks lease as idle
- Verify: release marks lease as idle
   - Expected: sb.leases[0].session_id equals `lease.session_id`
   - Expected: sb.leases[0].status equals `LEASE_IDLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("release marks lease as idle")
step("Verify: release marks lease as idle")
reset_sb()
val meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test")
val lease = sb.acquire(meta)
sb.release(lease.session_id)
expect(sb.leases[0].session_id).to_equal(lease.session_id)
expect(sb.leases[0].status).to_equal(LEASE_IDLE)
```

</details>

#### reuses idle lease with matching key

- reuses idle lease with matching key
- Verify: reuses idle lease with matching key
   - Expected: local_sb.total_count() equals `1`
   - Expected: lease2.session_id equals `sid`
   - Expected: lease2.test_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses idle lease with matching key")
step("Verify: reuses idle lease with matching key")
var local_sb = session_broker_new()
val meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test")
val lease1 = local_sb.acquire(meta)
val sid = lease1.session_id
local_sb.release(sid)
val lease2 = local_sb.acquire(meta)
expect(local_sb.total_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(lease2.session_id).to_equal(sid)
expect(lease2.test_count).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### fresh_per_test always creates new session

- fresh_per_test always creates new session
- Verify: fresh_per_test always creates new session
   - Expected: sb.total_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fresh_per_test always creates new session")
step("Verify: fresh_per_test always creates new session")
reset_sb()
val meta = make_qemu_meta("arm64", REUSE_FRESH_PER_TEST, "/bin/test")
val lease1 = sb.acquire(meta)
sb.release(lease1.session_id)
val lease2 = sb.acquire(meta)
# fresh_per_test creates a new lease each time
expect(sb.total_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### assigns unique session IDs

- assigns unique session IDs
- Verify: assigns unique session IDs
   - Expected: l1.session_id != l2.session_id is true
   - Expected: sb.total_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns unique session IDs")
step("Verify: assigns unique session IDs")
reset_sb()
val meta1 = make_qemu_meta("arm64", REUSE_FRESH_PER_TEST, "/bin/a")
val meta2 = make_qemu_meta("riscv64", REUSE_FRESH_PER_TEST, "/bin/b")
val l1 = sb.acquire(meta1)
val l2 = sb.acquire(meta2)
# Different targets produce different session IDs
expect(l1.session_id != l2.session_id).to_equal(true)
expect(sb.total_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### multi-kind sessions

#### tracks sessions from different kinds separately

- tracks sessions from different kinds separately
- Verify: tracks sessions from different kinds separately
   - Expected: sb.total_count() equals `3`
   - Expected: sb.count_by_kind(SESSION_KIND_QEMU_VM) equals `1`
   - Expected: sb.count_by_kind(SESSION_KIND_CONTAINER) equals `1`
   - Expected: sb.count_by_kind(SESSION_KIND_SERVICE) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks sessions from different kinds separately")
step("Verify: tracks sessions from different kinds separately")
reset_sb()
val qemu_meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/q")
val container_meta = make_container_meta("ubuntu", REUSE_SHARED_WITH_RESET)
val service_meta = make_service_meta("api-server")
sb.acquire(qemu_meta)
sb.acquire(container_meta)
sb.acquire(service_meta)
expect(sb.total_count()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(sb.count_by_kind(SESSION_KIND_QEMU_VM)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(sb.count_by_kind(SESSION_KIND_CONTAINER)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(sb.count_by_kind(SESSION_KIND_SERVICE)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### count_by_kind returns 0 for unused kinds

- count_by_kind returns 0 for unused kinds
- Verify: count_by_kind returns 0 for unused kinds
   - Expected: sb.count_by_kind(SESSION_KIND_SIMULATOR) equals `0`
   - Expected: sb.count_by_kind(SESSION_KIND_LOCAL) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("count_by_kind returns 0 for unused kinds")
step("Verify: count_by_kind returns 0 for unused kinds")
reset_sb()
expect(sb.count_by_kind(SESSION_KIND_SIMULATOR)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(sb.count_by_kind(SESSION_KIND_LOCAL)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### stop session

#### removes session from broker

- removes session from broker
- Verify: removes session from broker
   - Expected: sb.total_count() equals `1`
   - Expected: sb.total_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes session from broker")
step("Verify: removes session from broker")
reset_sb()
val meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test")
val lease = sb.acquire(meta)
expect(sb.total_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
sb.stop_session(lease.session_id)
expect(sb.total_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### stop returns true for existing session

- stop returns true for existing session
- Verify: stop returns true for existing session
   - Expected: stopped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stop returns true for existing session")
step("Verify: stop returns true for existing session")
reset_sb()
val meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test")
val lease = sb.acquire(meta)
val stopped = sb.stop_session(lease.session_id)
expect(stopped).to_equal(true)
```

</details>

#### stop returns false for unknown session

- stop returns false for unknown session
- Verify: stop returns false for unknown session
   - Expected: stopped is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stop returns false for unknown session")
step("Verify: stop returns false for unknown session")
reset_sb()
val stopped = sb.stop_session("nonexistent_session")
expect(stopped).to_equal(false)
```

</details>

### shutdown all

#### removes all sessions

- removes all sessions
- Verify: removes all sessions
   - Expected: sb.total_count() equals `3`
   - Expected: sb.total_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes all sessions")
step("Verify: removes all sessions")
reset_sb()
sb.acquire(make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/a"))
sb.acquire(make_container_meta("ubuntu", REUSE_SHARED_WITH_RESET))
sb.acquire(make_service_meta("api"))
expect(sb.total_count()).to_equal(3)  # oracle: 3 — named expected value from the requirement
sb.shutdown_all()
expect(sb.total_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### status reporting

#### reports active and idle counts

- reports active and idle counts
- Verify: reports active and idle counts
   - Expected: total equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports active and idle counts")
step("Verify: reports active and idle counts")
reset_sb()
val meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test")
val lease = sb.acquire(meta)
# Lease from start_new_session without adapter comes as LEASE_IDLE
# because session_lease_new sets status to LEASE_IDLE
val total = sb.total_count()
expect(total).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### status_report includes session counts

- status_report includes session counts
- Verify: status_report includes session counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("status_report includes session counts")
step("Verify: status_report includes session counts")
reset_sb()
sb.acquire(make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test"))
val report = sb.status_report()
expect(report).to_contain("Session Broker Status")
expect(report).to_contain("Total sessions: 1")
```

</details>

### adapter registration

#### registers adapter for kind

- registers adapter for kind
- Verify: registers adapter for kind
   - Expected: found == nil is false
   - Expected: found.name equals `qemu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers adapter for kind")
step("Verify: registers adapter for kind")
reset_sb()
val adapter = session_adapter_new(SESSION_KIND_QEMU_VM, "qemu")
sb.register_adapter(adapter)
# After registering, the registry can find the adapter
val found = sb.registry.find_by_kind(SESSION_KIND_QEMU_VM)
expect(found == nil).to_equal(false)
expect(found.name).to_equal("qemu")
```

</details>

#### find_by_kind returns nil for unregistered kind

- find_by_kind returns nil for unregistered kind
- Verify: find_by_kind returns nil for unregistered kind
   - Expected: found == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_by_kind returns nil for unregistered kind")
step("Verify: find_by_kind returns nil for unregistered kind")
reset_sb()
val found = sb.registry.find_by_kind(SESSION_KIND_SIMULATOR)
expect(found == nil).to_equal(true)
```

</details>

### session lease struct

#### creates lease with correct defaults

- creates lease with correct defaults
- Verify: creates lease with correct defaults
   - Expected: lease.status equals `LEASE_IDLE`
   - Expected: lease.test_count equals `0`
   - Expected: lease.pid equals `0`
   - Expected: lease.qmp_socket equals ``
   - Expected: lease.snapshot_name equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates lease with correct defaults")
step("Verify: creates lease with correct defaults")
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
expect(lease.test_count).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(lease.pid).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(lease.qmp_socket).to_equal("")
expect(lease.snapshot_name).to_equal("")
expect(lease.created_at).to_be_greater_than(0)
```

</details>

#### lease session_id matches key ID

- lease session_id matches key ID
- Verify: lease session_id matches key ID
   - Expected: lease.session_id equals `expected_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lease session_id matches key ID")
step("Verify: lease session_id matches key ID")
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

- creates descriptor with defaults
- Verify: creates descriptor with defaults
   - Expected: desc.timeout_ms equals `60000`
   - Expected: desc.max_concurrent equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates descriptor with defaults")
step("Verify: creates descriptor with defaults")
val key = SessionKey(
    kind: SESSION_KIND_QEMU_VM,
    target: "arm64",
    artifact_hash: "xyz",
    env_profile: "",
    reuse_mode: REUSE_SHARED_READ_ONLY,
    reset_policy: RESET_NONE
)
val desc = session_descriptor_new(key)
expect(desc.timeout_ms).to_equal(60000)  # oracle: 60000 — named expected value from the requirement
expect(desc.max_concurrent).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### complete lifecycle

#### acquire, release, reuse, stop cycle

- acquire, release, reuse, stop cycle
- Verify: acquire, release, reuse, stop cycle
   - Expected: sb.total_count() equals `1`
   - Expected: find_lease_status(sid) equals `LEASE_IDLE`
   - Expected: lease2.session_id equals `sid`
   - Expected: sb.total_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("acquire, release, reuse, stop cycle")
step("Verify: acquire, release, reuse, stop cycle")
reset_sb()
val meta = make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/test")
# Acquire
val lease1 = sb.acquire(meta)
val sid = lease1.session_id
expect(sb.total_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
# Release
sb.release(sid)
expect(find_lease_status(sid)).to_equal(LEASE_IDLE)
# Reuse
val lease2 = sb.acquire(meta)
expect(lease2.session_id).to_equal(sid)
# Stop
sb.stop_session(sid)
expect(sb.total_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### multi-kind acquire, release, shutdown

- multi-kind acquire, release, shutdown
- Verify: multi-kind acquire, release, shutdown
   - Expected: sb.total_count() equals `3`
   - Expected: sb.idle_count() equals `3`
   - Expected: sb.total_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multi-kind acquire, release, shutdown")
step("Verify: multi-kind acquire, release, shutdown")
reset_sb()
val l1 = sb.acquire(make_qemu_meta("arm64", REUSE_SHARED_READ_ONLY, "/bin/a"))
val l2 = sb.acquire(make_container_meta("ubuntu", REUSE_SHARED_WITH_RESET))
val l3 = sb.acquire(make_service_meta("api"))
expect(sb.total_count()).to_equal(3)  # oracle: 3 — named expected value from the requirement
sb.release(l1.session_id)
sb.release(l2.session_id)
sb.release(l3.session_id)
# All idle now
expect(sb.idle_count()).to_equal(3)  # oracle: 3 — named expected value from the requirement
sb.shutdown_all()
expect(sb.total_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-TEST-DAEMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a1b7c7125aed344fe9d10b0eb99f404c9917ef947bed2c21c633f571ba2bda39`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a1b7c7125aed344fe9d10b0eb99f404c9917ef947bed2c21c633f571ba2bda39`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a1b7c7125aed344fe9d10b0eb99f404c9917ef947bed2c21c633f571ba2bda39`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/test_daemon/test_daemon_session_lifecycle_spec.spl
mirror: doc/06_spec/unit/app/test_daemon/test_daemon_session_lifecycle_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_daemon/test_daemon_session_lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_daemon/test_daemon_session_lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_daemon/test_daemon_session_lifecycle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/test_daemon/test_daemon_session_lifecycle_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'session kind name round-trips' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_daemon/test_daemon_session_lifecycle_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuse mode name round-trips' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_daemon/test_daemon_session_lifecycle_spec.spl:166:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reset policy name round-trips' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
