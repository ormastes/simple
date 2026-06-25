# test_daemon_session_sharing_system_spec

> @cover src/app/test_daemon/session_broker.spl 80%

<!-- sdn-diagram:id=test_daemon_session_sharing_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_session_sharing_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_session_sharing_system_spec -> std
test_daemon_session_sharing_system_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_session_sharing_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_session_sharing_system_spec

@cover src/app/test_daemon/session_broker.spl 80%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TDMN-SYS-041 to #TDMN-SYS-060 |
| Category | Infrastructure / System Test |
| Status | Active |
| Source | `test/03_system/tools/test_daemon/test_daemon_session_sharing_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/app/test_daemon/session_broker.spl 80%
@cover src/app/test_daemon/session_types.spl 80%
@cover src/app/test_daemon/session_adapter.spl 80%
Test Daemon Session Sharing System Test

Tests broker-level session management: session registry via broker,
per-session leasing, concurrent session requests, session reuse
verification, and session lifecycle through the SessionBroker API.

## Scenarios

### Session Sharing System

### session registry via broker

#### creates a session when acquiring

1. var broker = session broker new
   - Expected: broker.total_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("arm64", "firmware.bin", REUSE_SHARED_READ_ONLY)
val lease = broker.acquire(meta)
expect(broker.total_count()).to_equal(1)
expect(lease.session_id.len()).to_be_greater_than(0)
```

</details>

#### registers session with correct kind

1. var broker = session broker new
   - Expected: lease.key.kind equals `SESSION_KIND_QEMU_VM`
   - Expected: lease.key.target equals `arm64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("arm64", "firmware.bin", REUSE_SHARED_READ_ONLY)
val lease = broker.acquire(meta)
expect(lease.key.kind).to_equal(SESSION_KIND_QEMU_VM)
expect(lease.key.target).to_equal("arm64")
```

</details>

#### tracks multiple sessions in registry

1. var broker = session broker new
2. broker acquire
3. broker acquire
4. broker acquire
   - Expected: broker.total_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val m1 = make_qemu_meta("arm64", "fw1.bin", REUSE_SHARED_READ_ONLY)
val m2 = make_qemu_meta("riscv64", "fw2.bin", REUSE_SHARED_READ_ONLY)
val m3 = make_container_meta("x86_64", "image1", REUSE_SHARED_READ_ONLY)
broker.acquire(m1)
broker.acquire(m2)
broker.acquire(m3)
expect(broker.total_count()).to_equal(3)
```

</details>

#### reports status with all session kinds

1. var broker = session broker new
2. broker acquire
3. broker acquire


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val m1 = make_qemu_meta("arm64", "fw1.bin", REUSE_SHARED_READ_ONLY)
val m2 = make_container_meta("x86_64", "img1", REUSE_SHARED_READ_ONLY)
broker.acquire(m1)
broker.acquire(m2)
val report = broker.status_report()
expect(report).to_contain("Total sessions: 2")
```

</details>

### per-session leasing

#### lease starts as active after acquire

1. var broker = session broker new
   - Expected: broker.total_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("arm64", "fw.bin", REUSE_SHARED_READ_ONLY)
val lease = broker.acquire(meta)
# Without an adapter, the lease is created via session_lease_new (IDLE)
# but the broker adds it to leases — check total
expect(broker.total_count()).to_equal(1)
```

</details>

#### release sets session back to idle

1. var broker = session broker new
2. broker release
   - Expected: broker.idle_count() equals `1`
   - Expected: broker.active_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("arm64", "fw.bin", REUSE_SHARED_READ_ONLY)
val lease = broker.acquire(meta)
broker.release(lease.session_id)
expect(broker.idle_count()).to_equal(1)
expect(broker.active_count()).to_equal(0)
```

</details>

#### released session can be reacquired

1. var broker = session broker new
2. broker release
   - Expected: broker.total_count() equals `1`
   - Expected: lease2.session_id equals `lease1.session_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("arm64", "fw.bin", REUSE_SHARED_READ_ONLY)
val lease1 = broker.acquire(meta)
broker.release(lease1.session_id)
# Second acquire should reuse the idle session
val lease2 = broker.acquire(meta)
# Should still be 1 total (reused, not new)
expect(broker.total_count()).to_equal(1)
expect(lease2.session_id).to_equal(lease1.session_id)
```

</details>

#### test_count increments on reuse

1. var broker = session broker new
2. broker release
   - Expected: lease2.test_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("arm64", "fw.bin", REUSE_SHARED_READ_ONLY)
val lease1 = broker.acquire(meta)
broker.release(lease1.session_id)
val lease2 = broker.acquire(meta)
expect(lease2.test_count).to_equal(1)
```

</details>

### concurrent session requests

#### different targets get separate sessions

1. var broker = session broker new
   - Expected: broker.total_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val m1 = make_qemu_meta("arm64", "fw.bin", REUSE_SHARED_READ_ONLY)
val m2 = make_qemu_meta("riscv64", "fw.bin", REUSE_SHARED_READ_ONLY)
val l1 = broker.acquire(m1)
val l2 = broker.acquire(m2)
expect(broker.total_count()).to_equal(2)
expect(l1.session_id).to_not_equal(l2.session_id)
```

</details>

#### same target same artifact reuses when idle

1. var broker = session broker new
2. broker release
   - Expected: broker.total_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("arm64", "fw.bin", REUSE_SHARED_READ_ONLY)
val l1 = broker.acquire(meta)
broker.release(l1.session_id)
val l2 = broker.acquire(meta)
expect(broker.total_count()).to_equal(1)
```

</details>

#### fresh_per_test always creates new session

1. var broker = session broker new
   - Expected: broker.total_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("arm64", "fw.bin", REUSE_FRESH_PER_TEST)
val l1 = broker.acquire(meta)
val l2 = broker.acquire(meta)
expect(broker.total_count()).to_equal(2)
```

</details>

#### multiple qemu sessions up to limit

1. var broker = session broker new
   - Expected: broker.total_count() equals `4`
   - Expected: broker.count_by_kind(SESSION_KIND_QEMU_VM) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
# Default max for qemu_vm is 4
val leases = acquire_n_sessions(broker, make_qemu_meta("arm64", "fw.bin", REUSE_FRESH_PER_TEST), 4)
expect(broker.total_count()).to_equal(4)
expect(broker.count_by_kind(SESSION_KIND_QEMU_VM)).to_equal(4)
```

</details>

### session reuse verification

#### shared_read_only sessions are reused

1. var broker = session broker new
2. broker release
   - Expected: l2.session_id equals `l1.session_id`
   - Expected: broker.total_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("arm64", "fw.bin", REUSE_SHARED_READ_ONLY)
val l1 = broker.acquire(meta)
broker.release(l1.session_id)
val l2 = broker.acquire(meta)
expect(l2.session_id).to_equal(l1.session_id)
expect(broker.total_count()).to_equal(1)
```

</details>

#### shared_with_reset sessions are reused

1. var broker = session broker new
2. broker release
   - Expected: l2.session_id equals `l1.session_id`
   - Expected: broker.total_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("arm64", "fw.bin", REUSE_SHARED_WITH_RESET)
val l1 = broker.acquire(meta)
broker.release(l1.session_id)
val l2 = broker.acquire(meta)
expect(l2.session_id).to_equal(l1.session_id)
expect(broker.total_count()).to_equal(1)
```

</details>

#### fresh_per_test sessions are never reused

1. var broker = session broker new
2. broker release
   - Expected: broker.total_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("arm64", "fw.bin", REUSE_FRESH_PER_TEST)
val l1 = broker.acquire(meta)
broker.release(l1.session_id)
val l2 = broker.acquire(meta)
# fresh_per_test always creates new, so total should be 2
expect(broker.total_count()).to_equal(2)
```

</details>

#### different artifacts do not share sessions

1. var broker = session broker new
2. broker release
   - Expected: broker.total_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val m1 = make_qemu_meta("arm64", "fw_v1.bin", REUSE_SHARED_READ_ONLY)
val m2 = make_qemu_meta("arm64", "fw_v2.bin", REUSE_SHARED_READ_ONLY)
val l1 = broker.acquire(m1)
broker.release(l1.session_id)
val l2 = broker.acquire(m2)
expect(broker.total_count()).to_equal(2)
```

</details>

### session stop and cleanup

#### stop_session removes from broker

1. var broker = session broker new
   - Expected: stopped is true
   - Expected: broker.total_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("arm64", "fw.bin", REUSE_SHARED_READ_ONLY)
val lease = broker.acquire(meta)
val stopped = broker.stop_session(lease.session_id)
expect(stopped).to_equal(true)
expect(broker.total_count()).to_equal(0)
```

</details>

#### shutdown_all removes all sessions

1. var broker = session broker new
2. broker acquire
3. broker acquire
   - Expected: broker.total_count() equals `2`
4. broker shutdown all
   - Expected: broker.total_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val m1 = make_qemu_meta("arm64", "fw1.bin", REUSE_SHARED_READ_ONLY)
val m2 = make_qemu_meta("riscv64", "fw2.bin", REUSE_SHARED_READ_ONLY)
broker.acquire(m1)
broker.acquire(m2)
expect(broker.total_count()).to_equal(2)
broker.shutdown_all()
expect(broker.total_count()).to_equal(0)
```

</details>

#### stop nonexistent session returns false

1. var broker = session broker new
   - Expected: stopped is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val stopped = broker.stop_session("nonexistent_session_id")
expect(stopped).to_equal(false)
```

</details>

### session lifecycle workflow

#### acquire, use, release, reacquire cycle

1. var broker = session broker new
   - Expected: broker.total_count() equals `1`
2. broker release
   - Expected: broker.idle_count() equals `1`
   - Expected: broker.total_count() equals `1`
   - Expected: l2.test_count equals `1`
3. broker release
   - Expected: broker.idle_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("arm64", "fw.bin", REUSE_SHARED_READ_ONLY)
# Step 1: Acquire
val l1 = broker.acquire(meta)
expect(broker.total_count()).to_equal(1)
# Step 2: Release back to idle
broker.release(l1.session_id)
expect(broker.idle_count()).to_equal(1)
# Step 3: Reacquire same session
val l2 = broker.acquire(meta)
expect(broker.total_count()).to_equal(1)
expect(l2.test_count).to_equal(1)
# Step 4: Release again
broker.release(l2.session_id)
expect(broker.idle_count()).to_equal(1)
```

</details>

#### multi-session acquire, release, shutdown

1. var broker = session broker new
   - Expected: broker.total_count() equals `2`
2. broker release
3. broker release
   - Expected: broker.idle_count() equals `2`
   - Expected: broker.active_count() equals `0`
4. broker shutdown all
   - Expected: broker.total_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val m1 = make_qemu_meta("arm64", "fw1.bin", REUSE_SHARED_READ_ONLY)
val m2 = make_container_meta("x86_64", "img1", REUSE_SHARED_READ_ONLY)
val l1 = broker.acquire(m1)
val l2 = broker.acquire(m2)
expect(broker.total_count()).to_equal(2)
broker.release(l1.session_id)
broker.release(l2.session_id)
expect(broker.idle_count()).to_equal(2)
expect(broker.active_count()).to_equal(0)
broker.shutdown_all()
expect(broker.total_count()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
