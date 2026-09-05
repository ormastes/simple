# test_daemon_mcp_session_spec

> Test Daemon SessionBroker Specification

<!-- sdn-diagram:id=test_daemon_mcp_session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_mcp_session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_mcp_session_spec -> std
test_daemon_mcp_session_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_mcp_session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_mcp_session_spec

Test Daemon SessionBroker Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TDMN-091 to #TDMN-110 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/app/test_daemon/test_daemon_mcp_session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Test Daemon SessionBroker Specification

Tests SessionBroker acquire/release/status flow, lease state transitions,
multi-kind session counting, and status reporting. Replaces MCP debug
session mock tests with real broker API tests.

## Scenarios

### SessionBroker

### broker creation

#### creates empty broker

1. var broker = session broker new
   - Expected: broker.total_count() equals `0`
   - Expected: broker.active_count() equals `0`
   - Expected: broker.idle_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
expect(broker.total_count()).to_equal(0)
expect(broker.active_count()).to_equal(0)
expect(broker.idle_count()).to_equal(0)
```

</details>

#### status report is non-empty

1. var broker = session broker new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val report = broker.status_report()
expect(report).to_contain("Session Broker Status")
expect(report).to_contain("Total sessions: 0")
```

</details>

### acquire and release

#### acquire creates a new lease

1. var broker = session broker new
   - Expected: broker.total_count() equals `1`
   - Expected: lease.key.kind equals `SESSION_KIND_QEMU_VM`
   - Expected: lease.key.target equals `riscv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("riscv64")
val lease = broker.acquire(meta)
expect(broker.total_count()).to_equal(1)
expect(lease.key.kind).to_equal(SESSION_KIND_QEMU_VM)
expect(lease.key.target).to_equal("riscv64")
```

</details>

#### release transitions lease to idle

1. var broker = session broker new
2. broker release


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("arm64")
val lease = broker.acquire(meta)
broker.release(lease.session_id)
expect(broker.idle_count()).to_be_greater_than(0)
```

</details>

#### acquire fresh_per_test always creates new

1. var broker = session broker new
   - Expected: broker.total_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_local_meta("test/unit/foo_spec.spl")
val lease1 = broker.acquire(meta)
val lease2 = broker.acquire(meta)
# Fresh per test creates a new lease each time
expect(broker.total_count()).to_equal(2)
```

</details>

#### acquire reuses idle session with matching key

1. var broker = session broker new
2. broker release
   - Expected: broker.total_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_container_meta("db_test")
val lease1 = broker.acquire(meta)
broker.release(lease1.session_id)
# Second acquire should reuse the idle lease
val lease2 = broker.acquire(meta)
# Should not have created a third session — reused the idle one
expect(broker.total_count()).to_equal(1)
```

</details>

### session counting

#### counts by kind

1. var broker = session broker new
2. broker acquire
3. broker acquire
4. broker acquire
   - Expected: broker.count_by_kind(SESSION_KIND_QEMU_VM) equals `2`
   - Expected: broker.count_by_kind(SESSION_KIND_CONTAINER) equals `1`
   - Expected: broker.count_by_kind(SESSION_KIND_SERVICE) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
broker.acquire(make_qemu_meta("riscv64"))
broker.acquire(make_qemu_meta("arm64"))
broker.acquire(make_container_meta("db"))
expect(broker.count_by_kind(SESSION_KIND_QEMU_VM)).to_equal(2)
expect(broker.count_by_kind(SESSION_KIND_CONTAINER)).to_equal(1)
expect(broker.count_by_kind(SESSION_KIND_SERVICE)).to_equal(0)
```

</details>

#### counts total sessions

1. var broker = session broker new
2. broker acquire
3. broker acquire
4. broker acquire
   - Expected: broker.total_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
broker.acquire(make_qemu_meta("riscv64"))
broker.acquire(make_container_meta("redis"))
broker.acquire(make_service_meta("api"))
expect(broker.total_count()).to_equal(3)
```

</details>

### status report

#### reports active and idle counts

1. var broker = session broker new


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("arm64")
val lease = broker.acquire(meta)
val report = broker.status_report()
expect(report).to_contain("Total sessions: 1")
expect(report).to_contain("QEMU: 1")
```

</details>

#### reports mixed session types

1. var broker = session broker new
2. broker acquire
3. broker acquire
4. broker acquire


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
broker.acquire(make_qemu_meta("arm64"))
broker.acquire(make_qemu_meta("riscv64"))
broker.acquire(make_container_meta("db"))
val report = broker.status_report()
expect(report).to_contain("Total sessions: 3")
expect(report).to_contain("QEMU: 2")
expect(report).to_contain("Container: 1")
```

</details>

### stop session

#### stop removes session from broker

1. var broker = session broker new
   - Expected: stopped is true
   - Expected: broker.total_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_qemu_meta("arm64")
val lease = broker.acquire(meta)
val stopped = broker.stop_session(lease.session_id)
expect(stopped).to_equal(true)
expect(broker.total_count()).to_equal(0)
```

</details>

#### stop returns false for nonexistent session

1. var broker = session broker new
   - Expected: stopped is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val stopped = broker.stop_session("nonexistent_id")
expect(stopped).to_equal(false)
```

</details>

### shutdown all

#### shuts down all sessions

1. var broker = session broker new
2. broker acquire
3. broker acquire
4. broker acquire
   - Expected: broker.total_count() equals `3`
5. broker shutdown all
   - Expected: broker.total_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
broker.acquire(make_qemu_meta("arm64"))
broker.acquire(make_container_meta("db"))
broker.acquire(make_service_meta("api"))
expect(broker.total_count()).to_equal(3)
broker.shutdown_all()
expect(broker.total_count()).to_equal(0)
```

</details>

### multi-session coordination

#### manages 4 concurrent sessions of different kinds

1. var broker = session broker new
   - Expected: broker.total_count() equals `4`
   - Expected: broker.count_by_kind(SESSION_KIND_QEMU_VM) equals `2`
   - Expected: broker.count_by_kind(SESSION_KIND_CONTAINER) equals `1`
   - Expected: broker.count_by_kind(SESSION_KIND_SERVICE) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val l1 = broker.acquire(make_qemu_meta("arm64"))
val l2 = broker.acquire(make_qemu_meta("riscv64"))
val l3 = broker.acquire(make_container_meta("postgres"))
val l4 = broker.acquire(make_service_meta("http_api"))
expect(broker.total_count()).to_equal(4)
expect(broker.count_by_kind(SESSION_KIND_QEMU_VM)).to_equal(2)
expect(broker.count_by_kind(SESSION_KIND_CONTAINER)).to_equal(1)
expect(broker.count_by_kind(SESSION_KIND_SERVICE)).to_equal(1)
```

</details>

#### releases and re-acquires correctly

1. var broker = session broker new
2. broker release
   - Expected: broker.total_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val meta = make_container_meta("redis")
val lease1 = broker.acquire(meta)
broker.release(lease1.session_id)
expect(broker.idle_count()).to_be_greater_than(0)
val lease2 = broker.acquire(meta)
# Should reuse the released session (exclusive reused mode)
expect(broker.total_count()).to_equal(1)
```

</details>

### isolation

#### different targets create separate sessions

1. var broker = session broker new
2. broker acquire
3. broker acquire
4. broker acquire
   - Expected: broker.total_count() equals `3`
   - Expected: broker.count_by_kind(SESSION_KIND_QEMU_VM) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
broker.acquire(make_qemu_meta("arm64"))
broker.acquire(make_qemu_meta("riscv64"))
broker.acquire(make_qemu_meta("x86_64"))
expect(broker.total_count()).to_equal(3)
expect(broker.count_by_kind(SESSION_KIND_QEMU_VM)).to_equal(3)
```

</details>

#### stop one session does not affect others

1. var broker = session broker new
2. broker stop session
   - Expected: broker.total_count() equals `1`
   - Expected: broker.count_by_kind(SESSION_KIND_CONTAINER) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = session_broker_new()
val l1 = broker.acquire(make_qemu_meta("arm64"))
val l2 = broker.acquire(make_container_meta("db"))
broker.stop_session(l1.session_id)
expect(broker.total_count()).to_equal(1)
expect(broker.count_by_kind(SESSION_KIND_CONTAINER)).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
