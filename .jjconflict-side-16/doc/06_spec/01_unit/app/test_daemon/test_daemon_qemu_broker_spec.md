# Test Daemon Qemu Broker Specification

> <details>

<!-- sdn-diagram:id=test_daemon_qemu_broker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_qemu_broker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_qemu_broker_spec -> std
test_daemon_qemu_broker_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_qemu_broker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Daemon Qemu Broker Specification

## Scenarios

### QemuBroker

#### creates a new session on first acquire

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val broker = qemu_broker_new(4)
val session = broker.acquire("arm64", "/bin/test-a")
expect(session.arch).to_equal("arm64")
expect(session.status).to_equal(QEMU_IN_USE)
expect(broker.active_count()).to_equal(1)
expect(broker.idle_count()).to_equal(0)
```

</details>

#### reuses an idle session with the same key

1. broker release
   - Expected: s2.session_key equals `s1.session_key`
   - Expected: s2.test_count equals `2`
   - Expected: broker.active_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val broker = qemu_broker_new(4)
val s1 = broker.acquire("arm64", "/bin/test-a")
broker.release(s1.session_key)
val s2 = broker.acquire("arm64", "/bin/test-a")

expect(s2.session_key).to_equal(s1.session_key)
expect(s2.test_count).to_equal(2)
expect(broker.active_count()).to_equal(1)
```

</details>

#### creates separate sessions for different binaries or architectures

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val broker = qemu_broker_new(4)
val a = broker.acquire("arm64", "/bin/test-a")
val b = broker.acquire("arm64", "/bin/test-b")
val c = broker.acquire("riscv64", "/bin/test-a")

expect(a.session_key != b.session_key).to_equal(true)
expect(a.session_key != c.session_key).to_equal(true)
expect(broker.active_count()).to_equal(3)
```

</details>

#### marks released sessions idle

1. broker release
   - Expected: broker.active_count() equals `0`
   - Expected: broker.idle_count() equals `1`
   - Expected: broker.sessions[0].status equals `QEMU_IDLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val broker = qemu_broker_new(4)
val session = broker.acquire("arm64", "/bin/test-a")
broker.release(session.session_key)

expect(broker.active_count()).to_equal(0)
expect(broker.idle_count()).to_equal(1)
expect(broker.sessions[0].status).to_equal(QEMU_IDLE)
```

</details>

#### evicts the oldest idle session when at limit

1. broker release
2. broker release
3. broker acquire
   - Expected: broker.sessions.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val broker = qemu_broker_new(2)
val s1 = broker.acquire("a", "/bin/a")
broker.release(s1.session_key)
val s2 = broker.acquire("b", "/bin/b")
broker.release(s2.session_key)

broker.acquire("c", "/bin/c")
expect(broker.sessions.len()).to_equal(2)
```

</details>

#### cleans up idle sessions and can shut down all

1. broker release
2. broker cleanup idle
   - Expected: broker.sessions.len() equals `0`
3. broker acquire
4. broker acquire
   - Expected: broker.sessions.len() equals `2`
5. broker shutdown all
   - Expected: broker.sessions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val broker = qemu_broker_new(4)
val s1 = broker.acquire("arm64", "/bin/test-a")
broker.release(s1.session_key)
broker.cleanup_idle(0)
expect(broker.sessions.len()).to_equal(0)

broker.acquire("x", "/bin/x")
broker.acquire("y", "/bin/y")
expect(broker.sessions.len()).to_equal(2)
broker.shutdown_all()
expect(broker.sessions.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_daemon/test_daemon_qemu_broker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- QemuBroker

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
