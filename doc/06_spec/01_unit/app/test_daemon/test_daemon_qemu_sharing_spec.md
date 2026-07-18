# test_daemon_qemu_sharing_spec

> Test Daemon QEMU Session Sharing Specification

<!-- sdn-diagram:id=test_daemon_qemu_sharing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_qemu_sharing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_qemu_sharing_spec -> std
test_daemon_qemu_sharing_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_qemu_sharing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_qemu_sharing_spec

Test Daemon QEMU Session Sharing Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TDMN-031 to #TDMN-050 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/app/test_daemon/test_daemon_qemu_sharing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Test Daemon QEMU Session Sharing Specification

Tests QEMU session sharing patterns using the real QemuBroker:
session pooling, acquire/release cycles, multi-arch sessions,
binary hash matching, eviction under pressure, and warm session reuse.

## Scenarios

### QEMU Session Sharing

### read-only sharing via pooling

#### acquires session and marks it in-use

1. reset broker
   - Expected: total_session_count() equals `1`
   - Expected: entry.status equals `QEMU_IN_USE`
   - Expected: entry.arch equals `arm64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val entry = broker.acquire("arm64", "/bin/test")
expect(total_session_count()).to_equal(1)
expect(entry.status).to_equal(QEMU_IN_USE)
expect(entry.arch).to_equal("arm64")
```

</details>

#### reuses idle session with same key

1. reset broker
2. broker release
   - Expected: find_session_status(key) equals `QEMU_IDLE`
   - Expected: total_session_count() equals `1`
   - Expected: e2.session_key equals `key`
   - Expected: e2.test_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val e1 = broker.acquire("arm64", "/bin/test")
val key = e1.session_key
broker.release(key)
expect(find_session_status(key)).to_equal(QEMU_IDLE)
val e2 = broker.acquire("arm64", "/bin/test")
expect(total_session_count()).to_equal(1)
expect(e2.session_key).to_equal(key)
expect(e2.test_count).to_equal(2)
```

</details>

#### session becomes idle after release

1. reset broker
   - Expected: broker.sessions[0].status equals `QEMU_IN_USE`
2. broker release
   - Expected: broker.sessions[0].session_key equals `key`
   - Expected: broker.sessions[0].status equals `QEMU_IDLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val entry = broker.acquire("arm64", "/bin/test")
val key = entry.session_key
expect(broker.sessions[0].status).to_equal(QEMU_IN_USE)
broker.release(key)
expect(broker.sessions[0].session_key).to_equal(key)
expect(broker.sessions[0].status).to_equal(QEMU_IDLE)
```

</details>

#### tracks test count across reuse cycles

1. reset broker
2. broker release
   - Expected: entry.test_count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
var i: i64 = 0
while i < 4:
    val e = broker.acquire("arm64", "/bin/test")
    broker.release(e.session_key)
    i = i + 1
# After 4 acquire+release cycles, acquiring once more gives test_count=5
val entry = broker.acquire("arm64", "/bin/test")
expect(entry.test_count).to_equal(5)
```

</details>

### exclusive session patterns

#### in-use session is not reused for new acquire

1. reset broker
   - Expected: total_session_count() equals `2`
   - Expected: e2.session_key != e1.session_key is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val e1 = broker.acquire("arm64", "/bin/test")
# Session is IN_USE, so next acquire with same key creates new one
val e2 = broker.acquire("arm64", "/bin/test")
expect(total_session_count()).to_equal(2)
expect(e2.session_key != e1.session_key).to_equal(true)
```

</details>

#### active count tracks in-use sessions

1. reset broker
2. broker acquire
3. broker acquire
   - Expected: broker.active_count() equals `2`
   - Expected: broker.idle_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
broker.acquire("arm64", "/bin/test_a")
broker.acquire("arm64", "/bin/test_b")
expect(broker.active_count()).to_equal(2)
expect(broker.idle_count()).to_equal(0)
```

</details>

#### release reduces active and increases idle

1. reset broker
   - Expected: broker.active_count() equals `1`
2. broker release
   - Expected: broker.active_count() equals `0`
   - Expected: broker.idle_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val e1 = broker.acquire("arm64", "/bin/test")
expect(broker.active_count()).to_equal(1)
broker.release(e1.session_key)
expect(broker.active_count()).to_equal(0)
expect(broker.idle_count()).to_equal(1)
```

</details>

### multi-architecture

#### creates separate sessions per architecture

1. reset broker
   - Expected: total_session_count() equals `4`
   - Expected: keys[0] != keys[1] is true
   - Expected: keys[1] != keys[2] is true
   - Expected: keys[2] != keys[3] is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val keys = acquire_multi_arch()
expect(total_session_count()).to_equal(4)
# All keys should be different
expect(keys[0] != keys[1]).to_equal(true)
expect(keys[1] != keys[2]).to_equal(true)
expect(keys[2] != keys[3]).to_equal(true)
```

</details>

#### same arch different binary creates separate sessions

1. reset broker
   - Expected: total_session_count() equals `2`
   - Expected: e1.session_key != e2.session_key is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val e1 = broker.acquire("arm64", "/bin/test_a")
val e2 = broker.acquire("arm64", "/bin/test_b")
expect(total_session_count()).to_equal(2)
expect(e1.session_key != e2.session_key).to_equal(true)
```

</details>

#### same arch same binary reuses idle session

1. reset broker
2. broker release
   - Expected: total_session_count() equals `1`
   - Expected: e2.session_key equals `e1.session_key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val e1 = broker.acquire("arm64", "/bin/test")
broker.release(e1.session_key)
val e2 = broker.acquire("arm64", "/bin/test")
expect(total_session_count()).to_equal(1)
expect(e2.session_key).to_equal(e1.session_key)
```

</details>

### eviction with sharing

#### evicts oldest idle under pressure

1. reset broker with max
2. broker release
3. broker release
   - Expected: total_session_count() equals `2`
   - Expected: find_session_exists(k1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker_with_max(2)
val e1 = broker.acquire("a", "/bin/a1")
val k1 = e1.session_key
broker.release(k1)
val e2 = broker.acquire("b", "/bin/b2")
val k2 = e2.session_key
broker.release(k2)
# At max (2), acquiring new should evict oldest idle (k1)
val e3 = broker.acquire("c", "/bin/c3")
expect(total_session_count()).to_equal(2)
expect(find_session_exists(k1)).to_equal(false)
```

</details>

#### does not evict in-use sessions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val local_broker = qemu_broker_new(2)
# Two in-use sessions, can't evict either
val e1 = local_broker.acquire("a", "/bin/a1")
val e2 = local_broker.acquire("b", "/bin/b2")
# Exceeds max but nothing to evict
val e3 = local_broker.acquire("c", "/bin/c3")
expect(local_broker.sessions.len()).to_equal(3)
```

</details>

### session reuse

#### reuses session across sequential tests

1. reset broker
   - Expected: total_session_count() equals `1`
   - Expected: tc equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val tc = sequential_reuse_cycle("arm64", "/bin/test", 5)
expect(total_session_count()).to_equal(1)
# 5 cycles + 1 final acquire = 6
expect(tc).to_equal(6)
```

</details>

#### session key is deterministic for same inputs

1. reset broker
2. broker release
3. broker shutdown all
   - Expected: e2.session_key equals `k1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val e1 = broker.acquire("arm64", "/bin/same")
val k1 = e1.session_key
broker.release(k1)
broker.shutdown_all()
val e2 = broker.acquire("arm64", "/bin/same")
expect(e2.session_key).to_equal(k1)
```

</details>

### cleanup with shared sessions

#### keeps in-use sessions during cleanup

1. reset broker
2. broker cleanup idle
   - Expected: total_session_count() equals `1`
   - Expected: broker.sessions[0].session_key equals `entry.session_key`
   - Expected: broker.sessions[0].status equals `QEMU_IN_USE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val entry = broker.acquire("arm64", "/bin/test")
# cleanup_idle uses rt_time_now_unix_micros internally;
# with timeout_ms=0, only idle sessions older than 0ms are cleaned
broker.cleanup_idle(0)
expect(total_session_count()).to_equal(1)
expect(broker.sessions[0].session_key).to_equal(entry.session_key)
expect(broker.sessions[0].status).to_equal(QEMU_IN_USE)
```

</details>

#### shutdown removes all sessions

1. reset broker
2. broker acquire
3. broker acquire
4. broker acquire
   - Expected: total_session_count() equals `3`
5. broker shutdown all
   - Expected: total_session_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
broker.acquire("arm64", "/bin/a")
broker.acquire("riscv64", "/bin/b")
broker.acquire("x86_64", "/bin/c")
expect(total_session_count()).to_equal(3)
broker.shutdown_all()
expect(total_session_count()).to_equal(0)
```

</details>

### broker contract for kernel-path sharing (qemu-perf-session AC-6)

#### AC-6: two specs with same arch and kernel ELF share one session

1. reset broker
2. broker release
   - Expected: total_session_count() equals `1`
   - Expected: e2.session_key equals `key`
   - Expected: e2.test_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
# browser_in_qemu_spec and browser_in_qemu_pixel_spec both build
# simpleos_browser_x86_64.elf — acquire with same (arch, path) reuses
val kernel_elf = "build/os/simpleos_browser_x86_64.elf"
val e1 = broker.acquire("x86_64", kernel_elf)
val key = e1.session_key
broker.release(key)
val e2 = broker.acquire("x86_64", kernel_elf)
expect(total_session_count()).to_equal(1)
expect(e2.session_key).to_equal(key)
expect(e2.test_count).to_equal(2)
```

</details>

#### AC-6: different kernel ELFs for same arch get separate sessions

1. reset broker
   - Expected: total_session_count() equals `2`
   - Expected: e1.session_key != e2.session_key is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val e1 = broker.acquire("x86_64", "build/os/simpleos_browser_x86_64.elf")
val e2 = broker.acquire("x86_64", "build/os/simpleos_engine2d_min_x86_64.elf")
expect(total_session_count()).to_equal(2)
expect(e1.session_key != e2.session_key).to_equal(true)
```

</details>

### pool lifecycle

#### full cycle: acquire, use, release, reuse, shutdown

1. reset broker
   - Expected: broker.active_count() equals `1`
2. broker release
   - Expected: broker.idle_count() equals `1`
   - Expected: e2.session_key equals `key`
   - Expected: e2.test_count equals `2`
3. broker release
4. broker shutdown all
   - Expected: total_session_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
# Acquire
val e1 = broker.acquire("arm64", "/bin/test")
val key = e1.session_key
expect(broker.active_count()).to_equal(1)
# Release
broker.release(key)
expect(broker.idle_count()).to_equal(1)
# Reuse
val e2 = broker.acquire("arm64", "/bin/test")
expect(e2.session_key).to_equal(key)
expect(e2.test_count).to_equal(2)
# Release again
broker.release(key)
# Shutdown
broker.shutdown_all()
expect(total_session_count()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
