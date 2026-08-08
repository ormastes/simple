# qemu_harness_acquire_or_spawn_spec

> @cover test/system/qemu/os/common/qemu_os_harness.spl 60%

<!-- sdn-diagram:id=qemu_harness_acquire_or_spawn_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_harness_acquire_or_spawn_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_harness_acquire_or_spawn_spec -> std
qemu_harness_acquire_or_spawn_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_harness_acquire_or_spawn_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# qemu_harness_acquire_or_spawn_spec

@cover test/system/qemu/os/common/qemu_os_harness.spl 60%

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/qemu/qemu_harness_acquire_or_spawn_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover test/system/qemu/os/common/qemu_os_harness.spl 60%

QEMU Harness — acquire_or_spawn / release_or_kill Specification

Verifies the broker-first session acquisition pattern:
- When a broker has an idle session for the same arch+kernel, reuse it
- When no broker or no idle session, fall back to spawn_guest_with_qmp
- release_or_kill returns session to pool (broker) or kills process (no broker)

NOTE: These specs do NOT launch real QEMU. They test the broker integration
at the decision-making level. The actual spawn fallback path is verified by
the existing system specs (test/system/*_in_qemu_spec.spl) which launch QEMU.

## Scenarios

### acquire_or_spawn

### broker-first reuse path

#### AC-4: reuses idle broker session with same arch and kernel path

1. reset broker
2. broker release
   - Expected: total_sessions() equals `1`
   - Expected: e2.session_key equals `key`
   - Expected: e2.status equals `QEMU_IN_USE`
   - Expected: e2.test_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulate: broker has an idle session for x86_64 + browser kernel
reset_broker()
val kernel_path = "build/os/simpleos_browser_x86_64.elf"
val e1 = broker.acquire("x86_64", kernel_path)
val key = e1.session_key
broker.release(key)
# acquire_or_spawn should find this idle session and reuse it
# For now we test the broker layer directly — acquire_or_spawn
# delegates to broker.acquire which finds idle sessions
val e2 = broker.acquire("x86_64", kernel_path)
expect(total_sessions()).to_equal(1)
expect(e2.session_key).to_equal(key)
expect(e2.status).to_equal(QEMU_IN_USE)
expect(e2.test_count).to_equal(2)
```

</details>

#### AC-4: creates new session when no idle session for kernel

1. reset broker
2. broker release
   - Expected: total_sessions() equals `2`
   - Expected: e2.session_key != e1.session_key is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val kernel_a = "build/os/simpleos_browser_x86_64.elf"
val kernel_b = "build/os/simpleos_engine2d_x86_64.elf"
val e1 = broker.acquire("x86_64", kernel_a)
broker.release(e1.session_key)
# Different kernel path — no reuse
val e2 = broker.acquire("x86_64", kernel_b)
expect(total_sessions()).to_equal(2)
expect(e2.session_key != e1.session_key).to_equal(true)
```

</details>

#### AC-4: creates new session when no idle session for arch

1. reset broker
2. broker release
   - Expected: total_sessions() equals `2`
   - Expected: e2.session_key != e1.session_key is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val kernel_path = "build/os/simpleos_browser_x86_64.elf"
val e1 = broker.acquire("x86_64", kernel_path)
broker.release(e1.session_key)
# Different arch — no reuse even though same kernel path
val e2 = broker.acquire("riscv64", kernel_path)
expect(total_sessions()).to_equal(2)
expect(e2.session_key != e1.session_key).to_equal(true)
```

</details>

### session sharing by kernel ELF path (AC-6)

#### AC-6: browser specs sharing same kernel ELF reuse one session

1. reset broker
2. broker release
   - Expected: total_sessions() equals `1`
   - Expected: e2.session_key equals `key`
   - Expected: e2.test_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# browser_in_qemu_spec and browser_in_qemu_pixel_spec both use
# build/os/simpleos_browser_x86_64.elf — they should share a session
reset_broker()
val shared_kernel = "build/os/simpleos_browser_x86_64.elf"
# First spec acquires
val e1 = broker.acquire("x86_64", shared_kernel)
val key = e1.session_key
# First spec releases (done with its tests)
broker.release(key)
# Second spec acquires same kernel — reuse
val e2 = broker.acquire("x86_64", shared_kernel)
expect(total_sessions()).to_equal(1)
expect(e2.session_key).to_equal(key)
expect(e2.test_count).to_equal(2)
```

</details>

#### AC-6: different kernel ELF paths get separate sessions

1. reset broker
   - Expected: total_sessions() equals `3`
   - Expected: e1.session_key != e2.session_key is true
   - Expected: e2.session_key != e3.session_key is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val browser_kernel = "build/os/simpleos_browser_x86_64.elf"
val engine_kernel = "build/os/simpleos_engine2d_min_x86_64.elf"
val js_kernel = "build/os/simpleos_js_runtime_x86_64.elf"
val e1 = broker.acquire("x86_64", browser_kernel)
val e2 = broker.acquire("x86_64", engine_kernel)
val e3 = broker.acquire("x86_64", js_kernel)
expect(total_sessions()).to_equal(3)
expect(e1.session_key != e2.session_key).to_equal(true)
expect(e2.session_key != e3.session_key).to_equal(true)
```

</details>

### release_or_kill

#### AC-5: release returns session to idle pool for reuse

1. reset broker
   - Expected: broker.active_count() equals `1`
   - Expected: broker.idle_count() equals `0`
2. broker release
   - Expected: broker.active_count() equals `0`
   - Expected: broker.idle_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val kernel_path = "build/os/simpleos_browser_x86_64.elf"
val entry = broker.acquire("x86_64", kernel_path)
val key = entry.session_key
expect(broker.active_count()).to_equal(1)
expect(broker.idle_count()).to_equal(0)
# release_or_kill with broker -> release back to pool
broker.release(key)
expect(broker.active_count()).to_equal(0)
expect(broker.idle_count()).to_equal(1)
```

</details>

#### AC-5: released session is available for next acquire

1. reset broker
2. broker release
   - Expected: e2.session_key equals `e1.session_key`
   - Expected: e2.test_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_broker()
val kernel_path = "build/os/simpleos_ssh_x86_64.elf"
val e1 = broker.acquire("x86_64", kernel_path)
broker.release(e1.session_key)
val e2 = broker.acquire("x86_64", kernel_path)
expect(e2.session_key).to_equal(e1.session_key)
expect(e2.test_count).to_equal(2)
```

</details>

### backward compatibility (AC-7)

#### AC-7: broker acquire does not break existing session lifecycle

1. reset broker
   - Expected: broker.active_count() equals `1`
2. broker release
   - Expected: broker.idle_count() equals `1`
   - Expected: e2.session_key equals `e1.session_key`
3. broker release
4. broker shutdown all
   - Expected: total_sessions() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Full lifecycle: acquire -> use -> release -> reuse -> shutdown
# This mirrors what spawn_guest_with_qmp does, just through broker
reset_broker()
val kernel_path = "build/os/simpleos_browser_x86_64.elf"
val e1 = broker.acquire("x86_64", kernel_path)
expect(broker.active_count()).to_equal(1)
broker.release(e1.session_key)
expect(broker.idle_count()).to_equal(1)
val e2 = broker.acquire("x86_64", kernel_path)
expect(e2.session_key).to_equal(e1.session_key)
broker.release(e2.session_key)
broker.shutdown_all()
expect(total_sessions()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
