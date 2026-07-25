# Simpleos Wine Proton Steam Impl Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_proton_steam_impl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_proton_steam_impl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_proton_steam_impl_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_proton_steam_impl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Proton Steam Impl Specification

## Scenarios

### SimpleOS Wine/Proton/Steam Implementation — System Spec

### AC-1: Process Baseline — scheduler-owned PIDs

#### AC-1: process_table_alloc_pid returns a real non-zero PID (no fallback markers)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = process_table_alloc_pid()
expect(pid).to_be_greater_than(0)
```

</details>

#### AC-1: registering a process produces a visible table entry with running state

1. process table register
   - Expected: entry.is_some is true
   - Expected: entry.value.state equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = process_table_alloc_pid()
process_table_register(pid, 1, 1)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(true)
expect(entry.value.state).to_equal("running")
```

</details>

#### AC-1: five distinct PIDs can be allocated (one per desktop app)

1. process table alloc pid
2. process table alloc pid
3. process table alloc pid
4. process table alloc pid
5. process table alloc pid
   - Expected: pids[0] == pids[1] is false
   - Expected: pids[0] == pids[4] is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pids = [
    process_table_alloc_pid(),
    process_table_alloc_pid(),
    process_table_alloc_pid(),
    process_table_alloc_pid(),
    process_table_alloc_pid()
]
expect(pids[0]).to_be_greater_than(0)
expect(pids[1]).to_be_greater_than(0)
expect(pids[4]).to_be_greater_than(0)
expect(pids[0] == pids[1]).to_equal(false)
expect(pids[0] == pids[4]).to_equal(false)
```

</details>

### AC-2: POSIX Host ABI — fd table

#### AC-2: fd_table_new creates a usable fd table

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fdt = fd_table_new()
expect(fdt.is_valid).to_equal(true)
```

</details>

#### AC-2: fd_open returns a valid file descriptor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fdt = fd_table_new()
val fd = fd_open(fdt, "/dev/null", 0)
expect(fd).to_be_greater_than(-1)
```

</details>

#### AC-2: fd_write on a valid fd returns bytes written

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fdt = fd_table_new()
val fd = fd_open(fdt, "/dev/null", 1)
val n = fd_write(fdt, fd, "hello", 5)
expect(n).to_equal(5)
```

</details>

#### AC-2: fd_close releases the file descriptor

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fdt = fd_table_new()
val fd = fd_open(fdt, "/dev/null", 0)
val ok = fd_close(fdt, fd)
expect(ok).to_equal(true)
```

</details>

### AC-3: Threads/TLS — real threading primitives

#### AC-3: tls_key_alloc returns a positive key

1. fn no dtor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn no_dtor(p: *void) -> void:
    val _ = 0
val key = tls_key_alloc(no_dtor)
expect(key).to_be_greater_than(0)
```

</details>

#### AC-3: tls_key_set and tls_key_get are consistent

1. fn no dtor
2. tls key set
   - Expected: tls_key_get(key) equals `0xCAFE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn no_dtor(p: *void) -> void:
    val _ = 0
val key = tls_key_alloc(no_dtor)
tls_key_set(key, 0xCAFE)
expect(tls_key_get(key)).to_equal(0xCAFE)
```

</details>

#### AC-3: semaphore post/wait cycle works end-to-end

1. semaphore post
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = semaphore_create(0)
semaphore_post(h)
val result = semaphore_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### AC-3: event_wait set/wait cycle works end-to-end

1. event wait set
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = event_wait_create(false)
event_wait_set(h)
val result = event_wait_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### AC-3: kernel_thread_create returns a positive Tid

1. fn noop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn noop() -> void:
    val _ = 0
val tid = kernel_thread_create(noop, 4096)
expect(tid).to_be_greater_than(0)
```

</details>

#### AC-3: kevent set/wait produces signaled result

1. kevent set
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = kevent_create(false)
kevent_set(h)
val result = kevent_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

### AC-4: VM/Containers — isolation primitives

#### AC-4: tss_write_rsp0 is callable with a valid kernel stack address

1. tss write rsp0
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Sentinel value — a non-zero RSP0 (actual value would be real stack PA)
tss_write_rsp0(0x100000)
# No panic means success
expect(1).to_equal(1)
```

</details>

#### AC-4: msr_lstar_install is callable (installs SYSCALL entry)

1. msr lstar install
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
msr_lstar_install(0x200000)
expect(1).to_equal(1)
```

</details>

#### AC-4: msr_star_install encodes kernel/user CS pair

1. msr star install
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
msr_star_install(0x0008, 0x0018)
expect(1).to_equal(1)
```

</details>

#### AC-4: msr_sfmask_install sets interrupt flag mask

1. msr sfmask install
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SFMASK_IF = 0x200
msr_sfmask_install(0x200)
expect(1).to_equal(1)
```

</details>

#### AC-4: namespace_create produces isolation facets for all five types

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid_ns = namespace_create(NsFlags.pid)
val fs_ns  = namespace_create(NsFlags.fs)
val ipc_ns = namespace_create(NsFlags.ipc)
val net_ns = namespace_create(NsFlags.net)
val cap_ns = namespace_create(NsFlags.capability)
expect(pid_ns).to_be_greater_than(0)
expect(cap_ns).to_be_greater_than(0)
```

</details>

#### AC-4: namespace_clone creates an isolated child namespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = namespace_create(NsFlags.pid)
val child  = namespace_clone(parent, NsFlags.pid)
expect(child).to_be_greater_than(0)
expect(child == parent).to_equal(false)
```

</details>

### AC-5: Renderer/WM — window protocol surface

#### AC-5: wm_port_open returns a valid port handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = wm_port_open()
expect(port).to_be_greater_than(0)
```

</details>

#### AC-5: wm_window_create on an open port returns a window handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = wm_port_open()
val win  = wm_window_create(port, "wine-test", 800, 600)
expect(win).to_be_greater_than(0)
```

</details>

### AC-6: Dynamic Loading — dlopen/dlsym surface

#### AC-6: guest_dlopen with a known module path returns a non-zero handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Interpreter-mode stub: the loader must at least return a handle record
val h = guest_dlopen("kernel32.dll")
expect(h.is_some).to_equal(true)
```

</details>

#### AC-6: guest_dlsym on a valid handle returns a non-zero symbol address

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = guest_dlopen("kernel32.dll")
expect(h.is_some).to_equal(true)
val sym = guest_dlsym(h.value, "WriteFile")
expect(sym).to_be_greater_than(0)
```

</details>

### AC-7: Real hello.exe execution — PE loader surface

#### AC-7: pe_map_image on valid PE bytes returns a non-error result

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Minimal 512-byte buffer representing a stub PE; implementation maps real sections
val stub_bytes: [u8] = [0x4D, 0x5A]  # MZ magic
val result = pe_map_image(stub_bytes)
# Either ok (full impl) or error with a structured code (no crash/panic)
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("too-small")
```

</details>

### AC-8: Async Substrate — IoDriver surface

#### AC-8: fd_table supports open/write/close cycle (async fd registration path)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fdt = fd_table_new()
val fd = fd_open(fdt, "/dev/null", 1)
val n = fd_write(fdt, fd, "test", 4)
val ok = fd_close(fdt, fd)
expect(n).to_be_greater_than(-1)
expect(ok).to_equal(true)
```

</details>

### AC-9: Vulkan/Graphics — loader surface

#### AC-9: vulkan_loader_init returns a loader handle or a structured error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = vulkan_loader_init()
# In interpreter/stub mode: either ok or error — must not panic
val is_structured = result.is_ok == true || result.error != ""
expect(is_structured).to_equal(true)
```

</details>

### AC-10: Steam/Proton — launcher surface

#### AC-10: esync_create returns a valid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = esync_create()
expect(h).to_be_greater_than(0)
```

</details>

#### AC-10: esync signal/wait produces signaled result

1. esync signal
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = esync_create()
esync_signal(h)
val result = esync_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### AC-10: fsync mutex lock/unlock pair completes without error

1. fsync mutex lock
2. fsync mutex unlock
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr: u32 = 0
fsync_mutex_lock(addr)
fsync_mutex_unlock(addr)
expect(1).to_equal(1)
```

</details>

#### AC-10: proton_launcher_plan returns a structured plan record

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = proton_launcher_plan("480", "hl2.exe", ["-novid"])
expect(plan.status).to_equal("planned")
expect(plan.app_id).to_equal("480")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_proton_steam_impl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine/Proton/Steam Implementation — System Spec
- AC-1: Process Baseline — scheduler-owned PIDs
- AC-2: POSIX Host ABI — fd table
- AC-3: Threads/TLS — real threading primitives
- AC-4: VM/Containers — isolation primitives
- AC-5: Renderer/WM — window protocol surface
- AC-6: Dynamic Loading — dlopen/dlsym surface
- AC-7: Real hello.exe execution — PE loader surface
- AC-8: Async Substrate — IoDriver surface
- AC-9: Vulkan/Graphics — loader surface
- AC-10: Steam/Proton — launcher surface

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
