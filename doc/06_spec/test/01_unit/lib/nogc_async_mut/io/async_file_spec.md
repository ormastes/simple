# Async File I/O Specification

> AsyncFileHandle wraps sync FileHandle with thread pool offload. Regular files don't support epoll, so async file I/O dispatches blocking operations to a thread pool.

<!-- sdn-diagram:id=async_file_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_file_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_file_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_file_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async File I/O Specification

AsyncFileHandle wraps sync FileHandle with thread pool offload. Regular files don't support epoll, so async file I/O dispatches blocking operations to a thread pool.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #IO-ASYNC-FILE |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/nogc_async_mut/io/async_file_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

AsyncFileHandle wraps sync FileHandle with thread pool offload.
Regular files don't support epoll, so async file I/O dispatches
blocking operations to a thread pool.

## Syntax

```simple
val fh = await AsyncFileHandle.open("data.txt", FileMode.ReadOnly)?
val content = await fh.read_text()?
await fh.close()?

# One-shot:
val text = await AsyncFile.read("config.sdn")?
await AsyncFile.write("output.txt", text)?
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| AsyncFileHandle | Thread-pool async file — AsyncRead+AsyncWrite+AsyncSeek+AsyncClose |
| AsyncFile | Static async convenience methods |
| ThreadPool | Worker threads for blocking offload |

## Behavior

- All operations dispatch to thread pool via pool.spawn()
- is_open() remains sync (checks inner handle state)
- AsyncFile.read/write/exists/delete wrap handle lifecycle
- Mirror of sync API — add `await` prefix

## Sync vs Async Comparison

```simple
# Sync:
val fh = FileHandle.open("data.txt", FileMode.ReadOnly)?
val text = fh.read_text()?
fh.close()?

# Async — identical names, just add await:
val fh = await AsyncFileHandle.open("data.txt", FileMode.ReadOnly)?
val text = await fh.read_text()?
await fh.close()?
```

## Scenarios

### ThreadPool

#### construction

#### documents thread pool creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val pool = ThreadPool.new(4)
# val result = await pool.spawn(\\: expensive_computation())
pass
```

</details>

#### documents default pool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val pool = ThreadPool.default()  # 4 threads
pass
```

</details>

### AsyncFileHandle

#### factory methods

#### documents open

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val fh = await AsyncFileHandle.open("data.txt", FileMode.ReadOnly)?
pass
```

</details>

#### documents read_file shortcut

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val fh = await AsyncFileHandle.read_file("data.txt")?
pass
```

</details>

#### documents create shortcut

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val fh = await AsyncFileHandle.create("output.txt")?
pass
```

</details>

#### AsyncRead operations

#### documents read

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val fh = await AsyncFileHandle.read_file("data.bin")?
# val chunk = await fh.read(1024)?
pass
```

</details>

#### documents read_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val fh = await AsyncFileHandle.read_file("data.txt")?
# val text = await fh.read_text()?
pass
```

</details>

#### documents read_line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val fh = await AsyncFileHandle.read_file("data.csv")?
# val line = await fh.read_line()?
pass
```

</details>

#### AsyncWrite operations

#### documents write_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val fh = await AsyncFileHandle.create("output.txt")?
# await fh.write_text("hello async")?
# await fh.flush()?
# await fh.close()?
pass
```

</details>

#### AsyncSeek operations

#### documents seek and rewind

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val fh = await AsyncFileHandle.open("data.txt", FileMode.ReadWrite)?
# await fh.write_text("content")?
# await fh.rewind()?
# val text = await fh.read_text()?
pass
```

</details>

#### is_open remains sync

#### documents sync is_open

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val fh = await AsyncFileHandle.read_file("data.txt")?
# expect fh.is_open() == true  # sync call
# await fh.close()?
# expect fh.is_open() == false  # sync call
pass
```

</details>

### AsyncFile

#### read and write

#### documents async read

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val text = await AsyncFile.read("config.sdn")?
pass
```

</details>

#### documents async write

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# await AsyncFile.write("output.txt", "hello async")?
pass
```

</details>

#### documents async read_bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val data = await AsyncFile.read_bytes("data.bin")?
pass
```

</details>

#### exists and delete

#### documents async exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val found = await AsyncFile.exists("config.sdn")
pass
```

</details>

#### documents async delete

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# await AsyncFile.delete("temp.txt")?
pass
```

</details>

#### mirrors sync File

#### documents sync vs async

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Sync:
#   val text = File.read("config.sdn")?
#   File.write("out.txt", text)?
#
# Async:
#   val text = await AsyncFile.read("config.sdn")?
#   await AsyncFile.write("out.txt", text)?
pass
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
