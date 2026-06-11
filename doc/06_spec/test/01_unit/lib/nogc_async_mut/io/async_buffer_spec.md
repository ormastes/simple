# Async Buffered I/O Specification

> AsyncBufferedReader and AsyncBufferedWriter wrap any AsyncRead/AsyncWrite, reducing async call overhead with in-memory buffering. Same structure as sync variants, with Future-wrapped operations.

<!-- sdn-diagram:id=async_buffer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_buffer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_buffer_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_buffer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Buffered I/O Specification

AsyncBufferedReader and AsyncBufferedWriter wrap any AsyncRead/AsyncWrite, reducing async call overhead with in-memory buffering. Same structure as sync variants, with Future-wrapped operations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #IO-ASYNC-BUFFER |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/nogc_async_mut/io/async_buffer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

AsyncBufferedReader and AsyncBufferedWriter wrap any AsyncRead/AsyncWrite,
reducing async call overhead with in-memory buffering. Same structure as
sync variants, with Future-wrapped operations.

## Syntax

```simple
val raw = await AsyncFileHandle.read_file("big.bin")?
val reader = AsyncBufferedReader.new(raw)
val line = await reader.read_line()?
await reader.close()?

val out = await AsyncFileHandle.create("output.log")?
val writer = AsyncBufferedWriter.new(out)
await writer.write_text("buffered line\\n")?
await writer.flush()?
await writer.close()?
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| AsyncBufferedReader | Wraps AsyncRead — buffers reads (default 8KB) |
| AsyncBufferedWriter | Wraps AsyncWrite — buffers writes (default 8KB) |
| with_capacity | Custom buffer size constructor |

## Behavior

- AsyncBufferedReader reads from buffer first, refills from inner async
- AsyncBufferedWriter accumulates writes, flushes when full or on flush()
- close() on AsyncBufferedWriter flushes then closes inner
- Works with any AsyncRead/AsyncWrite (AsyncFileHandle, AsyncTcpStream, etc.)

## Sync vs Async Comparison

```simple
# Sync:
val reader = BufferedReader.new(file_handle)
val line = reader.read_line()?

# Async — same API:
val reader = AsyncBufferedReader.new(async_file_handle)
val line = await reader.read_line()?
```

## Scenarios

### AsyncBufferedReader

#### construction

#### documents default construction

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val raw = await AsyncFileHandle.read_file("data.csv")?
# val reader = AsyncBufferedReader.new(raw)
# expect reader.buf_size == 8192
pass
```

</details>

#### documents custom capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val raw = await AsyncFileHandle.read_file("data.csv")?
# val reader = AsyncBufferedReader.with_capacity(raw, 16384)
# expect reader.buf_size == 16384
pass
```

</details>

#### reading

#### documents read_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val raw = await AsyncFileHandle.read_file("data.txt")?
# val reader = AsyncBufferedReader.new(raw)
# val content = await reader.read_text()?
pass
```

</details>

#### documents read_line

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val raw = await AsyncFileHandle.read_file("data.csv")?
# val reader = AsyncBufferedReader.new(raw)
# val header = await reader.read_line()?
# val row1 = await reader.read_line()?
pass
```

</details>

#### documents read_all

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val raw = await AsyncFileHandle.read_file("data.bin")?
# val reader = AsyncBufferedReader.new(raw)
# val data = await reader.read_all()?
pass
```

</details>

#### close

#### documents async close

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val raw = await AsyncFileHandle.read_file("data.txt")?
# val reader = AsyncBufferedReader.new(raw)
# await reader.close()?
pass
```

</details>

### AsyncBufferedWriter

#### construction

#### documents default construction

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val raw = await AsyncFileHandle.create("output.log")?
# val writer = AsyncBufferedWriter.new(raw)
pass
```

</details>

#### documents custom capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val raw = await AsyncFileHandle.create("output.log")?
# val writer = AsyncBufferedWriter.with_capacity(raw, 32768)
pass
```

</details>

#### writing

#### documents buffered write + flush

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val raw = await AsyncFileHandle.create("output.log")?
# val writer = AsyncBufferedWriter.new(raw)
# await writer.write_text("line 1\\n")?
# await writer.write_text("line 2\\n")?
# await writer.flush()?
pass
```

</details>

#### close flushes

#### documents close auto-flush

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val raw = await AsyncFileHandle.create("output.log")?
# val writer = AsyncBufferedWriter.new(raw)
# await writer.write_text("auto-flushed\\n")?
# await writer.close()?  # flushes then closes inner
pass
```

</details>

### Async Buffer Composition

#### wrapping AsyncFileHandle

#### documents file buffering

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val fh = await AsyncFileHandle.read_file("big.csv")?
# val reader = AsyncBufferedReader.new(fh)
# while true:
#     val line = await reader.read_line()?
#     if line.is_empty(): break
#     process(line)
pass
```

</details>

#### wrapping AsyncTcpStream

#### documents network buffering

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val stream = await AsyncTcpStream.connect("127.0.0.1:8080")?
# val reader = AsyncBufferedReader.new(stream)
# val header = await reader.read_line()?
pass
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
