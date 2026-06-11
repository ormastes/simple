# ConsoleBuffer Specification

> Tests for `ConsoleBuffer` in `src/lib/gc_async_mut/gpu/browser_engine/script/console_buffer.spl` (REQ-5 / AC-4). All specs FAIL until that module is implemented.

<!-- sdn-diagram:id=console_buffer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=console_buffer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

console_buffer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=console_buffer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ConsoleBuffer Specification

Tests for `ConsoleBuffer` in `src/lib/gc_async_mut/gpu/browser_engine/script/console_buffer.spl` (REQ-5 / AC-4). All specs FAIL until that module is implemented.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #M15-CONSOLE-BUFFER |
| Category | Stdlib |
| Difficulty | 1/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/browser_engine/script/console_buffer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `ConsoleBuffer` in
`src/lib/gc_async_mut/gpu/browser_engine/script/console_buffer.spl` (REQ-5 / AC-4).
All specs FAIL until that module is implemented.

## Key Behaviors

- `ConsoleBuffer.new()` creates an empty buffer.
- `append(level, message, now_micros)` adds a `ConsoleEntry`.
- `entries()` returns all appended entries in insertion order.
- `clear()` empties the buffer.
- Buffer is bounded at 512 entries; on overflow the oldest entry is
  overwritten (ring semantics).

## Scenarios

### ConsoleBuffer

### AC-4: creation

#### AC-4: new buffer starts with zero entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _make_empty_buffer()
val count = _entry_count(buf)
expect(count).to_equal(0)
```

</details>

### AC-4: append and read

#### AC-4: appended log message is stored in entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _buffer_with_one_log()
val msg = _first_entry_message(buf)
expect(msg).to_equal("hello world")
```

</details>

#### AC-4: appended level is stored in entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _buffer_with_one_log()
val lvl = _first_entry_level(buf)
expect(lvl).to_equal("log")
```

</details>

#### AC-4: entries count grows with each append

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _buffer_with_three_levels()
val count = _entry_count(buf)
expect(count).to_equal(3)
```

</details>

#### AC-4: entries are in insertion order — first is log level

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _buffer_with_three_levels()
val entries = buf.entries()
expect(entries[0].level).to_equal("log")
```

</details>

#### AC-4: entries are in insertion order — second is warn level

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _buffer_with_three_levels()
val entries = buf.entries()
expect(entries[1].level).to_equal("warn")
```

</details>

#### AC-4: entries are in insertion order — third is error level

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _buffer_with_three_levels()
val entries = buf.entries()
expect(entries[2].level).to_equal("error")
```

</details>

#### AC-4: timestamp_micros is stored in entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _buffer_with_one_log()
val entries = buf.entries()
expect(entries[0].timestamp_micros).to_equal(1000)
```

</details>

### AC-4: clear

#### AC-4: clear removes all entries

1. var buf =  buffer with three levels
2. buf clear
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = _buffer_with_three_levels()
buf.clear()
val count = _entry_count(buf)
expect(count).to_equal(0)
```

</details>

### AC-4: ring overflow at 512

#### AC-4: buffer accepts exactly 512 entries without loss

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _buffer_filled_to(512)
val count = _entry_count(buf)
expect(count).to_equal(512)
```

</details>

#### AC-4: buffer stays at 512 entries after 513th append

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _buffer_filled_to(513)
val count = _entry_count(buf)
expect(count).to_equal(512)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
