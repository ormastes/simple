# PipefsService Specification (G7)

> Pipe filesystem capsule backed by ECS. Validates pipe creation, buffer accounting (write and read notifications), close-side bitmask semantics, and pipe count lifecycle.

<!-- sdn-diagram:id=pipefs_service_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pipefs_service_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pipefs_service_spec -> std
pipefs_service_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pipefs_service_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# PipefsService Specification (G7)

Pipe filesystem capsule backed by ECS. Validates pipe creation, buffer accounting (write and read notifications), close-side bitmask semantics, and pipe count lifecycle.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #G7 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/os/services/pipefs_service_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Pipe filesystem capsule backed by ECS. Validates pipe creation,
buffer accounting (write and read notifications), close-side bitmask
semantics, and pipe count lifecycle.

## Scenarios

### PipefsService initial state

#### constructs with zero pipes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = PipefsService.new()
expect(svc.pipe_count()).to_equal(0)
```

</details>

#### PIPE_OPEN constant equals 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(PIPE_OPEN).to_equal(0)
```

</details>

#### PIPE_READER constant equals 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(PIPE_READER).to_equal(1)
```

</details>

#### PIPE_WRITER constant equals 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(PIPE_WRITER).to_equal(2)
```

</details>

#### PIPE_BOTH constant equals 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(PIPE_BOTH).to_equal(3)
```

</details>

### PipefsService pipe_create

#### create returns entity with positive id

1. var svc = PipefsService new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = PipefsService.new()
val pipe = svc.pipe_create(10, 20, 4096)
expect(pipe.id).to_be_greater_than(0)
```

</details>

#### create increments pipe count

1. var svc = PipefsService new
   - Expected: svc.pipe_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = PipefsService.new()
val _pipe = svc.pipe_create(10, 20, 4096)
expect(svc.pipe_count()).to_equal(1)
```

</details>

#### new pipe is not closed on reader side

1. var svc = PipefsService new
   - Expected: svc.pipe_is_closed(pipe, PIPE_READER) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = PipefsService.new()
val pipe = svc.pipe_create(10, 20, 4096)
expect(svc.pipe_is_closed(pipe, PIPE_READER)).to_equal(false)
```

</details>

### PipefsService pipe_write_notify and pipe_read_notify

#### write_notify returns new buffered count

1. var svc = PipefsService new
   - Expected: count equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = PipefsService.new()
val pipe = svc.pipe_create(10, 20, 4096)
val count = svc.pipe_write_notify(pipe, 512)
expect(count).to_equal(512)
```

</details>

#### write_notify accumulates across calls

1. var svc = PipefsService new
   - Expected: c2 equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = PipefsService.new()
val pipe = svc.pipe_create(10, 20, 4096)
val _c1 = svc.pipe_write_notify(pipe, 200)
val c2 = svc.pipe_write_notify(pipe, 100)
expect(c2).to_equal(300)
```

</details>

#### read_notify decrements buffered bytes

1. var svc = PipefsService new
2. svc pipe read notify
   - Expected: after equals `312`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = PipefsService.new()
val pipe = svc.pipe_create(10, 20, 4096)
val _w = svc.pipe_write_notify(pipe, 512)
svc.pipe_read_notify(pipe, 200)
val after = svc.pipe_write_notify(pipe, 0)
expect(after).to_equal(312)
```

</details>

### PipefsService pipe_close and pipe_is_closed

#### close reader returns true (state changed)

1. var svc = PipefsService new
   - Expected: changed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = PipefsService.new()
val pipe = svc.pipe_create(10, 20, 4096)
val changed = svc.pipe_close(pipe, PIPE_READER)
expect(changed).to_equal(true)
```

</details>

#### pipe_is_closed reader after close

1. var svc = PipefsService new
   - Expected: svc.pipe_is_closed(pipe, PIPE_READER) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = PipefsService.new()
val pipe = svc.pipe_create(10, 20, 4096)
val _ok = svc.pipe_close(pipe, PIPE_READER)
expect(svc.pipe_is_closed(pipe, PIPE_READER)).to_equal(true)
```

</details>

#### close same side twice returns false (no new bits)

1. var svc = PipefsService new
   - Expected: second is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = PipefsService.new()
val pipe = svc.pipe_create(10, 20, 4096)
val _first = svc.pipe_close(pipe, PIPE_WRITER)
val second = svc.pipe_close(pipe, PIPE_WRITER)
expect(second).to_equal(false)
```

</details>

#### close both sides sets PIPE_BOTH

1. var svc = PipefsService new
   - Expected: svc.pipe_is_closed(pipe, PIPE_BOTH) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = PipefsService.new()
val pipe = svc.pipe_create(10, 20, 4096)
val _r = svc.pipe_close(pipe, PIPE_READER)
val _w = svc.pipe_close(pipe, PIPE_WRITER)
expect(svc.pipe_is_closed(pipe, PIPE_BOTH)).to_equal(true)
```

</details>

#### writer not closed when only reader closed

1. var svc = PipefsService new
   - Expected: svc.pipe_is_closed(pipe, PIPE_WRITER) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = PipefsService.new()
val pipe = svc.pipe_create(10, 20, 4096)
val _ok = svc.pipe_close(pipe, PIPE_READER)
expect(svc.pipe_is_closed(pipe, PIPE_WRITER)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
