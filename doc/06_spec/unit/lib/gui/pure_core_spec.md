# Pure Core Specification

## Scenarios

### pure GUI command boundary

#### dispatches pointer and key events into command and dirty-region batches

1. gui pointer event

2. gui pointer event

3. gui key event
   - Expected: batch.commands.len() equals `3`
   - Expected: batch.dirty_regions.len() equals `3`
   - Expected: batch.counters.event_count equals `3`
   - Expected: batch.counters.command_count equals `3`
   - Expected: batch.counters.dirty_region_count equals `3`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val events = [
    gui_pointer_event("pointer_move", "button.save", 12, 24),
    gui_pointer_event("pointer_down", "button.save", 12, 24),
    gui_key_event("input.name", "A", "a")
]
val batch = gui_dispatch_events(events, 700)
expect(batch.commands.len()).to_equal(3)
expect(batch.dirty_regions.len()).to_equal(3)
expect(batch.counters.event_count).to_equal(3)
expect(batch.counters.command_count).to_equal(3)
expect(batch.counters.dirty_region_count).to_equal(3)
```

</details>

#### records command kinds without touching pixel output

1. gui pointer event

2. gui pointer event
   - Expected: batch.commands[0].kind equals `hover`
   - Expected: batch.commands[1].kind equals `commit`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val events = [
    gui_pointer_event("pointer_move", "button.save", 12, 24),
    gui_pointer_event("pointer_up", "button.save", 12, 24)
]
val batch = gui_dispatch_events(events, 800)
expect(batch.commands[0].kind).to_equal("hover")
expect(batch.commands[1].kind).to_equal("commit")
```

</details>

#### checks the sub millisecond hot response target from counters

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val events = [gui_pointer_event("pointer_down", "button.save", 12, 24)]
val batch = gui_dispatch_events(events, 999)
expect(gui_batch_meets_hot_response_target(batch, 1000)).to_equal(true)
```

</details>

#### fails the hot response target at one millisecond or above

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val events = [gui_pointer_event("pointer_down", "button.save", 12, 24)]
val batch = gui_dispatch_events(events, 1000)
expect(gui_batch_meets_hot_response_target(batch, 1000)).to_equal(false)
```

</details>

#### creates an empty batch with zero counters

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val batch = gui_empty_batch()
expect(batch.commands.len()).to_equal(0)
expect(batch.dirty_regions.len()).to_equal(0)
expect(batch.counters.elapsed_us).to_equal(0)
```

</details>

#### keeps scalar hot probe count equivalent to representative dispatch

1. gui pointer event

2. gui pointer event

3. gui pointer event

4. gui key event
   - Expected: gui_representative_hot_probe_command_count(7) equals `batch.commands.len().to_i64()`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val events = [
    gui_pointer_event("pointer_move", "button.save", 19, 24),
    gui_pointer_event("pointer_down", "button.save", 12, 24),
    gui_pointer_event("pointer_up", "button.save", 12, 24),
    gui_key_event("input.name", "A", "a")
]
val batch = gui_dispatch_events(events, 0)
expect(gui_representative_hot_probe_command_count(7)).to_equal(batch.commands.len().to_i64())
```

</details>

#### exposes an allocation-light i64-only dynlib hot probe symbol

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gui_dynlib_hot_probe_tick(7)).to_equal(4)
```

</details>

#### keeps representative hot count free of unused iteration conversion

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/gui/pure_core.spl")
expect(source.contains("val _i = iteration.to_i32()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gui/pure_core_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pure GUI command boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

