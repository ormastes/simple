# Pure Core Specification

> Tests covering pure GUI command boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Core Specification

## Scenarios

### pure GUI command boundary

#### dispatches pointer and key events into command and dirty-region batches

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- dispatches pointer and key events into command and dirty-region batches
   - Expected: batch.commands.len() equals `3`
   - Expected: batch.dirty_regions.len() equals `3`
   - Expected: batch.counters.event_count equals `3`
   - Expected: batch.counters.command_count equals `3`
   - Expected: batch.counters.dirty_region_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dispatches pointer and key events into command and dirty-region batches")
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

- records command kinds without touching pixel output
   - Expected: batch.commands[0].kind equals `hover`
   - Expected: batch.commands[1].kind equals `commit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records command kinds without touching pixel output")
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

- checks the sub millisecond hot response target from counters
   - Expected: gui_batch_meets_hot_response_target(batch, 1000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("checks the sub millisecond hot response target from counters")
val events = [gui_pointer_event("pointer_down", "button.save", 12, 24)]
val batch = gui_dispatch_events(events, 999)
expect(gui_batch_meets_hot_response_target(batch, 1000)).to_equal(true)
```

</details>

#### fails the hot response target at one millisecond or above

- fails the hot response target at one millisecond or above
   - Expected: gui_batch_meets_hot_response_target(batch, 1000) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails the hot response target at one millisecond or above")
val events = [gui_pointer_event("pointer_down", "button.save", 12, 24)]
val batch = gui_dispatch_events(events, 1000)
expect(gui_batch_meets_hot_response_target(batch, 1000)).to_equal(false)
```

</details>

#### creates an empty batch with zero counters

- creates an empty batch with zero counters
   - Expected: batch.commands.len() equals `0`
   - Expected: batch.dirty_regions.len() equals `0`
   - Expected: batch.counters.elapsed_us equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates an empty batch with zero counters")
val batch = gui_empty_batch()
expect(batch.commands.len()).to_equal(0)
expect(batch.dirty_regions.len()).to_equal(0)
expect(batch.counters.elapsed_us).to_equal(0)
```

</details>

#### keeps scalar hot probe count equivalent to representative dispatch

- keeps scalar hot probe count equivalent to representative dispatch
   - Expected: gui_representative_hot_probe_command_count(7) equals `batch.commands.len().to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps scalar hot probe count equivalent to representative dispatch")
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

#### exposes an allocation-light event-field dynlib hot probe symbol

- exposes an allocation-light event-field dynlib hot probe symbol
   - Expected: gui_representative_hot_probe_event_tick(7, 19, 24, 65) equals `4`
   - Expected: gui_representative_hot_probe_event_tick(7, -1, 24, 65) equals `1`
   - Expected: gui_dynlib_hot_probe_tick(7) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes an allocation-light event-field dynlib hot probe symbol")
expect(gui_representative_hot_probe_event_tick(7, 19, 24, 65)).to_equal(4)
expect(gui_representative_hot_probe_event_tick(7, -1, 24, 65)).to_equal(1)
expect(gui_dynlib_hot_probe_tick(7)).to_equal(4)
```

</details>

#### keeps representative hot count free of unused iteration conversion

- keeps representative hot count free of unused iteration conversion
   - Expected: gui_dynlib_hot_probe_tick(0) equals `gui_dynlib_hot_probe_tick(1000000)`
   - Expected: gui_representative_hot_probe_command_count(3) equals `gui_representative_hot_probe_command_count(11)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps representative hot count free of unused iteration conversion")
# oracle: iteration must not affect probe output — a stray per-iteration conversion would change the tick
expect(gui_dynlib_hot_probe_tick(0)).to_equal(gui_dynlib_hot_probe_tick(1000000))
expect(gui_representative_hot_probe_command_count(3)).to_equal(gui_representative_hot_probe_command_count(11))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gui/pure_core_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure GUI command boundary.
- pure GUI command boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9655b190cc20db983a500e8cbc7cabac128f346a1cfb3893a11562e25c30097b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9655b190cc20db983a500e8cbc7cabac128f346a1cfb3893a11562e25c30097b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9655b190cc20db983a500e8cbc7cabac128f346a1cfb3893a11562e25c30097b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gui/pure_core_spec.spl
mirror: doc/06_spec/01_unit/lib/gui/pure_core_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gui/pure_core_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gui/pure_core_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gui/pure_core_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gui/pure_core_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches pointer and key events into command and dirty-region batches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gui/pure_core_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records command kinds without touching pixel output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gui/pure_core_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks the sub millisecond hot response target from counters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
